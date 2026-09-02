/* =====================================================================
   안심 미션 · 실시간 포즈 유지형 판정
   - MediaPipe Pose Landmarker(tasks-vision)로 관절 추출
   - config.js 의 pose_model.json(MLP) 로 만세/왼팔/오른팔 분류
   - "포즈 유지형": 카메라를 보고 자세를 잡으면 자동 인식 → HOLD_SEC초 유지 시 성공
   - app.js 가 미션 지점에서 openMission(ms,mi) 호출, 끝나면 resumeMissionWalk() 호출
   - 학습 노트북의 preprocess_features 를 JS로 1:1 포팅 (좌표 정규화·16피처)
   ===================================================================== */
(function(){
  /* ---------- 설정 ---------- */
  const MISS   = (typeof MISSIONS!=='undefined') ? MISSIONS : [];
  const THRESH = (typeof POSE_THRESHOLD!=='undefined') ? POSE_THRESHOLD
               : (typeof MISSION_THRESHOLD!=='undefined') ? MISSION_THRESHOLD : 0.70;
  const HOLD_SEC   = (typeof POSE_HOLD_SEC!=='undefined') ? POSE_HOLD_SEC : 2.0;
  const MODEL_URL  = (typeof POSE_MODEL_URL!=='undefined') ? POSE_MODEL_URL : 'js/pose_model.json';
  const TASK_VER   = '1.0.1';
  const CDN        = `https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@${TASK_VER}`;
  const TASK_MODEL = 'https://storage.googleapis.com/mediapipe-models/pose_landmarker/pose_landmarker_lite/float16/latest/pose_landmarker_lite.task';

  const ORDER=["L_SH","R_SH","L_EL","R_EL","L_WR","R_WR"];

  let mlp=null, landmarker=null, modelState='idle'; // idle|loading|ready|error
  let stream=null, videoEl=null, curMission=null, curIdx=0;
  let rafId=null, holdStart=0, running=false, lastVideoTs=-1;
  let flipCanvas=null, flipCtx=null;   // 학습(cv2.flip)과 동일하게 '이미지를 먼저 뒤집어' MediaPipe에 투입

  /* ---------- modal root ---------- */
  function root(){let r=document.getElementById('mzRoot');
    if(!r){r=document.createElement('div');r.id='mzRoot';document.body.appendChild(r);}return r;}
  function close(){stopLoop();stopCam();const r=document.getElementById('mzRoot');if(r)r.innerHTML='';}
  window.closeMission=close;

  /* ---------- 모델 로드 ---------- */
  async function ensureModel(){
    if(modelState==='ready'||modelState==='loading')return;
    modelState='loading';
    try{
      if(!mlp){
        const res=await fetch(MODEL_URL,{cache:'no-store'});
        if(!res.ok) throw new Error('pose_model.json 로드 실패 ('+res.status+')');
        mlp=await res.json();
      }
      if(!landmarker){
        const vision=await import(`${CDN}/vision_bundle.mjs`);
        const {PoseLandmarker,FilesetResolver}=vision;
        const fileset=await FilesetResolver.forVisionTasks(`${CDN}/wasm`);
        landmarker=await PoseLandmarker.createFromOptions(fileset,{
          baseOptions:{modelAssetPath:TASK_MODEL, delegate:'GPU'},
          runningMode:'VIDEO', numPoses:1
        });
      }
      modelState='ready';
    }catch(e){ console.error('[mission] 모델 로드 실패',e); modelState='error'; }
  }

  /* ---------- 전처리(16 피처) — 노트북 preprocess_features 와 동일 ---------- */
  function preprocess(pts){
    const L=pts.L_SH, R=pts.R_SH;
    const cx=(L[0]+R[0])/2, cy=(L[1]+R[1])/2;
    const w=Math.hypot(L[0]-R[0], L[1]-R[1])+1e-6;
    const nm={}; for(const k of ORDER) nm[k]=[(pts[k][0]-cx)/w,(pts[k][1]-cy)/w];
    const coords=[]; for(const k of ORDER){coords.push(nm[k][0],nm[k][1]);}
    const wrL=nm.L_WR[1]-nm.L_SH[1];
    const wrR=nm.R_WR[1]-nm.R_SH[1];
    const ang=(a,b,c)=>{const A=pts[a],B=pts[b],C=pts[c];
      const bax=A[0]-B[0],bay=A[1]-B[1],bcx=C[0]-B[0],bcy=C[1]-B[1];
      let cs=(bax*bcx+bay*bcy)/((Math.hypot(bax,bay)*Math.hypot(bcx,bcy))+1e-6);
      cs=Math.max(-1,Math.min(1,cs));return Math.acos(cs);};
    const eL=ang("L_SH","L_EL","L_WR")/Math.PI;
    const eR=ang("R_SH","R_EL","R_WR")/Math.PI;
    return coords.concat([wrL,wrR,eL,eR]);
  }
  function forward(f){
    let h=f.slice();
    mlp.layers.forEach((l,i)=>{
      const out=new Array(l.b.length);
      for(let j=0;j<l.b.length;j++){let s=l.b[j];for(let k=0;k<h.length;k++)s+=h[k]*l.W[k][j];out[j]=s;}
      h=(i<mlp.layers.length-1)?out.map(v=>v>0?v:0):out;
    });
    const m=Math.max(...h),e=h.map(v=>Math.exp(v-m)),s=e.reduce((a,b)=>a+b,0);
    return e.map(v=>v/s);
  }
  function classifyLandmarks(lm){
    const idx=mlp.landmark_index;
    const pts={}; for(const k of ORDER) pts[k]=[lm[idx[k]].x, lm[idx[k]].y];
    const vis={}; for(const k of ORDER) vis[k]=(lm[idx[k]].visibility!=null?lm[idx[k]].visibility:1);
    const f=preprocess(pts);
    const rule=mlp.rule||{vis_thresh:0.05,raise_margin:0.15};
    const minVis=Math.min(...ORDER.map(k=>vis[k]));
    const candidate = minVis>=rule.vis_thresh && Math.min(f[12],f[13]) < -rule.raise_margin;
    const p=forward(f);
    const arr=mlp.labels.map((label,i)=>({label,prob:p[i]})).sort((a,b)=>b.prob-a.prob);
    return {preds:arr, candidate};
  }

  /* ---------- entry ---------- */
  window.openMission=function(ms,mi){curMission=ms;curIdx=mi;ensureModel();renderIntro();};
  function done(success){
    const payload=success?{success:true,reward:curMission.reward}:{success:false};
    close();
    if(typeof resumeMissionWalk==='function')resumeMissionWalk(payload);
  }
  const skip=()=>done(false);

  /* ---------- 1. 미션 등장 ---------- */
  function renderIntro(){
    root().innerHTML=`
    <div class="mz-dim"><div class="mz-modal">
      <div class="mz-head">
        <span class="mz-badge">안심 미션 도착!</span>
        <span class="mz-step">미션 ${curIdx+1} / ${MISS.length}</span>
        <h2>${curMission.title}</h2>
        <p>안심경로를 걷다 미션 지점에 도착했어요.<br>카메라 앞에서 아래 포즈를 취하고 <b>${HOLD_SEC}초간 유지</b>하면 AI가 인식해 <b>Safe-Point</b>를 드려요!</p>
      </div>
      <div class="mz-body">
        <div class="mz-guide">
          <div class="mz-pose-card">
            <span class="mz-cap">이렇게 따라하기</span>
            <svg class="mz-mascot" width="168" height="168" viewBox="0 0 200 200">${poseSVG(curMission.pose)}</svg>
            <span class="mz-posename">${curMission.label} 포즈</span>
          </div>
          <div class="mz-info">
            <h3>${curMission.lead}</h3>
            <div class="mz-howto">${curMission.steps.map((s,i)=>`<div class="mz-row"><span class="mz-num">${i+1}</span><span>${s}</span></div>`).join('')}</div>
            <span class="mz-reward">미션 성공 시 +${MISSION_PT} Safe-Point</span>
          </div>
        </div>
        <div class="mz-btns">
          <button class="mz-primary" id="mzStart">포즈 미션 시작 <span>→</span></button>
          <button class="mz-ghost" id="mzSkip">건너뛰기</button>
        </div>
      </div>
    </div></div>`;
    document.getElementById('mzStart').onclick=renderCamera;
    document.getElementById('mzSkip').onclick=skip;
  }

  /* ---------- 2. 카메라 + 실시간 판정 ---------- */
  function renderCamera(){
    root().innerHTML=`
    <div class="mz-dim"><div class="mz-modal mz-wide">
      <div class="mz-head">
        <span class="mz-badge">실시간 포즈 인식</span>
        <span class="mz-step">미션 ${curIdx+1} / ${MISS.length}</span>
        <h2>${curMission.label} 포즈를 취하고 유지하세요</h2>
        <p>온몸(양어깨·양팔)이 화면 안에 들어오게 서고, <b>양손까지 화면에 보이도록</b> 해주세요. 손이 보여야 인식이 정확해요. 포즈를 <b>${HOLD_SEC}초간</b> 유지하면 자동으로 성공 처리돼요.</p>
      </div>
      <div class="mz-body">
        <div class="mz-cam">
          <video id="mzVideo" autoplay playsinline muted></video>
          <div class="mz-rec"><span class="mz-dot"></span>LIVE</div>
          <div class="mz-corners"><i></i><i></i><i></i><i></i></div>
          <div class="mz-guideghost"><svg width="150" height="150" viewBox="0 0 200 200">${poseSVG(curMission.pose)}</svg></div>
          <div class="mz-hold" id="mzHold"><div class="mz-hold-bar"><i id="mzHoldFill"></i></div><div class="mz-hold-txt" id="mzHoldTxt">포즈를 인식하는 중…</div></div>
        </div>
        <div class="mz-side">
          <h3>실시간 신뢰도</h3>
          <div id="mzBars"></div>
          ${modelBadge()}
          <p class="mz-note">${Math.round(THRESH*100)}% 이상으로 ${HOLD_SEC}초 유지하면 성공. 영상은 저장되지 않고 기기 안에서만 분석됩니다.</p>
        </div>
        <div class="mz-cam-actions" style="grid-column:1 / -1">
          <button class="mz-ghost" id="mzBack">← 뒤로</button>
          <button class="mz-ghost" id="mzSkip3">건너뛰기</button>
        </div>
        <div id="mzCamMsg" class="mz-cammsg" style="grid-column:1 / -1"></div>
      </div>
    </div></div>`;
    videoEl=document.getElementById('mzVideo');
    document.getElementById('mzBack').onclick=()=>{stopLoop();stopCam();renderIntro();};
    document.getElementById('mzSkip3').onclick=()=>{stopLoop();skip();};
    const seed=mlp?mlp.labels.map(l=>({label:l,prob:0})):MISS.map(m=>({label:m.label,prob:0}));
    paintBars(seed,true);
    startCam();
  }

  async function startCam(){
    const msg=document.getElementById('mzCamMsg');
    await ensureModel();
    if(modelState==='error'){
      if(msg)msg.innerHTML=`<div class="mz-err">AI 모델을 불러오지 못했어요. 인터넷 연결을 확인해주세요.<br>
        <small>pose_model.json 이 js/ 폴더에 있는지, MediaPipe(CDN) 접속이 가능한지 확인하세요.</small></div>
        <button class="mz-ghost" id="mzSkipErr" style="margin-top:12px">이 미션 건너뛰기 →</button>`;
      const b=document.getElementById('mzSkipErr');if(b)b.onclick=skip; return;
    }
    try{
      stream=await navigator.mediaDevices.getUserMedia({video:{facingMode:'user',width:{ideal:720},height:{ideal:540}},audio:false});
      if(videoEl){videoEl.srcObject=stream; await videoEl.play().catch(()=>{});}
      startLoop();
    }catch(e){
      if(msg)msg.innerHTML=`<div class="mz-err">카메라를 열 수 없어요. 브라우저의 카메라 권한을 허용했는지 확인해주세요.<br>
        <small>HTML 파일을 직접 열면 카메라가 막힐 수 있어요 — 폴더에서 <b>python -m http.server</b> 로 실행한 뒤 <b>localhost</b> 로 접속하세요.</small></div>
        <button class="mz-ghost" id="mzSkipCam" style="margin-top:12px">이 미션 건너뛰기 →</button>`;
      const b=document.getElementById('mzSkipCam');if(b)b.onclick=skip;
    }
  }

  /* ---------- 실시간 루프 ---------- */
  function startLoop(){ running=true; holdStart=0; lastVideoTs=-1; rafId=requestAnimationFrame(tick); }
  function stopLoop(){ running=false; if(rafId)cancelAnimationFrame(rafId); rafId=null; }

  function tick(){
    if(!running||!videoEl||!landmarker){ if(running)rafId=requestAnimationFrame(tick); return; }
    if(videoEl.readyState<2 || videoEl.currentTime===lastVideoTs){ rafId=requestAnimationFrame(tick); return; }
    lastVideoTs=videoEl.currentTime;
    const vw=videoEl.videoWidth, vh=videoEl.videoHeight;
    if(!vw||!vh){ rafId=requestAnimationFrame(tick); return; }

    // 학습(capture)과 100% 동일하게: 프레임을 좌우반전한 뒤 MediaPipe 에 투입
    if(!flipCanvas){ flipCanvas=document.createElement('canvas'); flipCtx=flipCanvas.getContext('2d'); }
    if(flipCanvas.width!==vw){ flipCanvas.width=vw; flipCanvas.height=vh; }
    flipCtx.setTransform(-1,0,0,1,vw,0);       // 수평 뒤집기
    flipCtx.drawImage(videoEl,0,0,vw,vh);
    flipCtx.setTransform(1,0,0,1,0,0);

    let res;
    try{ res=landmarker.detectForVideo(flipCanvas, performance.now()); }
    catch(e){ rafId=requestAnimationFrame(tick); return; }

    const has = res && res.landmarks && res.landmarks.length>0;
    if(!has){
      updateHold(false,0); paintBars(mlp.labels.map(l=>({label:l,prob:0})),true);
      setHoldTxt('사람이 안 보여요 · 뒤로 물러서 주세요'); holdStart=0;
      rafId=requestAnimationFrame(tick); return;
    }
    // 뒤집은 이미지로 검출했으므로 좌표 추가 변환 없이 그대로 사용 (학습과 동일 좌표계)
    const lm=res.landmarks[0];

    const {preds,candidate}=classifyLandmarks(lm);
    paintBars(preds,false);

    const top=preds[0];
    const hit = candidate && top.label===curMission.label && top.prob>=THRESH;

    if(hit){
      if(!holdStart) holdStart=performance.now();
      const heldSec=(performance.now()-holdStart)/1000;
      updateHold(true, Math.min(1,heldSec/HOLD_SEC));
      setHoldTxt(`유지 중… ${Math.max(0,(HOLD_SEC-heldSec)).toFixed(1)}초`);
      if(heldSec>=HOLD_SEC){ stopLoop(); renderVerdict(true, top); return; }
    }else{
      holdStart=0; updateHold(false,0);
      setHoldTxt(candidate?`${curMission.label} 포즈를 취해주세요`:'팔을 확실히 올려주세요');
    }
    rafId=requestAnimationFrame(tick);
  }
  function updateHold(active,ratio){
    const fill=document.getElementById('mzHoldFill');const wrap=document.getElementById('mzHold');
    if(fill)fill.style.width=Math.round(ratio*100)+'%';
    if(wrap)wrap.classList.toggle('on',active);
  }
  function setHoldTxt(t){const el=document.getElementById('mzHoldTxt');if(el)el.textContent=t;}
  function stopCam(){if(stream){stream.getTracks().forEach(t=>t.stop());stream=null;}}

  function paintBars(preds,zero){
    const box=document.getElementById('mzBars');if(!box)return;
    const emojiOf=l=>{const m=MISS.find(x=>x.label===l);return m?m.emoji:'▫️';};
    box.innerHTML=preds.slice(0,3).map((p,i)=>{
      const win=i===0&&!zero&&p.label===curMission.label;const pct=Math.round(p.prob*100);
      return `<div class="mz-cand ${win?'win':''}"><div class="mz-cand-top">${emojiOf(p.label)} ${p.label}<span class="mz-pct">${zero?'--':pct+'%'}</span></div>
        <div class="mz-cbar"><i style="width:${zero?0:pct}%"></i></div></div>`;
    }).join('');
  }

  /* ---------- 4. 판정 ---------- */
  function renderVerdict(success,top){
    stopLoop();stopCam();
    const pct=Math.round((top&&top.prob||0)*100);
    if(success){
      root().innerHTML=`
      <div class="mz-dim"><div class="mz-modal mz-narrow">
        <div class="mz-body" style="padding:34px 30px 30px">
          <div class="mz-success">
            <span class="mz-result-badge">판정 완료 · 신뢰도 ${pct}%</span>
            <div class="mz-ring">${ringSVG(pct)}<div class="mz-ring-c"><b>${pct}</b><span>MATCH %</span></div></div>
            <div class="mz-succ-title">미션 성공! ${curMission.label} 포즈 인식 완료</div>
            <div class="mz-succ-sub">정확하게 포즈를 유지했어요. 가장 큰 Safe-Point를 획득했어요!</div>
            <div class="mz-succ-stats">
              <div class="mz-succ-stat"><div class="v">+${MISSION_PT} P</div><div class="k">획득 Safe-Point</div></div>
            </div>
            <div class="mz-btns"><button class="mz-primary" id="mzGo">안심경로 계속 걷기 <span>→</span></button></div>
          </div>
        </div>
      </div></div>`;
      document.getElementById('mzGo').onclick=()=>done(true);
    }else{
      root().innerHTML=`
      <div class="mz-dim"><div class="mz-modal mz-narrow">
        <div class="mz-body" style="padding:30px">
          <div class="mz-success">
            <span class="mz-result-badge fail">다시 한 번!</span>
            <div class="mz-succ-title">포즈를 조금 더 명확하게</div>
            <div class="mz-succ-sub">온몸이 화면에 들어오게 서서 <b>${curMission.label}</b> 포즈를 ${HOLD_SEC}초간 유지해보세요.</div>
            <div class="mz-btns"><button class="mz-primary" id="mzRetry">다시 도전</button><button class="mz-ghost" id="mzSkip2">건너뛰기</button></div>
          </div>
        </div>
      </div></div>`;
      document.getElementById('mzRetry').onclick=renderCamera;
      document.getElementById('mzSkip2').onclick=skip;
    }
  }

  /* ---------- helpers ---------- */
  function modelBadge(){
    let t,cls;
    if(modelState==='ready'){t='🟢 AI 모델 연결됨 · MediaPipe + MLP';cls='ok';}
    else if(modelState==='loading'){t='⏳ AI 모델 불러오는 중…';cls='load';}
    else if(modelState==='error'){t='⚠️ 모델 로드 실패 · 연결 확인 필요';cls='demo';}
    else{t='⏳ 준비 중…';cls='load';}
    return `<div class="mz-model ${cls}">${t}</div>`;
  }
  function ringSVG(pct){const R=72,C=2*Math.PI*R,off=C-C*Math.max(0,Math.min(100,pct))/100;
    return `<svg width="170" height="170" viewBox="0 0 170 170">
      <circle cx="85" cy="85" r="${R}" fill="none" stroke="#e6efe9" stroke-width="13"/>
      <circle cx="85" cy="85" r="${R}" fill="none" stroke="url(#mzg)" stroke-width="13" stroke-linecap="round"
        stroke-dasharray="${C.toFixed(0)}" stroke-dashoffset="${off.toFixed(0)}" transform="rotate(-90 85 85)"/>
      <defs><linearGradient id="mzg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#34cf83"/><stop offset="1" stop-color="#1ba866"/></linearGradient></defs>
    </svg>`;}

  /* ---------- 마스코트 포즈 일러스트 (만세/왼팔/오른팔) ---------- */
  function mascotFace(){return `
    <circle cx="100" cy="96" r="46" fill="#ffe0bd"/>
    <path d="M54 96 a46 46 0 0 0 92 0" fill="#ffe0bd"/>
    <path d="M54 92 Q54 44 100 44 Q146 44 146 92 Q120 70 100 70 Q80 70 54 92 Z" fill="#6b5748"/>
    <circle cx="83" cy="98" r="5.5" fill="#3a2e28"/><circle cx="117" cy="98" r="5.5" fill="#3a2e28"/>
    <circle cx="84.5" cy="96" r="1.7" fill="#fff"/><circle cx="118.5" cy="96" r="1.7" fill="#fff"/>
    <circle cx="74" cy="110" r="6" fill="#ffb3a7" opacity=".55"/><circle cx="126" cy="110" r="6" fill="#ffb3a7" opacity=".55"/>
    <path d="M90 114 Q100 124 110 114" fill="none" stroke="#c96a4d" stroke-width="3.2" stroke-linecap="round"/>`;}
  function arm(side, up){
    const sx = side==='L' ? 72 : 128, sy=140;
    if(up){
      const ex = side==='L' ? 60 : 140, ey=104, hx=side==='L'?54:146, hy=64;
      return `<g stroke="#ffe0bd" stroke-width="11" stroke-linecap="round" fill="none">
        <line x1="${sx}" y1="${sy}" x2="${ex}" y2="${ey}"/><line x1="${ex}" y1="${ey}" x2="${hx}" y2="${hy}"/></g>
        <circle cx="${hx}" cy="${hy-4}" r="8" fill="#ffe0bd" stroke="#e9b98c" stroke-width="1.5"/>`;
    }else{
      const ex = side==='L' ? 66 : 134, ey=168, hx=side==='L'?70:130, hy=196;
      return `<g stroke="#ffe0bd" stroke-width="11" stroke-linecap="round" fill="none">
        <line x1="${sx}" y1="${sy}" x2="${ex}" y2="${ey}"/><line x1="${ex}" y1="${ey}" x2="${hx}" y2="${hy}"/></g>
        <circle cx="${hx}" cy="${hy}" r="8" fill="#ffe0bd" stroke="#e9b98c" stroke-width="1.5"/>`;
    }
  }
  function poseSVG(pose){
    const body=`<rect x="78" y="132" width="44" height="46" rx="16" fill="#7cc6a0"/>`;
    let arms='';
    if(pose==='both'){ arms=arm('L',true)+arm('R',true); }
    else if(pose==='left'){ arms=arm('L',true)+arm('R',false); }
    else if(pose==='right'){ arms=arm('L',false)+arm('R',true); }
    else { arms=arm('L',false)+arm('R',false); }
    return body+arms+mascotFace();
  }

  /* ---------- 빠른 미리보기: #mission-demo / #mission-demo2 ---------- */
  function hashPreview(){
    const h=location.hash;
    if(h.indexOf('mission-demo')<0)return;
    const idx=h.indexOf('mission-demo2')>=0?1:0;
    if(MISS[idx])openMission(MISS[idx],idx);
  }
  window.addEventListener('hashchange',hashPreview);
  if(location.hash.indexOf('mission-demo')>=0)setTimeout(hashPreview,250);
})();
