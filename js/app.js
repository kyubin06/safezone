/* ===== geo helpers (local meters) ===== */
const RAD=Math.PI/180, LAT0=DATA.start.lat, LNG0=DATA.start.lng, MPD=111000;
function mx(lng){return (lng-LNG0)*Math.cos(LAT0*RAD)*MPD}
function my(lat){return (lat-LAT0)*MPD}
function segDist(a,b){return Math.hypot(mx(a.lng)-mx(b.lng),my(a.lat)-my(b.lat))}
function polyLen(poly){let s=0;for(let i=0;i<poly.length-1;i++)s+=segDist(poly[i],poly[i+1]);return s}
function projectToRoute(f,poly){
  const px=mx(f.lng),py=my(f.lat);let best=1e9,bestS=0,acc=0;
  for(let i=0;i<poly.length-1;i++){
    const ax=mx(poly[i].lng),ay=my(poly[i].lat),bx=mx(poly[i+1].lng),by=my(poly[i+1].lat);
    const dx=bx-ax,dy=by-ay,L2=dx*dx+dy*dy;
    let t=L2?Math.max(0,Math.min(1,((px-ax)*dx+(py-ay)*dy)/L2)):0;
    const cx=ax+t*dx,cy=ay+t*dy,d=Math.hypot(px-cx,py-cy);
    if(d<best){best=d;bestS=acc+Math.hypot(cx-ax,cy-ay);}
    acc+=Math.hypot(dx,dy);
  }
  return {d:best,s:bestS};
}
function posAtS(poly,s){let acc=0;for(let i=0;i<poly.length-1;i++){const seg=segDist(poly[i],poly[i+1]);
  if(acc+seg>=s){const f=seg?(s-acc)/seg:0;return {lat:poly[i].lat+(poly[i+1].lat-poly[i].lat)*f,lng:poly[i].lng+(poly[i+1].lng-poly[i].lng)*f};}acc+=seg;}
  return poly[poly.length-1];}

/* ===== scoring ===== */
const BUF=85, GUARD_BUF=40;
function facsNearRoute(poly){
  const r={cctv:[],bell:[],guard:[]};
  DATA.cctv.forEach(f=>{const pr=projectToRoute(f,poly);if(pr.d<=BUF)r.cctv.push({...f,s:pr.s})});
  DATA.bell.forEach(f=>{const pr=projectToRoute(f,poly);if(pr.d<=BUF*1.3)r.bell.push({...f,s:pr.s})});
  // 보안등: 실좌표 데이터(경기 고양시). 도로변에 있으므로 좁은 버퍼로 경로가 실제로 지나는 것만 집계.
  (DATA.guard||[]).forEach(f=>{const pr=projectToRoute(f,poly);if(pr.d<=GUARD_BUF)r.guard.push({...f,s:pr.s})});
  return r;
}
function zoneCountForRoute(len){return Math.max(1,Math.min(4,Math.round(len/650)));}
function sat(x,k){return 1-Math.exp(-x/k)}
function getWeights(){const s=state.weights.c+state.weights.g+state.weights.b||1;
  return {c:state.weights.c/s,g:state.weights.g/s,b:state.weights.b/s}}
function routeRawMetrics(poly,len){
  const per=len/100, f=facsNearRoute(poly), guardN=f.guard.length, zoneN=zoneCountForRoute(len);
  const dC=f.cctv.length/per, dG=f.guard.length/per, dB=f.bell.length*2/per;
  return {len,f,guardN,zoneN,dC,dG,dB};
}
function normList(arr){
  const min=Math.min(...arr),max=Math.max(...arr),range=max-min;
  return arr.map(v=>range<1e-6?1:(v-min)/range);
}
function scoreRoutesFromMetrics(metricsList){
  // 후보 경로들 "사이"에서 상대적으로 비교해야 가중치가 실제로 순위에 반영됨.
  // (절대 포화값만 쓰면 CCTV·비상벨이 촘촘한 지역에서는 모든 후보가 거의 1로 수렴해
  //  가중치를 바꿔도 경로 선택이 그대로인 문제가 생김)
  const minLen=Math.min(...metricsList.map(m=>m.len));
  const nC=normList(metricsList.map(m=>m.dC));   // CCTV 밀도 (실좌표 기반)
  const nB=normList(metricsList.map(m=>m.dB));   // 비상벨 밀도 (실좌표 기반)
  // 보안등: 실좌표 밀도를 우선 사용한다.
  // 단, 이 데이터셋은 킨텍스·신도시 구간 커버리지가 낮아 후보 경로 모두 보안등이 거의 0이면
  // 밀도로는 우열을 못 가린다. 그럴 때만 "곧장(짧게) 가기"로 폴백해 슬라이더가 죽지 않게 한다.
  const gDens=metricsList.map(m=>m.dG), gMax=Math.max(...gDens);
  const nG = gMax<0.05
    ? normList(metricsList.map(m=>minLen/m.len))  // 실측 보안등 신호 없음 → 직선 선호
    : normList(gDens);                            // 실측 보안등 밀도
  const W=getWeights();
  const covers=metricsList.map((m,i)=>W.c*nC[i]+W.g*nG[i]+W.b*nB[i]);
  return metricsList.map((m,i)=>{
    const cover=covers[i];
    // Safe-Score 는 57~97 범위로 표시(사용자 요청)
    let score=Math.round(57+34*cover+Math.min(6,m.zoneN*2));
    score=Math.max(57,Math.min(97,score));
    // rank: 표시점수는 클램프로 동점이 생길 수 있으므로, 추천 순위는 가중치가 그대로 반영된 cover로 정한다.
    return {score,rank:cover,len:m.len,f:m.f,counts:{cctv:m.f.cctv.length,guard:m.guardN,bell:m.f.bell.length,zone:m.zoneN}};
  });
}

/* ===== state ===== */
let state={dest:null,weights:{c:5,g:5,b:5},routes:[],chosen:null,walk:null,userName:''};
const SUGGEST=[["주엽공원","일산 주엽공원"],["문촌마을","일산 문촌마을"],["대진고등학교","일산 대진고등학교"],["일산서구청","일산서구청"],["정발산역","정발산역"]];

/* ===== Leaflet map (single instance, relocated between screens) ===== */
let map=null, mapEl=null, layerFac=null, layerRoute=null, layerChar=null, charMarker=null;
function initMap(){
  mapEl=document.createElement('div');mapEl.id='leafmap';
  map=L.map(mapEl,{zoomControl:true,attributionControl:true,preferCanvas:true}).setView([DATA.start.lat,DATA.start.lng],14);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png',{
    maxZoom:19,attribution:'© OpenStreetMap'}).addTo(map);
  layerFac=L.layerGroup().addTo(map);
  layerRoute=L.layerGroup().addTo(map);
  layerChar=L.layerGroup().addTo(map);
  drawAmbientFacilities();
}
function mountMap(slotId){const slot=document.getElementById(slotId);
  if(mapEl.parentElement!==slot)slot.appendChild(mapEl);
  setTimeout(()=>map.invalidateSize(),60);}
function drawAmbientFacilities(){
  const cv=L.canvas({padding:.5});
  // 보안등(실좌표)은 1만 개가 넘고 시 전체에 퍼져 있으므로, 킨텍스 인근(약 4.5km)만 아주 옅게 깔아준다.
  (DATA.guard||[]).forEach(f=>{if(Math.abs(f.lat-DATA.start.lat)>0.04||Math.abs(f.lng-DATA.start.lng)>0.05)return;
    L.circleMarker([f.lat,f.lng],{renderer:cv,radius:1.5,color:'#f0980f',weight:0,fillOpacity:.3}).addTo(layerFac);});
  DATA.cctv.forEach(f=>L.circleMarker([f.lat,f.lng],{renderer:cv,radius:2.6,color:'#2f6fed',weight:0,fillOpacity:.5}).addTo(layerFac));
  DATA.bell.forEach(f=>L.circleMarker([f.lat,f.lng],{renderer:cv,radius:3.4,color:'#ef4657',weight:0,fillOpacity:.75}).addTo(layerFac));
}
function startPin(){return L.divIcon({className:'',iconSize:[0,0],iconAnchor:[0,0],html:'<div class="mpin start"><b>출발</b><i></i></div>'});}
function destPin(){return L.divIcon({className:'',iconSize:[0,0],iconAnchor:[0,0],html:'<div class="mpin dest"><b>도착</b><i></i></div>'});}

/* ===== setup preview map (separate small instance) ===== */
let setupMap=null, setupDestMarker=null, setupLine=null;
function initSetupMap(){
  if(setupMap)return;
  const slot=document.getElementById('setupMap');if(!slot)return;
  setupMap=L.map(slot,{zoomControl:true,attributionControl:true,preferCanvas:true,scrollWheelZoom:false}).setView([DATA.start.lat,DATA.start.lng],14);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png',{
    maxZoom:19,attribution:'© OpenStreetMap'}).addTo(setupMap);
  L.marker([DATA.start.lat,DATA.start.lng],{icon:startPin(),zIndexOffset:1000}).addTo(setupMap);
}
function mountSetupMap(){
  initSetupMap();
  setTimeout(()=>{if(setupMap)setupMap.invalidateSize();},80);
  if(state.dest)showDestOnSetupMap(state.dest);
}
function showDestOnSetupMap(r){
  if(!setupMap)initSetupMap();
  if(!setupMap)return;
  if(setupDestMarker){setupMap.removeLayer(setupDestMarker);setupDestMarker=null;}
  if(setupLine){setupMap.removeLayer(setupLine);setupLine=null;}
  setupDestMarker=L.marker([r.lat,r.lng],{icon:destPin(),zIndexOffset:1000}).addTo(setupMap);
  setupLine=L.polyline([[DATA.start.lat,DATA.start.lng],[r.lat,r.lng]],{color:'#159a5b',weight:3,opacity:.55,dashArray:'4 8'}).addTo(setupMap);
  const b=L.latLngBounds([[DATA.start.lat,DATA.start.lng],[r.lat,r.lng]]);
  setupMap.fitBounds(b,{padding:[42,42],maxZoom:15});
  const hint=document.getElementById('setupMapHint');
  if(hint)hint.textContent=`${r.name} · 킨텍스에서 여기까지 경로를 안내합니다.`;
}

/* ===== navigation ===== */
function show(id){document.querySelectorAll('.screen').forEach(s=>s.classList.add('hidden'));
  document.getElementById('screen-'+id).classList.remove('hidden');window.scrollTo(0,0);setStep(id);}
function setStep(id){const order=['setup','analyze','walk','result'],idx=order.indexOf(id);
  document.querySelectorAll('#steps .st').forEach(el=>{const i=order.indexOf(el.dataset.s);el.classList.remove('on','done');
    if(i===idx)el.classList.add('on');else if(idx>=0&&i<idx)el.classList.add('done');});}
/* 설정 페이지 재진입 시 항상 디폴트 상태로 초기화 (목적지·지도·가중치) */
function resetSetupInputs(){
  state.dest=null;
  state.weights={c:5,g:5,b:5};
  const rcEl=document.getElementById('rc'),rgEl=document.getElementById('rg'),rbEl=document.getElementById('rb');
  if(rcEl)rcEl.value=5;if(rgEl)rgEl.value=5;if(rbEl)rbEl.value=5;
  onWeight();
  const di=document.getElementById('destInput');if(di)di.value='';
  const gs=document.getElementById('geoStatus');if(gs){gs.className='geo-status';gs.textContent='';}
  const cb=document.getElementById('calcBtn');if(cb)cb.disabled=true;
  hideAC();
  if(setupMap){
    if(setupDestMarker){setupMap.removeLayer(setupDestMarker);setupDestMarker=null;}
    if(setupLine){setupMap.removeLayer(setupLine);setupLine=null;}
    setupMap.setView([DATA.start.lat,DATA.start.lng],14);
  }
  const hint=document.getElementById('setupMapHint');
  if(hint)hint.textContent='목적지를 입력하면 지도에 위치가 표시됩니다.';
}
function onNameInput(){
  const el=document.getElementById('userName');
  const btn=document.getElementById('startBtn');
  if(btn)btn.disabled=!(el&&el.value.trim());
}
function startExp(){
  const el=document.getElementById('userName');
  const nm=el?el.value.trim():'';
  if(!nm){if(el)el.focus();return;}
  state.userName=nm;
  resetSetupInputs();
  updateSetupGreeting();
  show('setup');mountSetupMap();
}
function updateSetupGreeting(){
  const t=document.getElementById('setupTitle');if(!t)return;
  const nm=state.userName;
  t.textContent=nm?`${nm}님, 목적지와 안전요소 가중치를 설정하세요`:'목적지와 안전요소 가중치를 설정하세요';
}
function backToSetup(){resetSetupInputs();show('setup');mountSetupMap();}
function resetToSetup(){stopWalk();resetSetupInputs();show('setup');mountSetupMap();}
function resetToIntro(){stopWalk();document.querySelectorAll('.screen').forEach(s=>s.classList.add('hidden'));
  document.getElementById('screen-intro').classList.remove('hidden');
  document.querySelectorAll('#steps .st').forEach(el=>el.classList.remove('on','done'));window.scrollTo(0,0);}

/* ===== setup ===== */
function renderChips(){document.getElementById('chips').innerHTML=SUGGEST.map(s=>`<button class="chip-s" onclick="useChip('${s[1]}')">${s[0]}</button>`).join('');}
function useChip(q){document.getElementById('destInput').value=q;doGeocode();}
function onWeight(){
  const c=+rc.value,g=+rg.value,b=+rb.value;state.weights={c,g,b};
  ['rc','rg','rb'].forEach(id=>{const el=document.getElementById(id);el.style.setProperty('--p',(el.value/10*100)+'%')});
  const sum=c+g+b||1,pc=Math.round(c/sum*100),pg=Math.round(g/sum*100),pb=100-pc-pg;
  wtc.textContent=pc;wtg.textContent=pg;wtb.textContent=pb;
  const bars=wshare.children;bars[0].style.width=pc+'%';bars[1].style.width=pg+'%';bars[2].style.width=pb+'%';
}
function esc(s){return String(s).replace(/[&<>"']/g,m=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[m]));}

/* ---- 연관 검색어(자동완성) ---- */
let _acTimer=null,_acSeq=0;
function onDestInput(){
  const q=document.getElementById('destInput').value.trim();
  clearTimeout(_acTimer);
  state.dest=null;document.getElementById('calcBtn').disabled=true;
  document.getElementById('geoStatus').textContent='';state._acIdx=-1;
  if(q.length<2){hideAC();return;}
  const seq=++_acSeq;
  _acTimer=setTimeout(async()=>{const list=await geoSuggest(q);if(seq!==_acSeq)return;renderAC(list);},240);
}
function onDestKey(e){
  const box=document.getElementById('acList');
  const shown=box.classList.contains('show')&&state._sugg&&state._sugg.length;
  if(e.key==='ArrowDown'&&shown){e.preventDefault();state._acIdx=Math.min(state._sugg.length-1,(state._acIdx<0?-1:state._acIdx)+1);paintAC();}
  else if(e.key==='ArrowUp'&&shown){e.preventDefault();state._acIdx=Math.max(0,state._acIdx-1);paintAC();}
  else if(e.key==='Enter'){e.preventDefault();if(shown&&state._acIdx>=0)pickSuggest(state._acIdx);else{hideAC();doGeocode();}}
  else if(e.key==='Escape'){hideAC();}
}
async function geoSuggest(q){
  q=q.trim();if(q.length<2)return [];
  // 카카오 (키 설정 시)
  try{
    if(typeof KAKAO_REST_KEY!=='undefined'&&KAKAO_REST_KEY){
      const url=`https://dapi.kakao.com/v2/local/search/keyword.json?query=${encodeURIComponent(q)}&size=8&x=${DATA.start.lng}&y=${DATA.start.lat}`;
      const res=await fetch(url,{headers:{Authorization:'KakaoAK '+KAKAO_REST_KEY}});
      if(res.ok){const js=await res.json();
        if(js.documents&&js.documents.length)
          return js.documents.map(d=>({lat:+d.y,lng:+d.x,name:d.place_name,addr:d.road_address_name||d.address_name||'',cat:(d.category_name||'').split('>').pop().trim()}));
      }
    }
  }catch(e){}
  // Photon 폴백
  try{
    const url=`https://photon.komoot.io/api/?q=${encodeURIComponent(q)}&lat=${DATA.start.lat}&lon=${DATA.start.lng}&limit=6&lang=default`;
    const res=await fetch(url);const js=await res.json();
    if(js&&js.features)return js.features.map(f=>{const p=f.properties,c=f.geometry.coordinates;
      const name=p.name||[p.street,p.housenumber].filter(Boolean).join(' ')||p.city||q;
      const addr=[p.state,p.city,p.district,p.street].filter(Boolean).join(' ');
      return {lat:c[1],lng:c[0],name,addr,cat:''};});
  }catch(e){}
  return [];
}
function renderAC(list){
  state._sugg=list;state._acIdx=-1;
  const box=document.getElementById('acList');
  if(!list||!list.length){box.classList.remove('show');box.innerHTML='';return;}
  paintAC();box.classList.add('show');
}
function paintAC(){
  const box=document.getElementById('acList'),list=state._sugg||[];
  box.innerHTML=list.map((it,i)=>{
    const km=(segDist({lat:DATA.start.lat,lng:DATA.start.lng},{lat:it.lat,lng:it.lng})/1000).toFixed(1);
    const sub=[it.cat,it.addr].filter(Boolean).join(' · ');
    return `<div class="ac-item ${i===state._acIdx?'act':''}" onmousedown="pickSuggest(${i})">
      <span class="ac-ic">📍</span><div class="ac-tx"><b>${esc(it.name)}</b><small>${sub?esc(sub)+' · ':''}<em>${km}km</em></small></div></div>`;
  }).join('');
}
function pickSuggest(i){const it=(state._sugg||[])[i];if(!it)return;
  document.getElementById('destInput').value=it.name;hideAC();confirmDest(it);}
function hideAC(){const b=document.getElementById('acList');b.classList.remove('show');state._acIdx=-1;}
function confirmDest(r){
  const dkm=segDist({lat:DATA.start.lat,lng:DATA.start.lng},{lat:r.lat,lng:r.lng})/1000;
  state.dest={lat:r.lat,lng:r.lng,name:r.name};
  const st=document.getElementById('geoStatus');st.className='geo-status ok';
  st.innerHTML=`✓ <b>${esc(r.name)}</b> 확인됨 · 킨텍스에서 직선거리 약 ${dkm.toFixed(1)}km`
    +(dkm>4?'<br><span style="color:var(--guard)">※ 킨텍스에서 다소 멀어 주변 안전데이터가 적을 수 있어요.</span>':'');
  document.getElementById('calcBtn').disabled=false;
  showDestOnSetupMap(state.dest);
}
async function doGeocode(){
  const q=document.getElementById('destInput').value.trim();
  const st=document.getElementById('geoStatus');
  if(!q){st.className='geo-status err';st.textContent='목적지를 입력해주세요.';return;}
  st.className='geo-status load';st.textContent='🔎 위치를 찾는 중…';
  document.getElementById('calcBtn').disabled=true;
  try{
    const r=await geoQuery(q);
    if(!r){st.className='geo-status err';st.textContent='해당 위치를 찾지 못했어요. 다른 이름/주소로 시도해보세요.';return;}
    confirmDest(r);
  }catch(e){st.className='geo-status err';st.textContent='⚠ 검색 중 오류가 발생했어요. 인터넷 연결을 확인해주세요.';}
}
async function geoQuery(q){
  // 0순위: 카카오맵 Local 검색 (js/config.js 에 REST 키가 설정된 경우) — 한국어 검색 최상
  try{
    if(typeof KAKAO_REST_KEY!=='undefined' && KAKAO_REST_KEY){
      const url=`https://dapi.kakao.com/v2/local/search/keyword.json?query=${encodeURIComponent(q)}&size=5&x=${DATA.start.lng}&y=${DATA.start.lat}`;
      const res=await fetch(url,{headers:{Authorization:'KakaoAK '+KAKAO_REST_KEY}});
      if(res.ok){
        const js=await res.json();
        if(js.documents&&js.documents.length){
          const d=js.documents[0];               // 관련도순 최상위
          return {lat:+d.y,lng:+d.x,name:d.place_name};
        }
      }
    }
  }catch(e){}
  // 1순위: Photon (OSM 기반, 키 불필요) — 킨텍스 위치 바이어스로 한국어 장소·주소 검색
  try{
    const url=`https://photon.komoot.io/api/?q=${encodeURIComponent(q)}&lat=${DATA.start.lat}&lon=${DATA.start.lng}&limit=1&lang=default`;
    const res=await fetch(url);const js=await res.json();
    if(js&&js.features&&js.features.length){
      const f=js.features[0],c=f.geometry.coordinates,p=f.properties;
      const name=p.name||[p.street,p.housenumber].filter(Boolean).join(' ')||p.city||p.district||q;
      return {lat:c[1],lng:c[0],name};
    }
  }catch(e){}
  // 2순위: Nominatim (bounded 없이 viewbox 바이어스만)
  try{
    const vb='126.55,37.80,126.95,37.55';
    const url=`https://nominatim.openstreetmap.org/search?format=json&limit=1&countrycodes=kr&accept-language=ko&viewbox=${vb}&q=${encodeURIComponent(q)}`;
    const res=await fetch(url,{headers:{'Accept':'application/json'}});const js=await res.json();
    if(js&&js.length)return {lat:+js[0].lat,lng:+js[0].lon,name:js[0].display_name.split(',')[0]};
  }catch(e){}
  return null;
}

/* ===== analyze: fetch OSRM routes ===== */
function osrmUrl(coords){ // coords: [{lat,lng},...] · FOSSGIS 공개 OSRM 보행자(routed-foot) 서버
  const c=coords.map(p=>`${p.lng},${p.lat}`).join(';');
  return `https://routing.openstreetmap.de/routed-foot/route/v1/foot/${c}?alternatives=3&overview=full&geometries=geojson`;
}
function decodeGeo(route){return route.geometry.coordinates.map(c=>({lat:c[1],lng:c[0]}));}
async function goAnalyze(){
  if(!state.dest)return;
  show('analyze');
  mountMap('mapSlotAnalyze');
  document.getElementById('mapBadge1').textContent='킨텍스 → '+state.dest.name;
  document.getElementById('walkTitle').textContent='킨텍스 → '+state.dest.name+' 안심경로 이동 중…';
  document.getElementById('analyzeActions').classList.add('hidden');
  document.getElementById('analyzeSub').textContent='AI가 실제 보행자 후보 경로를 불러와 주변 안전요소를 스캔하고 있습니다…';
  document.getElementById('routeList').innerHTML=`<div class="card"><div style="text-align:center;padding:44px 10px"><div class="spinner"></div><div style="font-size:14px;font-weight:700;color:var(--sub)">후보 경로 분석 중…</div></div></div>`;
  layerRoute.clearLayers();layerChar.clearLayers();
  // start marker
  L.marker([DATA.start.lat,DATA.start.lng],{icon:startPin(),title:'출발 · 킨텍스',zIndexOffset:1000}).addTo(layerRoute);
  L.marker([state.dest.lat,state.dest.lng],{icon:destPin(),title:'도착 · '+state.dest.name,zIndexOffset:1000}).addTo(layerRoute);
  try{
    const routes=await fetchRoutes();
    if(!routes.length)throw new Error('no route');
    const metricsList=routes.map(rt=>routeRawMetrics(rt.poly,rt.len));
    const scoredList=scoreRoutesFromMetrics(metricsList);
    state.routes=routes.map((rt,i)=>({key:'r'+i,label:i===0?'추천 경로 후보 A':'경로 후보 '+String.fromCharCode(65+i),poly:rt.poly,dist:rt.len,...scoredList[i]}));
    state.routes.sort((a,b)=>(b.rank-a.rank)||(b.score-a.score));
    state.routes.forEach((r,i)=>r.label=i===0?'가장 안전한 경로':'대체 경로 '+i);
    state.chosen=state.routes[0];
    renderRouteList();
    drawRoutesOnMap(state.chosen.key);
    fitToRoute(state.chosen.poly);
  }catch(e){
    document.getElementById('routeList').innerHTML=`<div class="card"><p style="color:var(--bell);font-weight:700;font-size:14px">⚠ 경로를 불러오지 못했습니다.</p><p style="color:var(--sub);font-size:13px;margin-top:8px">인터넷 연결을 확인하거나 다른 목적지로 다시 시도해주세요.</p><button class="ghost-btn" onclick="backToSetup()">← 다시 설정</button></div>`;
  }
}
// 경로 도중에 방향이 거의 반대로(약 155도 이상) 꺾이는 구간이 있으면 "유턴성" 경로로 판단
function hasUTurn(poly){
  for(let i=1;i<poly.length-1;i++){
    const a=poly[i-1],b=poly[i],c=poly[i+1];
    const v1x=mx(b.lng)-mx(a.lng),v1y=my(b.lat)-my(a.lat);
    const v2x=mx(c.lng)-mx(b.lng),v2y=my(c.lat)-my(b.lat);
    const l1=Math.hypot(v1x,v1y),l2=Math.hypot(v2x,v2y);
    if(l1<3||l2<3)continue; // 너무 짧은 미세 구간은 노이즈이므로 스킵
    const cosA=(v1x*v2x+v1y*v2y)/(l1*l2);
    if(cosA<-0.9)return true;
  }
  return false;
}
// 목적지 방향(축)을 기준으로 "뒤로 되돌아간 총 거리"를 잰다.
// 옆으로 갔다가 축을 거슬러 돌아오는 후크/유턴형 경로를 잡아내기 위함(사진 사례).
// 옆 도로로 갈라지는 정상 우회는 축 방향 후진이 거의 없으므로 통과한다.
function backtrackDist(poly,s,d){
  const dx=mx(d.lng)-mx(s.lng),dy=my(d.lat)-my(s.lat),ln=Math.hypot(dx,dy)||1;
  let prev=null,back=0;
  for(const p of poly){
    const along=((mx(p.lng)-mx(s.lng))*dx+(my(p.lat)-my(s.lat))*dy)/ln; // 축 상의 전진 거리(m)
    if(prev!=null && along<prev) back+=(prev-along);
    prev=along;
  }
  return {back,straight:ln};
}
function isDetourish(poly,s,d){
  const {back,straight}=backtrackDist(poly,s,d);
  return back > Math.max(70, straight*0.10); // 축 기준 70m 또는 직선거리 10% 넘게 되돌아가면 후크로 간주
}
function isNatural(poly,s,d){return !hasUTurn(poly) && !isDetourish(poly,s,d);}
async function fetchRoutes(){
  const s={lat:DATA.start.lat,lng:DATA.start.lng},d=state.dest;
  // 1) OSRM 실제 보행 경로: 직선 최단 + 대안. 유턴/되돌아오는 경로는 제외.
  let base=[];
  try{
    const res=await fetch(osrmUrl([s,d]));const js=await res.json();
    if(js.code==='Ok'){js.routes.slice(0,3).forEach(rt=>{const poly=decodeGeo(rt);if(isNatural(poly,s,d))base.push({poly,len:rt.distance});});}
  }catch(e){}
  // OSRM이 자연스러운 경로를 하나도 안 줬을 때만, 최단 경로를 안전망으로 확보
  if(!base.length){try{const res=await fetch(osrmUrl([s,d]));const js=await res.json();
    if(js.code==='Ok'&&js.routes[0]){const poly=decodeGeo(js.routes[0]);if(!hasUTurn(poly))base.push({poly,len:js.routes[0].distance});}}catch(e){}}
  const baseLen=base.length?base[0].len:segDist(s,d)*1.3;
  const dx=d.lng-s.lng,dy=d.lat-s.lat,ln=Math.hypot(dx,dy)||1;
  // 옆 도로로 "완만히 갈라지는" 수준의 우회만 시도한다(축 방향 후진이 없어야 통과).
  const baseOff=Math.max(0.0026,(baseLen/111000)*0.16); // 대략 290m 안팎(살짝 더 완만하게)
  const corridorDeg=0.0035;
  function biasSignDeg(list){
    let pos=0,neg=0;
    list.forEach(f=>{
      const fx=f.lng-s.lng,fy=f.lat-s.lat;
      const along=(fx*dx+fy*dy)/ln;
      if(along<-0.001||along>ln+0.001)return;
      const perp=(fx*dy-fy*dx)/ln;
      if(Math.abs(perp)>corridorDeg)return;
      if(perp>=0)pos++;else neg++;
    });
    if(pos===neg)return 1;
    return pos>neg?1:-1;
  }
  const sCctv=biasSignDeg(DATA.cctv);
  const sBell=biasSignDeg(DATA.bell);
  // 중간 지점 1곳만 경유해 옆으로 완만히 갈라지게 한다.
  // 유턴이거나 목적지 축을 거슬러 되돌아오거나(=후크) 1.35배 넘게 길어지면 버린다.
  async function viaRoute(sign){
    const byLat=s.lat+dy*0.5,bx=s.lng+dx*0.5;
    for(const off of [baseOff,baseOff*0.6,baseOff*0.35]){
      const via={lat:byLat+(-dx/ln)*off*sign,lng:bx+(dy/ln)*off*sign};
      try{
        const r=await fetch(osrmUrl([s,via,d]));const j=await r.json();
        if(j.code==='Ok'&&j.routes[0]){
          const poly=decodeGeo(j.routes[0]),len=j.routes[0].distance;
          if(len>baseLen*1.35)continue;      // 너무 돌아가면 배제
          if(isNatural(poly,s,d))return {poly,len}; // 후크/유턴이면 배제
        }
      }catch(e){}
    }
    return null;
  }
  // 우선순위: OSRM이 준 자연스러운 대안들을 먼저 후보로 쓴다(인위적 우회 최소화).
  const routes=base.slice(0,3);
  // 대안이 부족할 때만, 옆으로 완만히 갈라지는 우회를 CCTV/비상벨 방향으로 보충한다.
  if(routes.length<3){const r=await viaRoute(sCctv);if(r)routes.push(r);}
  if(routes.length<3){let bSign=sBell;if(bSign===sCctv)bSign=-bSign;const r=await viaRoute(bSign);if(r)routes.push(r);}
  if(routes.length<3){const r=await viaRoute(-sCctv);if(r)routes.push(r);}
  // 중복 제거: 길이만이 아니라 실제 경로 모양(중간 지점 편차)까지 확인
  function pathsSimilar(a,b){
    if(Math.abs(a.len-b.len)>Math.max(60,a.len*0.03))return false;
    const N=6;let maxDiff=0;
    for(let i=0;i<=N;i++){const t=i/N;
      const pa=posAtS(a.poly,a.len*t),pb=posAtS(b.poly,b.len*t);
      maxDiff=Math.max(maxDiff,segDist(pa,pb));}
    return maxDiff<45;
  }
  const uniq=[];routes.forEach(r=>{if(!uniq.some(u=>pathsSimilar(u,r)))uniq.push(r);});
  return uniq.slice(0,3);
}
function fitToRoute(poly){const b=L.latLngBounds(poly.map(p=>[p.lat,p.lng]));b.extend([DATA.start.lat,DATA.start.lng]);map.fitBounds(b,{padding:[50,50]});}
function drawRoutesOnMap(highlightKey){
  layerRoute.eachLayer(l=>{if(l._isRoute)layerRoute.removeLayer(l);});
  // non-highlighted first
  state.routes.forEach(r=>{if(r.key===highlightKey)return;
    const pl=L.polyline(r.poly.map(p=>[p.lat,p.lng]),{color:'#9fb8ab',weight:5,opacity:.75,dashArray:'2 9'});pl._isRoute=true;pl.addTo(layerRoute);});
  const hr=state.routes.find(r=>r.key===highlightKey);
  const glow=L.polyline(hr.poly.map(p=>[p.lat,p.lng]),{color:'#34cf83',weight:14,opacity:.22});glow._isRoute=true;glow.addTo(layerRoute);
  const main=L.polyline(hr.poly.map(p=>[p.lat,p.lng]),{color:'#159a5b',weight:6,opacity:1});main._isRoute=true;main.addTo(layerRoute);
  // emphasize facilities near highlighted route
  const near=facsNearRoute(hr.poly);const cv=L.canvas({padding:.5});
  near.guard.forEach(f=>{const m=L.circleMarker([f.lat,f.lng],{renderer:cv,radius:3,color:'#f0980f',weight:0,fillColor:'#f0980f',fillOpacity:.85});m._isRoute=true;m.addTo(layerRoute);});
  near.cctv.forEach(f=>{const m=L.circleMarker([f.lat,f.lng],{renderer:cv,radius:5,color:'#2f6fed',weight:2,fillColor:'#2f6fed',fillOpacity:1});m._isRoute=true;m.addTo(layerRoute);});
  near.bell.forEach(f=>{const m=L.circleMarker([f.lat,f.lng],{renderer:cv,radius:6,color:'#fff',weight:2,fillColor:'#ef4657',fillOpacity:1});m._isRoute=true;m.addTo(layerRoute);});
}
function renderRouteList(){
  const list=document.getElementById('routeList');
  document.getElementById('analyzeSub').textContent='AI가 실제 보행자 경로 주변의 안전요소 밀도와 설정한 가중치를 종합해 Safe-Score를 산출했습니다.';
  list.innerHTML='<div class="card" style="padding:18px">'+state.routes.map((r,i)=>{const best=i===0;
    return `<div class="route-opt ${best?'best':''}" onclick="pickRoute('${r.key}')">
      <div class="rtop"><span class="rname">${r.label}${best?'<small>가장 안전</small>':''}</span><span class="badge">${best?'⭐ AI 추천':'후보'}</span></div>
      <div class="score-row"><span class="big">${r.score}</span><span class="unit">/100</span><span class="dist">이동거리<br><b>${Math.round(r.dist)}m</b></span></div>
      <div class="sbar"><i style="width:${r.score}%"></i></div>
      <div class="rfacts">🎥 CCTV <b>${r.counts.cctv}</b> · 💡 보안등 <b>${r.counts.guard}</b> · 🔔 비상벨 <b>${r.counts.bell}</b> · 🏪 Zone <b>${r.counts.zone}</b></div>
    </div>`;}).join('')+'</div>';
  document.getElementById('analyzeActions').classList.remove('hidden');
}
function pickRoute(key){state.chosen=state.routes.find(r=>r.key===key);
  document.querySelectorAll('.route-opt').forEach((el,i)=>el.classList.toggle('best',state.routes[i].key===key));
  drawRoutesOnMap(key);}

/* ===== walk ===== */
const EVMETA={
  cctv:{ic:'🎥',bg:'rgba(47,111,237,.12)',col:'#2f6fed',pt:1,title:c=>`CCTV 감시구간 · ${c}대`,desc:'이 구간은 CCTV로 감시됩니다. AI가 실시간 영상으로 이상행동을 자동 감지해요.'},
  guard:{ic:'💡',bg:'rgba(240,152,15,.14)',col:'#f0980f',pt:2,title:c=>`보안등 밝은구간 · ${c}개`,desc:'보안등이 밝혀 시야가 확보된 구간입니다. 야간 체감 안전도가 높아집니다.'},
  bell:{ic:'🔔',bg:'rgba(239,70,87,.12)',col:'#ef4657',pt:4,title:c=>`방범 비상벨`,desc:'위급 상황 시 버튼 한 번으로 관제센터·경찰과 즉시 연결됩니다.'},
  zone:{ic:'🏪',bg:'rgba(249,115,22,.12)',col:'#f97316',pt:8,title:c=>`Safe-Zone 진입`,desc:'심야 영업 제휴 매장입니다. 위급 시 잠시 대피할 수 있는 안전 거점이에요.'}
};
const ZONE_NAMES=['GS25','CU','세븐일레븐','이마트24','스타벅스','맥도날드','이디야커피','파리바게뜨'];
const ZONE_KIND={'GS25':'편의점','CU':'편의점','세븐일레븐':'편의점','이마트24':'편의점','스타벅스':'카페','맥도날드':'음식점','이디야커피':'카페','파리바게뜨':'베이커리'};
function buildEvents(poly){
  const near=facsNearRoute(poly),len=polyLen(poly);let ev=[];
  function cluster(arr,type,merge){arr.sort((a,b)=>a.s-b.s);let g=[];
    arr.forEach(f=>{const last=g[g.length-1];if(last&&f.s-last.sEnd<merge){last.items.push(f);last.sEnd=f.s;}else g.push({s:f.s,sEnd:f.s,items:[f]});});
    return g.map(x=>({s:(x.s+x.sEnd)/2,type,count:x.items.length,items:x.items}));}
  ev=ev.concat(cluster(near.cctv,'cctv',75));
  near.bell.forEach(f=>ev.push({s:f.s,type:'bell',count:1,items:[{lat:f.lat,lng:f.lng}]}));
  // guard: 실제 보안등을 '밝은 구간'으로 묶어 표시(있는 곳에서만 팝업 — 숫자를 부풀리지 않음)
  ev=ev.concat(cluster(near.guard,'guard',70));
  // safe-zone
  const zTot=zoneCountForRoute(len);for(let i=0;i<zTot;i++){const s=len*(i+.7)/(zTot+.4);const p=posAtS(poly,s);
    const nm=ZONE_NAMES[(i*3+Math.round(s))%ZONE_NAMES.length];
    ev.push({s,type:'zone',count:1,items:[{lat:p.lat,lng:p.lng,name:nm+' 안심매장',kind:ZONE_KIND[nm],hours:'심야 영업'}]});}
  // 🎯 안심 미션 지점: 경로 길이에 맞춰 균등 배치
  if(typeof MISSIONS!=='undefined' && MISSIONS.length){
    MISSIONS.forEach((ms,i)=>{const s=len*(i+1)/(MISSIONS.length+1);
      const p=posAtS(poly,s);
      ev.push({s,type:'mission',mission:ms,mi:i,items:[{lat:p.lat,lng:p.lng}]});});
  }
  ev.sort((a,b)=>a.s-b.s);
  return {events:ev,near};
}
function charIcon(gauge){const r=20+gauge/100*22;
  return L.divIcon({className:'',iconSize:[r*2,r*2],iconAnchor:[r,r],
    html:`<div class="char-ic" style="width:${r*2}px;height:${r*2}px">
      <div class="bubble" style="width:${r*2}px;height:${r*2}px"></div>
      <div class="body husskey"></div></div>`});}
// ===== Safe-Point = 걸으며 누적하는 안심 점수(54~96). 60 이상이면 성공, 미만이면 탈락. =====
// 안전요소를 지날 때 조금씩, Safe-Zone은 더 크게, 안심미션 성공은 더더 크게 쌓인다.
// (배점 비율: 보안등 < CCTV < 비상벨 < Safe-Zone < 미션 — 총합이 대략 54~96에 들어오도록 조정)
const MISSION_PT=12; // 미션 1회 성공 시 획득 Safe-Point
function livePoint(w){return Math.min(96, Math.round(w.points));}          // 걷는 중 표시(상한 96)
function finalPoint(w){return Math.max(54, Math.min(96, Math.round(w.points)));} // 최종 판정(54~96)
function startWalk(){
  show('walk');mountMap('mapSlotWalk');
  const poly=state.chosen.poly,len=polyLen(poly);
  const {events,near}=buildEvents(poly);
  state.walk={poly,len,events,near,evIdx:0,s:0,paused:false,speed:1,target:state.chosen.score,
    points:0,gauge:0,dist:0,pass:{cctv:0,guard:0,bell:0,zone:0},raf:null,last:null,totalEv:events.length||1,guardDots:[],
    missionActive:false,missionsDone:0,missionTotal:events.filter(e=>e.type==='mission').length,missionBonus:0};
  gaugeVal.textContent='0';distVal.textContent='0';
  state.walk.points=0;pointVal.textContent='0';
  ['pc','pg','pb','pz'].forEach(id=>document.getElementById(id).textContent='0');
  progFill.style.width='0%';setGauge(0);
  // draw chosen route only
  layerRoute.clearLayers();layerChar.clearLayers();
  L.marker([DATA.start.lat,DATA.start.lng],{icon:startPin(),zIndexOffset:1000}).addTo(layerRoute);
  L.marker([state.dest.lat,state.dest.lng],{icon:destPin(),zIndexOffset:1000}).addTo(layerRoute);
  L.polyline(poly.map(p=>[p.lat,p.lng]),{color:'#34cf83',weight:14,opacity:.2}).addTo(layerRoute);
  L.polyline(poly.map(p=>[p.lat,p.lng]),{color:'#159a5b',weight:6,opacity:1}).addTo(layerRoute);
  const cv=L.canvas({padding:.5});
  near.guard.forEach(f=>L.circleMarker([f.lat,f.lng],{renderer:cv,radius:2.8,color:'#f0980f',weight:0,fillColor:'#f0980f',fillOpacity:.55}).addTo(layerRoute));
  near.cctv.forEach(f=>L.circleMarker([f.lat,f.lng],{renderer:cv,radius:5,color:'#2f6fed',weight:2,fillColor:'#2f6fed',fillOpacity:1}).addTo(layerRoute));
  near.bell.forEach(f=>L.circleMarker([f.lat,f.lng],{renderer:cv,radius:6,color:'#fff',weight:2,fillColor:'#ef4657',fillOpacity:1}).addTo(layerRoute));
  // 🎯 미션 지점 마커
  events.filter(e=>e.type==='mission').forEach(e=>{const p=posAtS(poly,e.s);
    L.marker([p.lat,p.lng],{icon:L.divIcon({className:'',html:'<div class="mz-flag">🎯</div>',iconSize:[30,30],iconAnchor:[15,15]}),zIndexOffset:900}).addTo(layerRoute);});
  fitToRoute(poly);
  btnPause.textContent='⏸ 일시정지';spdLabel.textContent='1.0×';
  charMarker=L.marker([poly[0].lat,poly[0].lng],{icon:charIcon(0),zIndexOffset:1000}).addTo(layerChar);
  state.walk.last=null;state.walk.raf=requestAnimationFrame(walkTick);
}
function walkTick(ts){const w=state.walk;if(!w)return;
  if(w.paused){w.last=ts;w.raf=requestAnimationFrame(walkTick);return;}
  if(w.last==null)w.last=ts;let dt=(ts-w.last)/1000;w.last=ts;if(dt>0.1)dt=0.1;
  const base=Math.max(40,Math.min(150,w.len/28)); // 경로 길이에 맞춰 총 이동시간 ~28초로 보정
  const speed=base*w.speed;w.s=Math.min(w.len,w.s+speed*dt);w.dist=Math.round(w.s);
  distVal.textContent=w.dist;progFill.style.width=(w.s/w.len*100)+'%';
  while(w.evIdx<w.events.length&&w.s>=w.events[w.evIdx].s){
    const ev=w.events[w.evIdx];w.evIdx++;
    if(ev.type==='mission'){w.paused=true;w.missionActive=true;
      if(typeof openMission==='function')openMission(ev.mission,ev.mi);break;}
    fireEvent(ev);
  }
  const cur=posAtS(w.poly,w.s);if(charMarker)charMarker.setLatLng([cur.lat,cur.lng]);
  if(w.s>=w.len){finishWalk();return;}
  w.raf=requestAnimationFrame(walkTick);}
function fireEvent(ev){const w=state.walk,m=EVMETA[ev.type];const gained=m.pt*ev.count;
  w.points+=gained;w.pass[ev.type]+=ev.count;
  const frac=w.evIdx/w.totalEv;w.gauge=Math.min(w.target,Math.max(w.gauge,Math.round(w.target*Math.min(1,frac+0.12))));
  setGauge(w.gauge);
  animNum('pointVal',livePoint(w)); // 안전요소를 지날수록 Safe-Point 누적
  document.getElementById({cctv:'pc',guard:'pg',bell:'pb',zone:'pz'}[ev.type]).textContent=w.pass[ev.type];
  if(charMarker)charMarker.setIcon(charIcon(w.gauge));
  // add marker on map for guard/zone (they sit on the real road)
  const it=ev.items[0];
  if(ev.type==='guard')ev.items.forEach(g=>L.circleMarker([g.lat,g.lng],{radius:3.4,color:'#f0980f',weight:0,fillOpacity:.9}).addTo(layerRoute));
  if(ev.type==='zone')L.marker([it.lat,it.lng],{icon:L.divIcon({className:'',html:'<div style="font-size:18px;filter:drop-shadow(0 2px 3px rgba(0,0,0,.3))">🏪</div>',iconSize:[20,20],iconAnchor:[10,10]})}).addTo(layerRoute);
  pulseAt(it,m.col);
  const title=(ev.type==='zone'&&it.name)?`Safe-Zone · ${it.name}`:m.title(ev.count);
  const desc=(ev.type==='zone'&&it.name)?`${it.kind} · ${it.hours} · 위급 시 대피 가능한 안전 거점입니다.`:m.desc;
  showToast(m,title,desc,gained);
}
function showToast(m,title,desc,pts){const layer=document.getElementById('toastLayer');
  const el=document.createElement('div');el.className='toast';
  el.innerHTML=`<div class="tic" style="background:${m.bg}">${m.ic}</div><div class="tt"><b>${title}</b><p>${desc}</p><span class="pts">+${Math.round(pts)} Safe-Point</span></div>`;
  layer.appendChild(el);setTimeout(()=>{el.classList.add('out');setTimeout(()=>el.remove(),400)},2500);
  while(layer.children.length>1)layer.firstChild.remove();}
function pulseAt(it,col){if(!it)return;const c=L.circleMarker([it.lat,it.lng],{radius:6,color:col,weight:2.5,fill:false,opacity:1}).addTo(layerChar);
  let r=6,op=1;const iv=setInterval(()=>{r+=3.5;op-=0.09;c.setRadius(r);c.setStyle({opacity:op});if(op<=0){clearInterval(iv);layerChar.removeLayer(c);}},40);}
function setGauge(v){document.getElementById('gaugeArc').style.strokeDashoffset=490-(490*v/100);gaugeVal.textContent=v;}
function animNum(id,to){const el=document.getElementById(id);const from=+el.textContent||0;let i=0;const st=12;
  const iv=setInterval(()=>{i++;el.textContent=Math.round(from+(to-from)*i/st);if(i>=st)clearInterval(iv);},22);}
function togglePause(){const w=state.walk;if(!w)return;w.paused=!w.paused;btnPause.textContent=w.paused?'▶ 계속':'⏸ 일시정지';}
function setSpeed(){const w=state.walk;if(!w)return;const o=[1,1.6,2.4];w.speed=o[(o.indexOf(w.speed)+1)%o.length];spdLabel.textContent=w.speed.toFixed(1)+'×';}
function stopWalk(){if(state.walk&&state.walk.raf){cancelAnimationFrame(state.walk.raf);state.walk.raf=null;}
  if(typeof closeMission==='function')closeMission();}

/* 미션 팝업이 끝나면 mission.js 가 호출 — 보상 반영 후 이동 재개 */
function resumeMissionWalk(res){
  const w=state.walk;if(!w)return;
  if(res&&res.success){
    // 미션 성공 → 가장 큰 Safe-Point 획득 (SAFE 게이지는 상승하지 않음)
    w.points+=MISSION_PT;w.missionsDone++;w.missionBonus+=MISSION_PT;
    animNum('pointVal',livePoint(w));
  }
  w.missionActive=false;w.paused=false;w.last=null;
}
function finishWalk(){const w=state.walk;stopWalk();w.gauge=w.target;setGauge(w.target);setTimeout(showResult,650);}

/* ===== result ===== */
function showResult(){const w=state.walk;show('result');const sc=state.chosen.score;const sp=finalPoint(w);
  setTimeout(()=>{const a=document.getElementById('resArc');a.style.transition='stroke-dashoffset 1.3s cubic-bezier(.2,.9,.25,1)';a.style.strokeDashoffset=540-(540*sp/100);},120);
  animNum('resScore',sc);document.getElementById('resDist').textContent=w.dist;animNum('resPoint',sp);
  const tot=w.pass.cctv+w.pass.guard+w.pass.bell+w.pass.zone;document.getElementById('resPass').textContent=tot;
  const passed=sp>=60; // Safe-Point 60 미만이면 탈락
  document.getElementById('resSub').textContent=passed
    ? `킨텍스 → ${state.dest.name} · 안심경로 미션 성공! 🎉`
    : `킨텍스 → ${state.dest.name} · 아쉽게 탈락… 더 안전한 경로와 안심미션에 도전해보세요.`;
  let rank,style;
  if(passed){rank='성공 (PASS)';style='background:var(--green-l);color:var(--green-d)';}
  else{rank='탈락 (FAIL)';style='background:rgba(239,70,87,.14);color:var(--bell)';}
  const rk=document.getElementById('resRank');rk.textContent=rank;rk.style=style;
  document.getElementById('resBreak').innerHTML=`<div class="chip">CCTV <b>${w.pass.cctv}</b></div><div class="chip">보안등 <b>${w.pass.guard}</b></div><div class="chip">비상벨 <b>${w.pass.bell}</b></div><div class="chip">Safe-Zone <b>${w.pass.zone}</b></div>`
    +(w.missionTotal?`<div class="chip" style="background:var(--green-l);border-color:var(--line2)">안심미션 <b>${w.missionsDone}/${w.missionTotal}</b></div>`:'');
  document.getElementById('resNote').innerHTML=`Safe-Point는 지나온 안전요소·Safe-Zone·안심미션에서 쌓은 점수예요(안전요소 소, Safe-Zone 대, 미션 특대). <b>60점 이상이면 성공</b>, 미만이면 탈락입니다. · 이 경로의 Safe-Score ${sc}점은 안전요소 개수와 설정 가중치로 계산된 별도 지표예요.<br>기존 신고 중심 서비스와 달리, Safe-Point AI는 이동 전에 미리 안전한 길을 안내하고 지속적인 이용 동기를 제공합니다.`;
  fireConfetti(passed);}
function fireConfetti(big){const box=document.getElementById('confetti');box.innerHTML='';if(!big)return;
  const cols=['#22b06b','#34cf83','#2f6fed','#f0980f','#f97316'];
  for(let i=0;i<70;i++){const p=document.createElement('div');const x=Math.random()*100,dur=2.4+Math.random()*2,delay=Math.random()*1.1,sz=6+Math.random()*7;
    p.style.cssText=`position:absolute;top:-14px;left:${x}%;width:${sz}px;height:${sz*.5}px;background:${cols[i%cols.length]};border-radius:2px;opacity:.9;transform:rotate(${Math.random()*360}deg);animation:fall ${dur}s ${delay}s ease-in forwards`;
    box.appendChild(p);}}
const sf=document.createElement('style');sf.textContent='@keyframes fall{to{transform:translateY(420px) rotate(720deg);opacity:0}}';document.head.appendChild(sf);

/* ===== init ===== */
renderChips();onWeight();initMap();onNameInput();
document.getElementById('destInput').addEventListener('blur',()=>setTimeout(hideAC,150));
