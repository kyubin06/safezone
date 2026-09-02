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
const BUF=85, GUARD_SPACING=40;
function facsNearRoute(poly){
  const r={cctv:[],bell:[]};
  DATA.cctv.forEach(f=>{const pr=projectToRoute(f,poly);if(pr.d<=BUF)r.cctv.push({...f,s:pr.s})});
  DATA.bell.forEach(f=>{const pr=projectToRoute(f,poly);if(pr.d<=BUF*1.3)r.bell.push({...f,s:pr.s})});
  return r;
}
function guardCountForRoute(len){return Math.max(1,Math.round(len/GUARD_SPACING));}
function zoneCountForRoute(len){return Math.max(1,Math.min(4,Math.round(len/650)));}
function sat(x,k){return 1-Math.exp(-x/k)}
function getWeights(){const s=state.weights.c+state.weights.g+state.weights.b||1;
  return {c:state.weights.c/s,g:state.weights.g/s,b:state.weights.b/s}}
function routeRawMetrics(poly,len){
  const per=len/100, f=facsNearRoute(poly), guardN=guardCountForRoute(len), zoneN=zoneCountForRoute(len);
  const dC=f.cctv.length/per, dG=guardN/per, dB=f.bell.length*2/per;
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
  const nC=normList(metricsList.map(m=>m.dC));
  const nG=normList(metricsList.map(m=>m.dG));
  const nB=normList(metricsList.map(m=>m.dB));
  const W=getWeights();
  return metricsList.map((m,i)=>{
    const cover=W.c*nC[i]+W.g*nG[i]+W.b*nB[i];
    // Safe-Point 점수는 58~96 범위 안에서만 나오도록 제한
    let score=Math.round(60+30*cover+Math.min(6,m.zoneN*2));
    score=Math.max(58,Math.min(96,score));
    return {score,len:m.len,f:m.f,counts:{cctv:m.f.cctv.length,guard:m.guardN,bell:m.f.bell.length,zone:m.zoneN}};
  });
}

/* ===== state ===== */
let state={dest:null,weights:{c:5,g:5,b:5},routes:[],chosen:null,walk:null,userName:''};
const SUGGEST=[["대화역","대화역 3호선"],["일산호수공원","일산호수공원"],["주엽역","주엽역 3호선"],["정발산역","정발산역"],["킨텍스제2전시장","킨텍스 제2전시장"],["원마운트","원마운트 고양"]];

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
    state.routes.sort((a,b)=>b.score-a.score);
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
async function fetchRoutes(){
  const s={lat:DATA.start.lat,lng:DATA.start.lng},d=state.dest;
  let res=await fetch(osrmUrl([s,d]));let js=await res.json();
  let routes=[];
  if(js.code==='Ok'){js.routes.slice(0,3).forEach(rt=>{const poly=decodeGeo(rt);if(!hasUTurn(poly))routes.push({poly,len:rt.distance});});}
  const baseLen=routes.length?routes[0].len:segDist(s,d)*1.3;
  const dx=d.lng-s.lng,dy=d.lat-s.lat,ln=Math.hypot(dx,dy)||1;
  // 우회 경유지 오프셋을 넉넉하게 잡아야 실제로 다른 골목/도로로 갈라짐.
  // (오프셋이 작으면 OSRM이 결국 같은 큰길로 다시 합류시켜버려서 "다른 경로"처럼 안 보였음)
  const baseOff=Math.max(0.006,(baseLen/111000)*0.32);
  const corridorDeg=0.0035; // 직선 경로 기준 대략 380m 이내만 "근처"로 봄
  // 직선 경로를 기준으로 CCTV / 비상벨이 실제로 더 몰려 있는 쪽을 찾는다.
  function biasSignDeg(list){
    let pos=0,neg=0;
    list.forEach(f=>{
      const fx=f.lng-s.lng,fy=f.lat-s.lat;
      const along=(fx*dx+fy*dy)/ln;
      if(along<-0.001||along>ln+0.001)return;
      const perp=(fx*dy-fy*dx)/ln; // viaRoute의 오프셋 부호와 동일한 기준
      if(Math.abs(perp)>corridorDeg)return;
      if(perp>=0)pos++;else neg++;
    });
    if(pos===neg)return 1;
    return pos>neg?1:-1;
  }
  const sCctv=biasSignDeg(DATA.cctv);
  const sBell=biasSignDeg(DATA.bell);
  // 현재 사용자가 설정한 가중치를 기준으로 어느 방향(CCTV쪽/비상벨쪽)을 먼저 시도할지 정한다.
  // (보안등은 좌표 데이터가 없어 경로 모양을 좌우할 수 없으므로 방향 결정에서는 제외)
  const W=getWeights();
  const priority=[{sign:sCctv,w:W.c},{sign:sBell,w:W.b}].sort((a,b)=>b.w-a.w);
  async function viaRoute(frac,sign,offMul){
    const byLat=s.lat+dy*frac,bx=s.lng+dx*frac;
    // 오프셋을 큰 값부터 시도해서 확실히 갈라지는 경로부터 찾고, 유턴이 나올 때만 줄여서 재시도한다.
    // 안전을 위해 좀 더 도는 것은 이 앱의 취지상 정상이므로 "길다"는 이유만으로는 버리지 않는다.
    for(const off of [baseOff*offMul,baseOff*offMul*0.65,baseOff*offMul*0.4]){
      const via={lat:byLat+(-dx/ln)*off*sign,lng:bx+(dy/ln)*off*sign};
      try{
        const r=await fetch(osrmUrl([s,via,d]));const j=await r.json();
        if(j.code==='Ok'&&j.routes[0]){
          const poly=decodeGeo(j.routes[0]),len=j.routes[0].distance;
          if(len>baseLen*2.2)continue; // 지나치게(2배 이상) 길어지는 것만 배제
          if(!hasUTurn(poly))return {poly,len};
        }
      }catch(e){}
    }
    return null;
  }
  // 후보1: 경로 30% 지점에서, 현재 가중치가 더 높은 요소가 몰린 방향으로 크게 우회
  if(routes.length<3){const r=await viaRoute(0.3,priority[0].sign,1.15);if(r)routes.push(r);}
  // 후보2: 경로 70% 지점에서, 반대쪽(혹은 두 번째 요소 방향)으로 크게 우회 — 후보1과 겹치지 않도록 확실히 반대 부호 사용
  if(routes.length<3){
    let sign2=priority[1].sign;
    if(sign2===priority[0].sign)sign2=-sign2;
    const r=await viaRoute(0.7,sign2,1.15);if(r)routes.push(r);
  }
  // 그래도 후보가 부족하면 중간지점 양쪽으로 보충
  if(routes.length<2){const r=await viaRoute(0.5,1,1.3);if(r)routes.push(r);}
  if(routes.length<3){const r=await viaRoute(0.5,-1,1.3);if(r)routes.push(r);}
  // 중복 제거: 길이만으로 판단하지 않고, 실제 경로 모양(중간 지점들의 편차)까지 함께 확인
  // → 길이는 비슷해도 실제로 다른 길이면 서로 다른 후보로 남긴다
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
  cctv:{ic:'🎥',bg:'rgba(47,111,237,.12)',col:'#2f6fed',pt:4,title:c=>`CCTV 감시구간 · ${c}대`,desc:'이 구간은 CCTV로 감시됩니다. AI가 실시간 영상으로 이상행동을 자동 감지해요.'},
  guard:{ic:'💡',bg:'rgba(240,152,15,.14)',col:'#f0980f',pt:2,title:c=>`보안등 밝은구간 · ${c}개`,desc:'보안등이 밝혀 시야가 확보된 구간입니다. 야간 체감 안전도가 높아집니다.'},
  bell:{ic:'🔔',bg:'rgba(239,70,87,.12)',col:'#ef4657',pt:12,title:c=>`방범 비상벨`,desc:'위급 상황 시 버튼 한 번으로 관제센터·경찰과 즉시 연결됩니다.'},
  zone:{ic:'🏪',bg:'rgba(249,115,22,.12)',col:'#f97316',pt:25,title:c=>`Safe-Zone 진입`,desc:'심야 영업 제휴 매장입니다. 위급 시 잠시 대피할 수 있는 안전 거점이에요.'}
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
  // guard evenly (total=len/40), popups ~ every 180m
  const gTot=guardCountForRoute(len),nSeg=Math.max(1,Math.round(len/180));let placed=0;
  for(let i=0;i<nSeg;i++){const s=len*(i+.5)/nSeg;const cnt=i===nSeg-1?(gTot-placed):Math.round(gTot/nSeg);if(cnt<=0)continue;placed+=cnt;
    const p=posAtS(poly,s);ev.push({s,type:'guard',count:cnt,items:[{lat:p.lat,lng:p.lng,many:cnt}]});}
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
      <div class="body">🚶</div></div>`});}
function startWalk(){
  show('walk');mountMap('mapSlotWalk');
  const poly=state.chosen.poly,len=polyLen(poly);
  const {events,near}=buildEvents(poly);
  state.walk={poly,len,events,near,evIdx:0,s:0,paused:false,speed:1,target:state.chosen.score,
    points:0,gauge:0,dist:0,pass:{cctv:0,guard:0,bell:0,zone:0},raf:null,last:null,totalEv:events.length||1,guardDots:[],
    missionActive:false,missionsDone:0,missionTotal:events.filter(e=>e.type==='mission').length,missionBonus:0};
  gaugeVal.textContent='0';pointVal.textContent='0';distVal.textContent='0';
  ['pc','pg','pb','pz'].forEach(id=>document.getElementById(id).textContent='0');
  progFill.style.width='0%';setGauge(0);
  // draw chosen route only
  layerRoute.clearLayers();layerChar.clearLayers();
  L.marker([DATA.start.lat,DATA.start.lng],{icon:startPin(),zIndexOffset:1000}).addTo(layerRoute);
  L.marker([state.dest.lat,state.dest.lng],{icon:destPin(),zIndexOffset:1000}).addTo(layerRoute);
  L.polyline(poly.map(p=>[p.lat,p.lng]),{color:'#34cf83',weight:14,opacity:.2}).addTo(layerRoute);
  L.polyline(poly.map(p=>[p.lat,p.lng]),{color:'#159a5b',weight:6,opacity:1}).addTo(layerRoute);
  const cv=L.canvas({padding:.5});
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
  setGauge(w.gauge);animNum('pointVal',w.points);
  document.getElementById({cctv:'pc',guard:'pg',bell:'pb',zone:'pz'}[ev.type]).textContent=w.pass[ev.type];
  if(charMarker)charMarker.setIcon(charIcon(w.gauge));
  // add marker on map for guard/zone (they sit on the real road)
  const it=ev.items[0];
  if(ev.type==='guard')L.circleMarker([it.lat,it.lng],{radius:4,color:'#f0980f',weight:0,fillOpacity:.9}).addTo(layerRoute);
  if(ev.type==='zone')L.marker([it.lat,it.lng],{icon:L.divIcon({className:'',html:'<div style="font-size:18px;filter:drop-shadow(0 2px 3px rgba(0,0,0,.3))">🏪</div>',iconSize:[20,20],iconAnchor:[10,10]})}).addTo(layerRoute);
  pulseAt(it,m.col);
  const title=(ev.type==='zone'&&it.name)?`Safe-Zone · ${it.name}`:m.title(ev.count);
  const desc=(ev.type==='zone'&&it.name)?`${it.kind} · ${it.hours} · 위급 시 대피 가능한 안전 거점입니다.`:m.desc;
  showToast(m,title,desc,gained);
}
function showToast(m,title,desc,pts){const layer=document.getElementById('toastLayer');
  const el=document.createElement('div');el.className='toast';
  el.innerHTML=`<div class="tic" style="background:${m.bg}">${m.ic}</div><div class="tt"><b>${title}</b><p>${desc}</p><span class="pts">+${pts} Safe-Point</span></div>`;
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
    w.points+=res.reward||0;animNum('pointVal',w.points);
    w.target=Math.min(100,w.target+(res.gauge||0));
    w.gauge=Math.min(w.target,w.gauge+(res.gauge||0));setGauge(w.gauge);
    if(charMarker)charMarker.setIcon(charIcon(w.gauge));
    w.missionsDone++;w.missionBonus+=res.reward||0;
  }
  w.missionActive=false;w.paused=false;w.last=null;
}
function finishWalk(){const w=state.walk;stopWalk();w.gauge=w.target;setGauge(w.target);setTimeout(showResult,650);}

/* ===== result ===== */
function showResult(){const w=state.walk;show('result');const sc=state.chosen.score;
  setTimeout(()=>{const a=document.getElementById('resArc');a.style.transition='stroke-dashoffset 1.3s cubic-bezier(.2,.9,.25,1)';a.style.strokeDashoffset=540-(540*sc/100);},120);
  animNum('resScore',sc);document.getElementById('resDist').textContent=w.dist;animNum('resPoint',w.points);
  const tot=w.pass.cctv+w.pass.guard+w.pass.bell+w.pass.zone;document.getElementById('resPass').textContent=tot;
  document.getElementById('resSub').textContent=`킨텍스 → ${state.dest.name} · ${state.chosen.label} 체험 완료`;
  let rank,style;if(sc>=80){rank='매우 안전 (SAFE)';style='background:var(--green-l);color:var(--green-d)';}
  else if(sc>=65){rank='안전 (GOOD)';style='background:rgba(47,111,237,.12);color:#2f6fed';}
  else{rank='보통 (CARE)';style='background:rgba(240,152,15,.15);color:#b9740a';}
  const rk=document.getElementById('resRank');rk.textContent=rank;rk.style=style;
  document.getElementById('resBreak').innerHTML=`<div class="chip">CCTV <b>${w.pass.cctv}</b></div><div class="chip">보안등 <b>${w.pass.guard}</b></div><div class="chip">비상벨 <b>${w.pass.bell}</b></div><div class="chip">Safe-Zone <b>${w.pass.zone}</b></div>`
    +(w.missionTotal?`<div class="chip" style="background:var(--green-l);border-color:var(--line2)">안심미션 <b>${w.missionsDone}/${w.missionTotal}</b></div>`:'');
  document.getElementById('resNote').innerHTML=`설정한 가중치(CCTV ${wtc.textContent}% · 보안등 ${wtg.textContent}% · 비상벨 ${wtb.textContent}%)를 반영해 계산된 Safe-Score입니다.<br>기존 신고 중심 서비스와 달리, Safe-Point AI는 이동 전에 미리 안전한 길을 안내하고 지속적인 이용 동기를 제공합니다.`;
  fireConfetti(sc>=80);}
function fireConfetti(big){const box=document.getElementById('confetti');box.innerHTML='';if(!big)return;
  const cols=['#22b06b','#34cf83','#2f6fed','#f0980f','#f97316'];
  for(let i=0;i<70;i++){const p=document.createElement('div');const x=Math.random()*100,dur=2.4+Math.random()*2,delay=Math.random()*1.1,sz=6+Math.random()*7;
    p.style.cssText=`position:absolute;top:-14px;left:${x}%;width:${sz}px;height:${sz*.5}px;background:${cols[i%cols.length]};border-radius:2px;opacity:.9;transform:rotate(${Math.random()*360}deg);animation:fall ${dur}s ${delay}s ease-in forwards`;
    box.appendChild(p);}}
const sf=document.createElement('style');sf.textContent='@keyframes fall{to{transform:translateY(420px) rotate(720deg);opacity:0}}';document.head.appendChild(sf);

/* ===== init ===== */
renderChips();onWeight();initMap();onNameInput();
document.getElementById('destInput').addEventListener('blur',()=>setTimeout(hideAC,150));
