"use strict";
/* ============ PicaPhoto 移动版 v1.2.0 ============ */
/* 原生桥接 */
const BRIDGE = (typeof window !== "undefined" && window.Android) || null;
const APP_VERSION = (BRIDGE && BRIDGE.getAppVersion && BRIDGE.getAppVersion()) || "1.2.3";
const GITHUB_API = "https://api.github.com/repos/Yan16384/PicaPhoto/releases/latest";
let phoneAlbums = [];
let phoneAlbum = null;        // 当前浏览的手机相册 bucket id
let phoneMedia = [];          // 当前手机相册媒体

/* ============ 数据层（IndexedDB v3：media / albums / trash / stats） ============ */
const DB_NAME = "picaphoto";
let db = null;
function openDB(){
  return new Promise((res,rej)=>{
    const rq = indexedDB.open(DB_NAME, 3);
    rq.onupgradeneeded = e => {
      const d = e.target.result;
      if(!d.objectStoreNames.contains("media")) d.createObjectStore("media", {keyPath:"id"});
      if(!d.objectStoreNames.contains("albums")) d.createObjectStore("albums", {keyPath:"id"});
      if(!d.objectStoreNames.contains("trash")) d.createObjectStore("trash", {keyPath:"id"});
      if(!d.objectStoreNames.contains("stats")) d.createObjectStore("stats", {keyPath:"key"});
    };
    rq.onsuccess = e => { db = e.target.result; res(db); };
    rq.onerror = () => rej(rq.error);
  });
}
function tx(store, mode){ return db.transaction(store, mode).objectStore(store); }
function storeGetAll(store){ return new Promise(r => { const q = tx(store).getAll(); q.onsuccess = () => r(q.result||[]); q.onerror = () => r([]); }); }
function storePut(store, obj){ return new Promise(r => { const q = tx(store,"readwrite").put(obj); q.onsuccess = () => r(true); q.onerror = () => r(false); }); }
function storePutAll(store, objs){ return new Promise(r => { if(!objs.length){ r(); return; } const t = tx(store,"readwrite"); let left=objs.length; objs.forEach(o=>{ const q=t.put(o); q.onsuccess=()=>{ if(--left===0) r(); }; }); }); }
function storeDel(store, id){ return new Promise(r => { const q = tx(store,"readwrite").delete(id); q.onsuccess = () => r(true); q.onerror = () => r(false); }); }
function storeDelAll(store, ids){ return new Promise(r => { if(!ids.length){ r(); return; } const t = tx(store,"readwrite"); let left=ids.length; ids.forEach(id=>{ const q=t.delete(id); q.onsuccess=()=>{ if(--left===0) r(); }; }); }); }

/* ============ 状态 ============ */
let media = [];
let albums = [];
let appTrash = [];
let phoneTrash = [];
let trashList = [];
let tab = "org";            // org | me
let orgSub = "home";        // home | photos | trash
let currentAlbum = null;
let selection = new Set();
let multi = false;
let theme = localStorage.getItem("pp_theme") || "auto";
let urls = new Map();
let lastTrashed = null;
let favs = new Set(JSON.parse(localStorage.getItem("pp_favs")||"[]"));
let stats = { organizedTotal:0, organizedByDay:{}, trashTotal:0, restoreTotal:0, startDate:null };
let calYear, calMonth;
let statsDirty = 0, statsTimer = null;
let storageCache = { t:0, bytes:0 };
let gridCols = (parseInt(localStorage.getItem("pp_grid_cols")||"3",10)||3);
gridCols = Math.max(2, Math.min(6, gridCols));

/* ============ 工具 ============ */
const $ = s => document.querySelector(s);
function uid(){ return Date.now().toString(36) + Math.random().toString(36).slice(2,8); }
function toast(msg, act, fn){
  const t=$("#toast");
  t.innerHTML = "<span>"+escapeHtml(msg)+"</span>" + (fn ? '<button class="act" id="toastAct">'+escapeHtml(act)+"</button>" : "");
  t.classList.add("show"); clearTimeout(t._h);
  const a=$("#toastAct");
  if(a){ a.onclick=()=>{ t.classList.remove("show"); fn(); }; }
  t._h=setTimeout(()=>t.classList.remove("show"),2600);
}
function isVideo(m){ return (m.type||m.mime||"").startsWith("video/"); }
function itemKey(m){ return m.uri || m.id; }
function objURL(m){
  if(m.uri) return m.uri;
  if(urls.has(m.id)) return urls.get(m.id);
  if(!m.blob) return "";
  const u=URL.createObjectURL(m.blob); urls.set(m.id,u); return u;
}
function revokeObj(id){ if(urls.has(id)){ try{ URL.revokeObjectURL(urls.get(id)); }catch(e){} urls.delete(id); } }
function escapeHtml(s){ return (s||"").replace(/[&<>"']/g, c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c])); }
function isFav(m){ return m.uri ? favs.has(m.uri) : favs.has(m.id); }
function toggleFav(m){
  const k = m.uri || m.id;
  if(favs.has(k)) favs.delete(k); else favs.add(k);
  localStorage.setItem("pp_favs", JSON.stringify([...favs]));
  updateViewerChrome();
}
function vibrate(ms){ try{ navigator.vibrate && navigator.vibrate(ms||15); }catch(e){} }
/* 长按：触发回调并抑制随后的 click（避免误进入相册/查看器） */
function bindLong(el, fn){
  let th=null, longFired=false;
  const cancel=()=>{ clearTimeout(th); th=null; };
  el.addEventListener("touchstart", ()=>{ longFired=false; th=setTimeout(()=>{ longFired=true; vibrate(15); fn(); },480); },{passive:true});
  el.addEventListener("touchmove", cancel,{passive:true});
  el.addEventListener("touchend", cancel);
  el.addEventListener("touchcancel", cancel);
  el.addEventListener("click", (e)=>{ if(longFired){ e.stopPropagation(); e.preventDefault(); longFired=false; } });
}

/* ============ 主题：跟随系统（APK 用原生 isSystemDark，网页用媒体查询） ============ */
function systemDark(){
  if(BRIDGE && BRIDGE.isSystemDark){
    try{ return !!BRIDGE.isSystemDark(); }catch(e){}
  }
  return matchMedia("(prefers-color-scheme: dark)").matches;
}
function currentTheme(){ return theme==="auto" ? (systemDark()?"dark":"light") : theme; }
function applyTheme(){
  const t = currentTheme();
  document.documentElement.dataset.theme = t;
  const m = document.querySelector('meta[name="theme-color"]');
  if(m) m.content = t === "dark" ? "#17181c" : "#f2f3f5";
  /* 全面屏：注入状态栏/导航栏高度 + 状态栏图标自动变色 */
  if(BRIDGE){
    try{
      const st=BRIDGE.getStatusBarHeight ? BRIDGE.getStatusBarHeight() : 0;
      const nb=BRIDGE.getNavBarHeight ? BRIDGE.getNavBarHeight() : 0;
      document.documentElement.style.setProperty("--safe-t", (st||0)+"px");
      document.documentElement.style.setProperty("--safe-b", (nb||0)+"px");
      if(BRIDGE.setStatusBarDark) BRIDGE.setStatusBarDark(t==="light");
      if(BRIDGE.setNavBarDark) BRIDGE.setNavBarDark(t==="light");
    }catch(e){}
  }
  const sw=$("#swTheme");
  if(sw) sw.classList.toggle("on", t==="dark");
  const td=$("#themeDesc");
  if(td) td.textContent = theme==="auto" ? "跟随系统" : (t==="dark" ? "深色" : "浅色");
  if(tab==="me") renderMe();
}
window.__sysDarkChanged = ()=>{ if(theme==="auto"){ applyTheme(); } };
if(matchMedia && matchMedia("(prefers-color-scheme: dark)").addEventListener){
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", ()=>{ if(theme==="auto") applyTheme(); });
}

/* ============ 整理统计（独立存储 + 批量防抖写入） ============ */
function todayKey(){ const d=new Date(); return d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0")+"-"+String(d.getDate()).padStart(2,"0"); }
async function loadStats(){
  const rows=await storeGetAll("stats");
  const s=rows.find(x=>x.key==="main");
  if(s){ stats=s; }
  else { stats={ organizedTotal:0, organizedByDay:{}, trashTotal:0, restoreTotal:0, startDate:null }; stats.key="main"; await saveStatsNow(); }
}
function saveStatsNow(){ return storePut("stats", stats); }
function recordStats(type, n){
  const k = todayKey();
  if(type==="move"){ stats.organizedTotal += n; stats.organizedByDay[k] = (stats.organizedByDay[k]||0) + n; if(!stats.startDate) stats.startDate = k; }
  else if(type==="trash"){ stats.trashTotal += n; }
  else if(type==="restore"){ stats.restoreTotal += n; }
  statsDirty += n;
  clearTimeout(statsTimer);
  statsTimer = setTimeout(()=>{ if(statsDirty){ statsDirty=0; saveStatsNow(); } }, 400);
}
function storageBytes(force){
  const now=Date.now();
  if(!force && now-storageCache.t < 1500 && storageCache.bytes>0) return storageCache.bytes;
  let s=0;
  for(const m of media){ if(m.blob && m.blob.size) s += m.blob.size; }
  for(const t of appTrash){ if(t.blob && t.blob.size) s += t.blob.size; }
  storageCache={ t:now, bytes:s };
  return s;
}
function fmtBytes(n){
  if(n < 1024*1024) return (n/1024).toFixed(0) + " KB";
  return (n/1024/1024).toFixed(1) + " MB";
}

/* ============ 手机相册（原生桥接） ============ */
let phoneMediaCache = new Map();
const PHONE_CACHE_TTL = 300000;      // 5 分钟
const PHONE_CACHE_MAX = 12;          // 最多缓存 12 个相册，防内存膨胀
function refreshPhoneAlbums(force){
  if(!BRIDGE) return;
  try{
    if(!force){
      const c=localStorage.getItem("pp_albums_cache");
      if(c){ const o=JSON.parse(c); if(o && o.albums && Date.now()-o.t<PHONE_CACHE_TTL && BRIDGE.hasPermission()){ phoneAlbums=o.albums; return; } }
    }
    if(!BRIDGE.hasPermission()){ phoneAlbums=[]; return; }
    phoneAlbums=JSON.parse(BRIDGE.readAlbums());
    try{ localStorage.setItem("pp_albums_cache", JSON.stringify({t:Date.now(), albums:phoneAlbums})); }catch(e){}
    const ids=new Set(phoneAlbums.map(a=>a.id));
    for(const key of [...phoneMediaCache.keys()]){ if(!ids.has(key)) phoneMediaCache.delete(key); }
  }catch(e){ phoneAlbums=[]; }
}
function readPhoneMedia(id, cb){
  const c=phoneMediaCache.get(id);
  if(c && Date.now()-c.t<PHONE_CACHE_TTL){ cb && cb(c.items.filter(x=>!trashedUris.has(x.uri))); return; }
  if(!BRIDGE || !BRIDGE.readMediaAsync){ cb && cb([]); return; }
  window.__mediaCb = json => {
    let items=[];
    try{ items=JSON.parse(json); }catch(e){}
    phoneMediaCache.set(id,{t:Date.now(), items});
    if(phoneMediaCache.size>PHONE_CACHE_MAX){
      let oldest=null;
      for(const [k,v] of phoneMediaCache){ if(!oldest || v.t<oldest.v.t) oldest={k,v}; }
      if(oldest) phoneMediaCache.delete(oldest.k);
    }
    cb && cb(items.filter(x=>!trashedUris.has(x.uri)));
  };
  BRIDGE.readMediaAsync(id, "__mediaCb");
}
function clearPhoneMediaCache(id){ if(id) phoneMediaCache.delete(id); else phoneMediaCache.clear(); try{ localStorage.removeItem("pp_albums_cache"); }catch(e){} }
function requestPhonePermission(){
  if(!BRIDGE) return;
  BRIDGE.requestPermission();
  toast("请在系统弹窗中允许访问照片");
  setTimeout(()=>{ refreshPhoneAlbums(); renderHome(); }, 1600);
}
function openPhoneAlbum(id, name){
  phoneAlbum = id; currentAlbum = null; orgSub = "photos";
  exitMulti();
  phoneMedia = [];
  showOrg();
  $("#photos").innerHTML = '<div class="empty"><div class="big">⏳</div>正在加载相册…</div>';
  readPhoneMedia(id, items=>{
    phoneMedia = items;
    renderPhotos();
  });
}
function exitPhoneMode(){
  phoneAlbum = null; phoneMedia = [];
  exitMulti();
  goHome();
}

/* ============ 整理首页（相册网格 + 回收站 + 新建相册） ============ */
function h(txt){ const el=document.createElement("div"); el.className="set-h full"; el.textContent=txt; return el; }
function createdAlbums(){ try{ return JSON.parse(localStorage.getItem("pp_created")||"[]"); }catch(e){ return []; } }
function addCreated(n){ const a=createdAlbums(); if(!a.includes(n)){ a.push(n); localStorage.setItem("pp_created", JSON.stringify(a)); } }
function removeCreated(n){ localStorage.setItem("pp_created", JSON.stringify(createdAlbums().filter(x=>x!==n))); }
function albumTargets(){
  /* 所有手机相册（含 PicaPhoto 系列与系统相册）+ 用户新建相册 */
  const map=new Map();
  phoneAlbums.forEach(a=>{ map.set(a.name, a); });
  createdAlbums().forEach(n=>{ if(!map.has(n)) map.set(n,{name:n}); });
  return [...map.values()];
}
function createSystemAlbum(name, cb){
  try{ BRIDGE.createAlbum(name); }catch(e){ toast("创建失败："+e); return; }
  addCreated(name);
  /* 不强制重读系统相册（大媒体库查询慢导致卡顿），延迟后台刷新，界面立即响应 */
  if(BRIDGE && BRIDGE.hasPermission) setTimeout(()=>{ try{ refreshPhoneAlbums(true); }catch(e){} }, 900);
  if(cb) cb();
}
function renderHome(){
  const box=$("#albums");
  box.className="";
  box.innerHTML="";
  box.appendChild(h("手机相册"));
  if(BRIDGE && !BRIDGE.hasPermission()){
    const p=document.createElement("div"); p.className="full empty";
    p.innerHTML='<div class="big">🖼️</div>需要权限才能读取手机相册<br><button class="big-btn" id="btnPerm">授权读取相册</button>';
    box.appendChild(p);
    p.querySelector("#btnPerm").addEventListener("click", requestPhonePermission);
  } else if(BRIDGE){
    const g=document.createElement("div"); g.className="pgalb-grid";
    phoneAlbums.forEach((a,ai)=>{
      const c=document.createElement("div"); c.className="pgalb anim-pop";
      c.dataset.albumId=a.id;
      c.innerHTML='<div class="cover">'+(a.cover?'<img loading="lazy" decoding="async" src="'+a.cover+'" alt="">':'<div style="height:100%"></div>')+'</div><div class="name">'+escapeHtml(a.name)+'</div><div class="cnt">'+a.count+' 项</div>';
      c.style.animationDelay=(ai*40)+"ms";
      c.addEventListener("click", ()=>{ openPhoneAlbum(a.id, a.name); });
      bindLong(c, ()=>phoneAlbumMenu(a));
      g.appendChild(c);
    });
    box.appendChild(g);
    if(!phoneAlbums.length){
      const p=document.createElement("div"); p.className="full empty";
      p.innerHTML='<div class="big">📭</div>手机相册为空<br><span style="font-size:13px">下拉可刷新</span>';
      box.appendChild(p);
    }
  } else {
    const p=document.createElement("div"); p.className="full empty";
    p.innerHTML='<div class="big">📱</div>请安装安卓版 PicaPhoto 使用';
    box.appendChild(p);
  }
  const nb=document.createElement("button"); nb.className="big-btn"; nb.textContent="＋ 新建相册";
  nb.addEventListener("click", ()=>{ if(!BRIDGE){ toast("请在 App 中使用"); return; } promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v); renderHome(); toast("已创建相册「"+v+"」"); } }); });
  box.appendChild(nb);
}
/* 手机相册管理：删除相册（询问是否删除相册内照片）/ 刷新 */
function phoneAlbumMenu(a){
  sheet([{ic:"🗑️",t:"删除相册",f:()=>confirmDeletePhoneAlbum(a)},
          {ic:"⟳",t:"刷新列表",f:()=>{ refreshPhoneAlbums(true); renderHome(); toast("已刷新"); }}],"管理相册");
}
let pendingDelAlbumName = null;
function confirmDeletePhoneAlbum(a){
  if(!confirm("删除相册「"+a.name+"」？\n相册内的 "+a.count+" 张照片将从系统中真正删除，不可恢复！")) return;
  readPhoneMedia(a.id, items=>{
    const uris=(items||[]).map(x=>x.uri).filter(u=>u && !trashedUris.has(u));
    if(!uris.length){ toast("相册为空"); return; }
    pendingDelAlbumName = a.name;   // 系统确认成功后再移除“新建相册”记录
    requestRealDelete(uris);        // 系统确认弹窗，确认后 __deleted 刷新
  });
}
function openPhotosView(albumId){ currentAlbum=albumId; orgSub="photos"; exitMulti(); showOrg(); }
function visibleMedia(){ return phoneAlbum!==null ? phoneMedia : (currentAlbum===null?media:media.filter(m=>m.album===currentAlbum)); }

/* 下拉刷新（整理首页） */
(function(){
  const v=$("#view-home");
  let pullStart=null, pulled=0;
  v.addEventListener("touchstart", e=>{ if(e.touches.length===1 && v.scrollTop<=0){ pullStart=e.touches[0].clientY; pulled=0; } },{passive:true});
  v.addEventListener("touchmove", e=>{
    if(pullStart===null || v.scrollTop>0) return;
    pulled=Math.max(0, e.touches[0].clientY-pullStart);
    const hh=$("#pullHint");
    hh.classList.add("show");
    hh.textContent = pulled>70 ? "松开刷新" : "下拉刷新";
  },{passive:true});
  v.addEventListener("touchend", ()=>{
    const hh=$("#pullHint");
    if(pullStart!==null && pulled>70){
      hh.textContent="正在刷新…";
      refreshPhoneAlbums(true);
      setTimeout(()=>{ hh.classList.remove("show"); renderHome(); toast("已刷新相册列表"); },350);
    } else {
      hh.classList.remove("show");
    }
    pullStart=null; pulled=0;
  },{passive:true});
})();
/* 照片网格：横向滑动进入管理模式 */
(function(){
  const v=$("#view-photos");
  let sx=null, sy=null, active=false;
  v.addEventListener("touchstart", e=>{ if(e.touches.length===1){ sx=e.touches[0].clientX; sy=e.touches[0].clientY; active=true; } },{passive:true});
  v.addEventListener("touchmove", e=>{
    if(!active || multi) return;
    const dx=e.touches[0].clientX-sx, dy=e.touches[0].clientY-sy;
    if(Math.abs(dx)>30 && Math.abs(dx)>Math.abs(dy)*1.3){
      active=false;
      /* 进入管理模式的同时选中手指当前的照片，滑动即开始选 */
      const el=document.elementFromPoint(e.touches[0].clientX, e.touches[0].clientY);
      const ph=el && el.closest ? el.closest(".ph") : null;
      const firstKey = ph && ph.dataset.key ? ph.dataset.key : null;
      enterMulti(firstKey ? [firstKey] : []);
      toast(firstKey ? "管理模式：继续滑动连续选择" : "管理模式：点击选择");
    }
  },{passive:true});
  v.addEventListener("touchend", ()=>{ active=false; },{passive:true});
})();
/* 小图网格：双指捏合调整排列（张开=变大，最多横排2；合拢=变小，最少横排6） */
(function(){
  const v=$("#view-photos");
  let pinch0=0, cols0=gridCols;
  v.addEventListener("touchstart", e=>{
    if(e.touches.length===2){ pinch0=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY); cols0=gridCols; }
  },{passive:true});
  v.addEventListener("touchmove", e=>{
    if(e.touches.length<2 || pinch0<=0) return;
    const d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
    let nc = cols0 - Math.round((d-pinch0)/70);
    nc = Math.max(2, Math.min(6, nc));
    if(nc!==gridCols){
      gridCols=nc;
      try{ localStorage.setItem("pp_grid_cols", String(gridCols)); }catch(e){}
      applyGridCols();
      vibrate(8);
    }
  },{passive:true});
  v.addEventListener("touchend", ()=>{ pinch0=0; },{passive:true});
  v.addEventListener("touchcancel", ()=>{ pinch0=0; },{passive:true});
})();
/* 管理模式：横向滑动可连续选中（点选/取消仍有效） */
(function(){
  const box=$("#photos");
  let sx=null, sy=null, mode=null, active=false, lastKey=null;
  box.addEventListener("touchstart", e=>{ if(multi && e.touches.length===1){ sx=e.touches[0].clientX; sy=e.touches[0].clientY; mode=null; active=true; lastKey=null; } },{passive:true});
  box.addEventListener("touchmove", e=>{
    if(!multi || !active || sx===null) return;
    const dx=e.touches[0].clientX-sx, dy=e.touches[0].clientY-sy;
    if(mode===null && (Math.abs(dx)>18 || Math.abs(dy)>18)) mode = Math.abs(dx)>Math.abs(dy) ? "h" : "v";
    if(mode!=="h") return;
    e.preventDefault();   // 仅横向滑选时阻止页面滚动
    const el=document.elementFromPoint(e.touches[0].clientX, e.touches[0].clientY);
    const ph=el && el.closest ? el.closest(".ph") : null;
    if(ph && ph.dataset.key && ph.dataset.key!==lastKey){
      lastKey=ph.dataset.key;
      if(!selection.has(lastKey)){ selection.add(lastKey); ph.classList.add("sel-on"); refreshBadges(); }
    }
  },{passive:false});
  box.addEventListener("touchend", ()=>{ active=false; sx=null; mode=null; lastKey=null; },{passive:true});
})();

/* ============ 照片网格（懒加载分块渲染 + 滚动位置保持） ============ */
let phEls = new Map();
let phRendered = 0;
let phObserver = null;
const PH_CHUNK = 60;
function applyGridCols(){ const box=$("#photos"); if(box && box.className==="ph-grid") box.style.gridTemplateColumns="repeat("+gridCols+",1fr)"; }
function buildPhotoEl(m){
  const key = itemKey(m);
  const el = document.createElement("div");
  el.className = "ph";
  el.dataset.key = key;
  el.innerHTML = '<img loading="lazy" decoding="async" src="'+(m.thumb||m.uri||objURL(m))+'" alt=""><span class="idx"></span>'+(isVideo(m)?'<span class="dur">▶</span>':'');
  if(multi && selection.has(key)){ el.classList.add("sel-on"); el.querySelector(".idx").textContent = [...selection].indexOf(key)+1; }
  if(multi) el.classList.add("multi");
  /* 入场动画：仅首批 60 项依次浮现；滚动加载的项立即显示（避免延迟白屏） */
  if(phRendered < PH_CHUNK){
    el.classList.add("anim-pop");
    el.style.animationDelay = (phRendered*25)+"ms";
  }
  phEls.set(key, el);
  return el;
}
function itemsIndexOf(m){ return visibleMedia().indexOf(m); }
function renderChunk(items){
  const box = $("#photos");
  const end = Math.min(items.length, phRendered + PH_CHUNK);
  for(; phRendered < end; phRendered++){
    box.appendChild(buildPhotoEl(items[phRendered]));
  }
  let sent = document.getElementById("phMore");
  if(phRendered < items.length){
    if(!sent){ sent=document.createElement("div"); sent.id="phMore"; sent.style.height="1px"; box.appendChild(sent); }
    if(!phObserver){
      phObserver = new IntersectionObserver(entries=>{
        if(entries.some(e=>e.isIntersecting)) renderChunk(visibleMedia());
      }, {root:document.getElementById("view-photos")||null, rootMargin:"300px"});
    }
    phObserver.observe(sent);
  } else {
    if(sent) sent.remove();
    if(phObserver){ phObserver.disconnect(); phObserver=null; }
  }
}
function renderPhotos(keepScroll){
  const box = $("#photos");
  const items = visibleMedia();
  const view=$("#view-photos");
  const prevTop = keepScroll ? (view ? view.scrollTop : 0) : 0;
  phEls = new Map();
  if(phObserver){ phObserver.disconnect(); phObserver=null; }
  phRendered = 0;
  if(!items.length){
    box.className="";
    box.innerHTML = '<div class="empty"><div class="big">📷</div>还没有照片<br><span style="font-size:13px">点击上方相册进入</span></div>';
    return;
  }
  box.className = "ph-grid";
  box.innerHTML = "";
  applyGridCols();
  renderChunk(items);
  if(keepScroll && prevTop>0 && view){ requestAnimationFrame(()=>{ view.scrollTop = prevTop; }); }
}
function refreshBadges(){
  let i=1;
  for(const k of selection){ const e=phEls.get(k); if(e){ const b=e.querySelector(".idx"); if(b) b.textContent=i; } i++; }
  updateSelbar();
}
function toggleSel(key, el){
  if(selection.has(key)){ selection.delete(key); el&&el.classList.remove("sel-on"); if(el){ const b=el.querySelector(".idx"); if(b) b.textContent=""; } }
  else { selection.add(key); el&&el.classList.add("sel-on"); }
  refreshBadges();
}
function enterMulti(initial){
  multi = true; selection = new Set(initial||[]);
  /* 不重建 DOM：仅给现有照片加管理模式类，切换零卡顿无白屏 */
  phEls.forEach((el,key)=>{
    el.classList.add("multi");
    if(selection.has(key)){ el.classList.add("sel-on"); const b=el.querySelector(".idx"); if(b) b.textContent=[...selection].indexOf(key)+1; }
  });
  $("#selbar").classList.add("show");
  $("#selDel").style.display = "";
  if(phoneAlbum!==null) renderMultiAlbums();
  $("#title").textContent = "选择照片";
  refreshBadges();
}
function exitMulti(){
  multi = false; selection = new Set();
  /* 不重建 DOM：直接移除管理模式类 */
  phEls.forEach(el=>{ el.classList.remove("multi","sel-on"); const b=el.querySelector(".idx"); if(b) b.textContent=""; });
  $("#selbar").classList.remove("show");
  $("#multiAlbums").classList.remove("show");
  $("#multiAlbums").innerHTML = "";
  if(orgSub==="photos") updateTitle();
}
function updateSelbar(){
  const c=$("#selCount");
  c.textContent = selection.size + " 项";
  c.classList.remove("bump"); void c.offsetWidth; c.classList.add("bump");
}
function updateTitle(){
  if(tab==="me"){ $("#title").textContent="我的"; return; }
  if(orgSub==="home"){ $("#title").textContent="整理"; return; }
  if(orgSub==="trash"){ $("#title").textContent="回收站"; return; }
  $("#title").textContent = phoneAlbum!==null ? "手机相册" : (currentAlbum===null ? "全部照片" : ((albums.find(a=>a.id===currentAlbum)||{}).name||"照片"));
}

/* 移动选中（记录整理统计） */
function moveSelected(){
  const list = visibleMedia().filter(m=>selection.has(itemKey(m)));
  if(!list.length) return;
  if(phoneAlbum===null){ toast("请先进入手机相册"); return; }
  const opts = albumTargets().map(a=>({ic:"📁",t:a.name,f:()=>nativeMove(a.name,list)}));
  opts.push({ic:"➕",t:"新建相册…",f:()=>promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v, ()=>nativeMove(v,list)); } })});
  sheet(opts,"移动到相册");
}
function nativeMove(name, list){
  if(!list || !list.length) return;
  try {
    const uris = JSON.stringify(list.map(m=>m.uri));
    toast("正在移动…");
    if(!BRIDGE || !BRIDGE.moveToAlbumAsync){ toast("移动失败"); return; }
    window.__moveCb = resJson => {
      let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
      const ok=res.filter(r=>r.ok).length, fail=res.length-ok;
      if(ok) recordStats("move", ok);
      clearPhoneMediaCache();
      if(ok>0){
        /* 移入后留在当前相册并刷新网格 */
        if(phoneAlbum!==null){
          readPhoneMedia(phoneAlbum, items=>{ phoneMedia=items; });
        }
        if(BRIDGE && BRIDGE.hasPermission) refreshPhoneAlbums(true);
        exitMulti();
        renderPhotos();
        toast(ok+" 项已移入「"+name+"」"+(fail>0?"，"+fail+" 项无权限跳过":""));
      } else {
        toast("移动失败：所选照片无权限或无法移动");
      }
    };
    BRIDGE.moveToAlbumAsync(name, uris, "__moveCb");
  } catch(e){ toast("移动失败："+e); }
}
async function removeSelected(){
  const list = visibleMedia().filter(m=>selection.has(itemKey(m)));
  if(!list.length) return;
  /* 移入回收站无需确认（可恢复，系统文件不删除） */
  if(phoneAlbum!==null){
    for(const m of list){ await trashPhone(m); }
    exitMulti();
    await refreshTrash();
    toast("已移入回收站 "+list.length+" 项");
    return;
  }
  const ids = [...selection].filter(k => k && !k.startsWith("content:"));
  if(!ids.length) return;
  for(const k of ids){ const m = media.find(x=>x.id===k); if(m){ await trashOne(m); } }
  exitMulti();
  saveState();
}

/* ============ 回收站（App 内软删除：系统文件不动，清空回收站时才真正删除） ============ */
let trashedUris = new Set();   // 已回收的手机相册 uri，用于从相册中过滤
async function refreshTrash(){
  const all = await storeGetAll("trash");
  appTrash = all.filter(t=>!t.fromPhone);
  phoneTrash = all.filter(t=>t.fromPhone);
  trashList = [
    ...appTrash.map(t=>({id:t.id, name:t.name, mime:t.mime, isVideo:t.isVideo, trashedAt:t.trashedAt, blob:t.blob, fromApp:true})),
    ...phoneTrash.map(t=>({id:t.id, name:t.name, mime:t.mime, isVideo:t.isVideo, uri:t.uri, trashedAt:t.trashedAt, fromPhone:true}))
  ];
  trashedUris = new Set(phoneTrash.map(t=>t.uri));
  const d=$("#trashCardD");
  if(d) d.textContent = trashList.length ? ("共 "+trashList.length+" 项 · 上滑照片即可回收") : "上滑照片即可回收，误删可找回";
}
let trashRendered = 0, trashObserver = null;
function renderTrash(){
  const box=$("#trash");
  const view=$("#view-trash");
  const prevTop = view ? view.scrollTop : 0;
  box.className="ph-grid";
  box.innerHTML="";
  trashRendered = 0;
  if(trashObserver){ trashObserver.disconnect(); trashObserver=null; }
  if(!trashList.length){
    box.innerHTML='<div class="empty full"><div class="big">🗑️</div>回收站是空的<br><span style="font-size:13px">查看照片时上滑即可移入回收站</span></div>';
    return;
  }
  renderTrashChunk();
  if(view && prevTop>0) requestAnimationFrame(()=>{ view.scrollTop = prevTop; });
}
function trashEl(m){
  const el=document.createElement("div"); el.className="ph";
  el.innerHTML='<img loading="lazy" decoding="async" src="'+(m.thumb||m.uri||objURL(m))+'" alt="">'+(m.isVideo?'<span class="dur">▶</span>':'');
  if(trashRendered < PH_CHUNK){ el.classList.add("anim-pop"); el.style.animationDelay=(trashRendered*25)+"ms"; }
  el.addEventListener("click", ()=>{ openViewer(trashList, trashList.indexOf(m), "trash"); });
  bindLong(el, ()=>sheetTrashItem(m));
  return el;
}
function renderTrashChunk(){
  const box=$("#trash");
  const end = Math.min(trashList.length, trashRendered + 60);
  for(; trashRendered < end; trashRendered++){ box.appendChild(trashEl(trashList[trashRendered])); }
  let sent = document.getElementById("trMore");
  if(trashRendered < trashList.length){
    if(!sent){ sent=document.createElement("div"); sent.id="trMore"; sent.style.height="1px"; box.appendChild(sent); }
    if(!trashObserver){
      trashObserver = new IntersectionObserver(entries=>{
        if(entries.some(e=>e.isIntersecting)) renderTrashChunk();
      }, {root:document.getElementById("view-trash")||null, rootMargin:"300px"});
    }
    trashObserver.observe(sent);
  } else {
    if(sent) sent.remove();
    if(trashObserver){ trashObserver.disconnect(); trashObserver=null; }
  }
  if(trashRendered >= trashList.length){
    const actions=document.createElement("div");
    actions.className="trash-actions full";
    actions.innerHTML='<button class="big-btn ghost" id="btnRestoreAll">↩️ 全部恢复</button><button class="big-btn danger" id="btnEmpty">清空回收站</button>';
    box.appendChild(actions);
    $("#btnRestoreAll").addEventListener("click", restoreAllTrash);
    $("#btnEmpty").addEventListener("click", emptyTrash);
  }
}
function sheetTrashItem(m){
  sheet([{ic:"↩️",t:"恢复",f:()=>restoreFromTrash(m)},
          {ic:"🗑️",t:"彻底删除",f:()=>permanentDelete(m)}],"回收站操作");
}
/* 手机照片移入回收站：只做 App 内标记，系统文件不动 */
async function trashPhone(m){
  const rec={id:"p_"+m.uri, uri:m.uri, name:m.name, mime:m.mime||m.type||"", isVideo:!!((m.mime||m.type)||"").startsWith("video/"), trashedAt:Date.now(), fromPhone:true};
  await storePut("trash", rec);
  trashedUris.add(m.uri);
  const idx=phoneMedia.indexOf(m); if(idx>=0) phoneMedia.splice(idx,1);
  lastTrashed={type:"phone", uri:m.uri, id:rec.id};
  recordStats("trash",1);
}
async function restoreFromTrash(m){
  if(m.fromPhone){
    await storeDel("trash", m.id);
    trashedUris.delete(m.uri);
    recordStats("restore",1);
    toast("已恢复");
  } else {
    const rec=appTrash.find(t=>t.id===m.id);
    if(rec){
      media.push(restoreObj(rec));
      await storePut("media", restoreObj(rec));
      await storeDel("trash",rec.id);
      recordStats("restore",1);
      toast("已恢复");
    }
  }
  await refreshTrash(); renderTrash();
  refreshActiveView();
}
function restoreObj(rec){
  return {id:rec.id, name:rec.name, type:rec.mime, size:0, addedAt:Date.now(), album:null, blob:rec.blob};
}
async function permanentDelete(m){
  if(m.fromPhone){ requestRealDelete([m.uri]); return; }
  revokeObj(m.id);
  await storeDel("trash", m.id);
  toast("已彻底删除");
  await refreshTrash(); renderTrash();
}
async function restoreAllTrash(){
  const apps=appTrash.slice(), ph=phoneTrash.slice();
  let n=0;
  for(const t of apps){ const obj=restoreObj(t); media.push(obj); n++; await storePut("media",obj); await storeDel("trash",t.id); }
  for(const t of ph){ await storeDel("trash", t.id); trashedUris.delete(t.uri); n++; }
  if(n) recordStats("restore", n);
  toast("已恢复 "+n+" 项");
  await refreshTrash(); renderTrash();
  refreshActiveView();
}
async function emptyTrash(){
  if(!trashList.length) return;
  if(!confirm("确定清空回收站？\n手机相册中的照片将从系统中真正删除，不可恢复！")) return;
  const apps = trashList.filter(m=>!m.fromPhone);
  const ph = trashList.filter(m=>m.fromPhone).map(m=>m.uri);
  for(const m of apps){ revokeObj(m.id); await storeDel("trash", m.id); }
  if(ph.length){
    requestRealDelete(ph);
  } else {
    toast("回收站已清空");
    await refreshTrash(); renderTrash();
  }
}

/* 真正删除手机照片：走系统确认弹窗（Android 10+），用户确认后 __deleted 回调清理 */
let pendingDelUris = [];
function requestRealDelete(uris){
  if(!uris.length) return;
  pendingDelUris = uris;
  try{ BRIDGE.requestDelete(JSON.stringify(uris)); }catch(e){ toast("删除失败："+e); }
}
window.__deleted = async ()=>{
  const set = new Set(pendingDelUris); pendingDelUris=[];
  const all = await storeGetAll("trash");
  const delIds = all.filter(t=>t.fromPhone && set.has(t.uri)).map(t=>t.id);
  await storeDelAll("trash", delIds);
  delIds.forEach(id=>{ const t=all.find(x=>x.id===id); if(t) trashedUris.delete(t.uri); });
  if(pendingDelAlbumName){ removeCreated(pendingDelAlbumName); pendingDelAlbumName=null; }
  await refreshTrash();
  if(BRIDGE && BRIDGE.hasPermission) refreshPhoneAlbums(true);
  toast("已从系统删除 " + set.size + " 项");
  refreshActiveView();
}

/* ============ 移入回收站 / 撤销 ============ */
async function trashOne(m){
  if(m.uri && m.uri.startsWith("content:")){
    await trashPhone(m);
    toastTrash();
  } else {
    const tr={id:m.id, name:m.name, mime:m.type||"", isVideo:!!(m.type||"").startsWith("video/"), trashedAt:Date.now(), blob:m.blob};
    await storePut("trash",tr);
    await storeDel("media", m.id);
    const idx=media.indexOf(m); if(idx>=0) media.splice(idx,1);
    lastTrashed={type:"app", item:tr};
    recordStats("trash",1);
    toastTrash();
  }
  await refreshTrash();
}
function toastTrash(){ toast("已移入回收站","撤销",()=>undoTrash()); }
async function undoTrash(){
  if(!lastTrashed) return;
  const t=lastTrashed; lastTrashed=null;
  if(t.type==="phone"){
    await storeDel("trash", t.id || ("p_"+t.uri));
    trashedUris.delete(t.uri);
    recordStats("restore",1);
    clearPhoneMediaCache();
    refreshPhoneAlbums(true);
    if(phoneAlbum!==null) readPhoneMedia(phoneAlbum, items=>{ phoneMedia=items; });
    toast("已撤销");
  } else {
    const tr=t.item;
    media.push(restoreObj(tr));
    await storeDel("trash",tr.id);
    await storePut("media",restoreObj(tr));
    recordStats("restore",1);
    toast("已撤销");
  }
  await refreshTrash();
  refreshActiveView();
  updateViewerChrome();
}

/* ============ 全屏查看器（窗口化渲染 + 邻居预加载） ============ */
let viewerList=[], viewerIdx=0, viewerMode="normal";
let g=null, longT=null, lastTap=0, zoomed=false, pinch=0;
let vSlots=[]; const VWIN=2;

function openViewer(list, idx, mode){
  viewerList=list; viewerIdx=idx; viewerMode=mode||"normal"; zoomed=false; lastTap=0;
  $("#viewer").classList.add("open");
  buildSlides();
  setTrack(0,0,1,false);
  updateViewerChrome();
  document.body.style.overflow="hidden";
  $("#vHint").classList.add("show");
  $("#vHint").textContent = mode==="trash" ? "↑ 上滑删除 · ↓ 下滑返回" : "↑ 上滑回收 · ↓ 下滑返回";
  setTimeout(()=>{ if($("#viewer").classList.contains("open")) $("#vHint").classList.remove("show"); },2200);
}
function closeViewer(){
  $("#viewer").classList.remove("open");
  document.body.style.overflow="";
  clearTimeout(longT); g=null;
  vSlots.forEach(s=>{ s.el.remove(); }); vSlots=[];
  refreshActiveView();
}
function setTrack(dx, dy, sc, animate){
  const t=$("#vTrack");
  t.style.transition = animate ? "transform .32s cubic-bezier(.2,.8,.2,1)" : "none";
  t.style.transform = "translate(calc("+(-viewerIdx*100)+"% + "+dx+"px), "+dy+"px) scale("+sc+")";
}
function clearZoomAll(){ vSlots.forEach(s=>s.el.classList.remove("zoomed","peek")); }
function buildSlides(){
  const track=$("#vTrack");
  const lo=Math.max(0,viewerIdx-VWIN), hi=Math.min(viewerList.length-1,viewerIdx+VWIN);
  const keep=new Set();
  for(let i=lo;i<=hi;i++){
    let slot=vSlots.find(s=>s.idx===i);
    if(!slot){
      const el=document.createElement("div"); el.className="slide";
      el.style.transform="translateX("+(i*100)+"%)";
      track.appendChild(el);
      slot={idx:i, el}; vSlots.push(slot);
    }
    setSlideContent(slot.el, viewerList[i]);
    keep.add(slot);
  }
  vSlots=vSlots.filter(s=>{
    if(!keep.has(s)){ track.removeChild(s.el); return false; }
    return true;
  });
  preloadIdx(viewerIdx+VWIN+1);
  preloadIdx(viewerIdx-VWIN-1);
}
function setSlideContent(el, m){
  const src=objURL(m);
  if(isVideo(m)){
    let v=el.querySelector("video");
    if(!v){ el.innerHTML='<video src="'+src+'" playsinline controls></video>'; }
    else if(v.src!==src){ v.src=src; v.controls=true; }
    else v.controls=true;
  } else {
    let im=el.querySelector("img");
    if(!im){ el.innerHTML='<img src="'+src+'" alt="" decoding="async">'; }
    else if(im.src!==src){ im.src=src; }
  }
}
function preloadIdx(i){
  if(i<0 || i>=viewerList.length) return;
  const m=viewerList[i]; if(!m) return;
  const src=m.uri || (m.blob ? objURL(m) : "");
  if(src){ const im=new Image(); im.src=src; }
}
function updateViewerChrome(){
  const m=viewerList[viewerIdx];
  if(!m) return;
  $("#vCount").textContent=(viewerIdx+1)+" / "+viewerList.length;
  const work=$("#vWork");
  if(viewerMode==="trash"){
    work.innerHTML='<div class="vw-btns"><button id="vRestore">↩️ 恢复</button><button class="danger" id="vDel">🗑️ 彻底删除</button></div>';
    $("#vRestore").addEventListener("click", async ()=>{
      const mm=viewerList[viewerIdx];
      await restoreFromTrash(mm);
      const i=viewerList.indexOf(mm); if(i>=0) viewerList.splice(i,1); afterViewerRemove();
    });
    $("#vDel").addEventListener("click", async ()=>{
      const mm=viewerList[viewerIdx];
      await permanentDelete(mm);
      const i=viewerList.indexOf(mm); if(i>=0) viewerList.splice(i,1); afterViewerRemove();
    });
  } else {
    const f=isFav(m);
    let chips='<div class="vchip new" id="vNew">＋ 新建</div>';
    albumTargets().forEach(a=>{ chips+='<div class="vchip" data-alb="'+escapeHtml(a.name)+'">'+escapeHtml(a.name)+'</div>'; });
    work.innerHTML='<div class="vw-albums">'+chips+'</div>'+
      '<div class="vw-btns">'+
      '<button class="'+(f?'on':'')+'" id="vFav">'+(f?'♥':'♡')+' 收藏</button>'+
      '<button id="vUndo" style="'+(lastTrashed?'':'display:none')+'">↩ 撤销</button>'+
      '<button id="vTrash">🗑 回收</button>'+
      '<button id="vClose2">✕ 关闭</button>'+
      '</div>';
    work.querySelectorAll(".vchip").forEach(c=>{
      c.addEventListener("click", ()=>{
        if(c.id==="vNew"){ promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v, ()=>moveCurrentTo(v)); } }); }
        else if(c.classList.contains("on")){ moveOutCurrent(c.dataset.alb); }
        else { moveCurrentTo(c.dataset.alb); }
      });
    });
    /* 高亮当前照片所属相册（照片自带 albumNames，readMedia 时原生已附带） */
    try{
      const names = new Set((m.albumNames||[]).map(n=>String(n)));
      if(names.size){
        work.querySelectorAll(".vchip[data-alb]").forEach(c=>{
          if(names.has(c.dataset.alb)) c.classList.add("on");
        });
      }
    }catch(e){}
    $("#vFav").addEventListener("click", ()=>{ toggleFav(viewerList[viewerIdx]); });
    $("#vUndo").addEventListener("click", ()=>{ undoTrash(); });
    $("#vTrash").addEventListener("click", ()=>{ doTrashCurrent(); });
    $("#vClose2").addEventListener("click", closeViewer);
  }
}
/* 大图浏览：把当前照片移出所属相册（移到 PicaPhoto 整理区） */
function moveOutCurrent(name){
  const m=viewerList[viewerIdx];
  if(!m) return;
  if(!m.uri || !m.uri.startsWith("content:")){ toast("仅系统相册照片支持移出"); return; }
  if(!BRIDGE || !BRIDGE.moveOutAlbumAsync){ toast("移出失败"); return; }
  try{
    window.__moCb = resJson => {
      let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
      if(res[0]&&res[0].ok){
        recordStats("move",1);
        clearPhoneMediaCache();
        const idx=phoneMedia.indexOf(m); if(idx>=0) phoneMedia.splice(idx,1);
        const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
        afterViewerRemove();
        toast("已移出「"+name+"」到 PicaPhoto");
      } else toast("移出失败");
    };
    BRIDGE.moveOutAlbumAsync(JSON.stringify([m.uri]), "__moCb");
  }catch(e){ toast("移出失败："+e); }
}
function afterViewerRemove(){
  if(!viewerList.length){ closeViewer(); return; }
  if(viewerIdx>=viewerList.length) viewerIdx=viewerList.length-1;
  buildSlides();
  setTrack(0,0,1,false);
  updateViewerChrome();
}
function moveViewer(step){
  const ni=Math.max(0,Math.min(viewerList.length-1,viewerIdx+step));
  if(ni===viewerIdx){ setTrack(0,0,1,true); return; }
  viewerIdx=ni; zoomed=false;
  clearZoomAll();
  buildSlides();
  setTrack(0,0,1,true);
  updateViewerChrome();
}
async function moveCurrentTo(name){
  const m=viewerList[viewerIdx];
  if(!m) return;
  if(m.uri && m.uri.startsWith("content:")){
    if(!BRIDGE || !BRIDGE.moveToAlbumAsync){ toast("移动失败"); return; }
    try{
      window.__mcCb = resJson => {
        let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
        if(res[0]&&res[0].ok){
          recordStats("move",1);
          clearPhoneMediaCache();
          const idx=phoneMedia.indexOf(m); if(idx>=0) phoneMedia.splice(idx,1);
          const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
          afterViewerRemove();
          toast("已移入「"+name+"」");
        } else toast("移动失败");
      };
      BRIDGE.moveToAlbumAsync(name, JSON.stringify([m.uri]), "__mcCb");
    }catch(e){ toast("移动失败："+e); }
  } else {
    const a=albums.find(x=>x.name===name);
    m.album = a ? a.id : null;
    await storePut("media", m);
    recordStats("move",1);
    toast("已移入「"+name+"」");
    updateViewerChrome();
  }
}

/* ---- 手势：左右切换 / 上滑回收 / 下滑返回 / 点按 / 长按 Peek / 捏合退出 ---- */
$("#viewer").addEventListener("touchstart", e=>{
  if(e.touches.length>1){
    pinch=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
    g=null; clearTimeout(longT);
    return;
  }
  const t=e.touches[0];
  g={mode:null, sx:t.clientX, sy:t.clientY, dx:0, dy:0, moved:false, t0:Date.now(), long:false};
  clearTimeout(longT);
  longT=setTimeout(()=>{
    if(g && !g.moved && g.mode===null){
      g.long=true; vibrate(12);
      const cur=vSlots.find(s=>s.idx===viewerIdx);
      if(cur) cur.el.classList.add("peek");
      $("#vHint").classList.add("show");
      $("#vHint").textContent = viewerMode==="trash" ? "↑ 上滑删除 · ↓ 下滑返回" : "↑ 上滑回收 · ↓ 下滑返回";
    }
  },360);
},{passive:true});

$("#viewer").addEventListener("touchmove", e=>{
  if(e.touches.length>1){
    const d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
    if(pinch>0 && Math.abs(d-pinch)>50){ pinch=0; closeViewer(); return; }
    return;
  }
  if(!g) return;
  const t=e.touches[0];
  const dx=t.clientX-g.sx, dy=t.clientY-g.sy;
  if(g.mode===null){
    if(Math.abs(dx)>14 || Math.abs(dy)>14){
      g.mode = Math.abs(dy)>Math.abs(dx) ? "v" : "h";
      if(g.mode==="h"){ clearTimeout(longT); const cur=vSlots.find(s=>s.idx===viewerIdx); if(cur) cur.el.classList.remove("peek"); $("#vHint").classList.remove("show"); }
    }
  }
  if(g.mode===null) return;
  e.preventDefault();
  g.dx=dx; g.dy=dy; g.moved=true;
  if(g.mode==="h"){
    setTrack(dx, 0, 1, false);
  } else {
    const cy=Math.max(-320,Math.min(320,dy));
    const sc=Math.max(.86, 1-Math.abs(cy)/1400);
    setTrack(0, cy, sc, false);
    const zone=$("#vTrashZone");
    zone.classList.toggle("show", viewerMode==="normal" && cy<-70);
    $("#vHint").classList.toggle("show", !(cy<-70));
    if(cy<-70) $("#vHint").textContent="松手移入回收站";
    else if(cy>80) $("#vHint").textContent="松手返回";
    else $("#vHint").textContent = viewerMode==="trash" ? "↑ 上滑删除 · ↓ 下滑返回" : "↑ 上滑回收 · ↓ 下滑返回";
  }
},{passive:false});

$("#viewer").addEventListener("touchend", e=>{
  clearTimeout(longT);
  if(!g) return;
  const g0=g; g=null;
  const cur=vSlots.find(s=>s.idx===viewerIdx);
  if(cur) cur.el.classList.remove("peek");
  $("#vHint").classList.remove("show");
  $("#vTrashZone").classList.remove("show");
  if(g0.long && g0.mode==="v"){
    if(g0.dy<-70) doTrashCurrent();
    else if(g0.dy>70) closeViewer();
    else setTrack(0,0,1,true);
    return;
  }
  if(g0.mode==="h"){
    if(g0.dx<-60) moveViewer(1);
    else if(g0.dx>60) moveViewer(-1);
    else setTrack(0,0,1,true);
    return;
  }
  if(g0.mode==="v"){
    if(g0.dy<-70){ setTrack(0,-120,.9,true); setTimeout(()=>doTrashCurrent(),200); }
    else if(g0.dy>70){ setTrack(0,120,1,true); setTimeout(()=>closeViewer(),200); }
    else { setTrack(0,0,1,true); }
    return;
  }
  const now=Date.now();
  if(!g0.moved && now-g0.t0<350){
    if(now-lastTap<300){
      zoomed=!zoomed;
      const s=vSlots.find(x=>x.idx===viewerIdx);
      if(s) s.el.classList.toggle("zoomed", zoomed);
      lastTap=0;
    } else {
      lastTap=now;   // 修复：记录单次轻触时间，双击缩放才生效
    }
  }
},{passive:true});

$("#viewer").addEventListener("touchcancel", ()=>{
  clearTimeout(longT); g=null;
  const cur=vSlots.find(s=>s.idx===viewerIdx); if(cur) cur.el.classList.remove("peek");
  $("#vHint").classList.remove("show"); $("#vTrashZone").classList.remove("show");
});
$("#vClose").addEventListener("click", closeViewer);

async function doTrashCurrent(){
  const m=viewerList[viewerIdx];
  if(!m) return;
  const cur=vSlots.find(s=>s.idx===viewerIdx);
  if(cur){ cur.el.classList.add("flyout-up"); await new Promise(r=>setTimeout(r,140)); }
  const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
  afterViewerRemove();   // 先重建视图，避免等待异步删除导致黑屏
  if(viewerMode==="trash"){ await permanentDelete(m); } else { await trashOne(m); }
}

/* ============ 底部弹层 / 对话框 ============ */
function sheet(opts, title){
  $("#sheetTitle").textContent = title || "选择操作";
  const list=$("#sheetList"); list.innerHTML="";
  opts.forEach(o=>{
    const el=document.createElement("div"); el.className="opt";
    el.innerHTML='<span class="ic">'+o.ic+'</span><span>'+escapeHtml(o.t)+'</span>';
    el.addEventListener("click", ()=>{ closeSheet(); o.f(); });
    list.appendChild(el);
  });
  $("#sheet").classList.add("open");
}
function closeSheet(){ $("#sheet").classList.remove("open"); }
$("#sheetX").addEventListener("click", closeSheet);
$("#sheet").addEventListener("click", e=>{ if(e.target===$("#sheet")) closeSheet(); });
function promptInput(title, value, onOk){
  $("#dlgTitle").textContent=title;
  const inp=$("#dlgInput"); inp.value=value||""; inp.focus();
  $("#dlg").classList.add("open");
  const ok=$("#dlgOk"), cancel=$("#dlgCancel");
  ok.onclick=async ()=>{ const v=inp.value.trim(); if(!v){ toast("名称不能为空"); return; } $("#dlg").classList.remove("open"); await onOk(v); };
  cancel.onclick=()=>{ $("#dlg").classList.remove("open"); };
  inp.onkeydown=e=>{ if(e.key==="Enter") ok.click(); };
}

/* ============ 我的：统计 / 日历 / 存储 / 设置 ============ */
function monthTotal(){
  const y=calYear, m=calMonth;
  const days=new Date(y,m+1,0).getDate();
  let n=0;
  for(let d=1;d<=days;d++){
    const key=y+"-"+String(m+1).padStart(2,"0")+"-"+String(d).padStart(2,"0");
    n += stats.organizedByDay[key]||0;
  }
  return n;
}
function renderCalendar(){
  const y=calYear, m=calMonth;
  const first=new Date(y,m,1);
  const startDow=(first.getDay()+6)%7;
  const days=new Date(y,m+1,0).getDate();
  const prevDays=new Date(y,m,0).getDate();
  const prevM = m===0 ? 11 : m-1, prevY = m===0 ? y-1 : y;
  const nextM = m===11 ? 0 : m+1, nextY = m===11 ? y+1 : y;
  let html="";
  for(let i=0;i<startDow;i++){
    const d=prevDays-startDow+i+1;
    const key=prevY+"-"+String(prevM+1).padStart(2,"0")+"-"+String(d).padStart(2,"0");
    html+=calCell(key,d,stats.organizedByDay[key]||0,true);
  }
  for(let d=1;d<=days;d++){
    const key=y+"-"+String(m+1).padStart(2,"0")+"-"+String(d).padStart(2,"0");
    html+=calCell(key,d,stats.organizedByDay[key]||0,false);
  }
  const total=startDow+days, rem=(7-total%7)%7;
  for(let i=1;i<=rem;i++){
    const key=nextY+"-"+String(nextM+1).padStart(2,"0")+"-"+String(i).padStart(2,"0");
    html+=calCell(key,i,stats.organizedByDay[key]||0,true);
  }
  const g=$("#calGrid"); if(g) g.innerHTML=html;
  const t=$("#calTitle"); if(t) t.textContent=y+" 年 "+(m+1)+" 月";
  const mt=$("#calMonthTotal"); if(mt) mt.textContent="本月整理 "+monthTotal()+" 张";
}
function calCell(key,d,n,muted){
  const lvl = n===0 ? 0 : (n<3?1 : (n<6?2 : 3));
  return '<div class="cal-day lvl'+lvl+(muted?' muted':'')+'" title="'+key+'">'+d+(n?'<b>'+n+'</b>':'')+'</div>';
}
function renderMe(){
  const s=$("#view-me");
  const view=$("#view-me");
  const prevTop = view ? view.scrollTop : 0;
  const darkOn = currentTheme()==="dark";
  const tot=storageBytes();
  const todayN=stats.organizedByDay[todayKey()]||0;
  const themeDesc = theme==="auto" ? "跟随系统" : (theme==="dark" ? "深色" : "浅色");
  s.innerHTML=`
    <div class="me-head">
      <img src="icon-192.png" alt="">
      <div><div class="me-name">PicaPhoto</div><div class="me-ver">移动版 v${APP_VERSION} · Phoom 手势 · 自动更新</div></div>
    </div>
    <div class="stat-grid">
      <div class="stat"><b>${stats.organizedTotal}</b><span>累计整理</span></div>
      <div class="stat"><b>${todayN}</b><span>今日整理</span></div>
      <div class="stat"><b>${stats.trashTotal}</b><span>累计回收</span></div>
      <div class="stat"><b>${stats.restoreTotal}</b><span>累计恢复</span></div>
      <div class="stat"><b>${favs.size}</b><span>收藏</span></div>
      <div class="stat"><b>${trashList.length}</b><span>回收站</span></div>
    </div>
    <div class="set-h2" id="calMonthTotal">本月整理 0 张</div>
    <div class="cal-card">
      <div class="cal-head"><button id="calPrev">‹</button><b id="calTitle"></b><button id="calNext">›</button></div>
      <div class="cal-week"><span>一</span><span>二</span><span>三</span><span>四</span><span>五</span><span>六</span><span>日</span></div>
      <div id="calGrid" class="cal-grid"></div>
      <div class="cal-legend"><span></span>0<span class="l1"></span>1-2<span class="l2"></span>3-5<span class="l3"></span>6+</div>
    </div>
    <div class="set-h2">数据</div>
    <div class="set-group">
      <div class="set-row"><div class="tt"><div class="n">存储空间</div><div class="d">App 内照片视频占用 ${fmtBytes(tot)}</div></div></div>
      <div class="set-row" id="rowCache"><div class="tt"><div class="n">清理缓存</div><div class="d" id="cacheInfo">相册/缩略图缓存</div></div><span class="arrow">›</span></div>
      <div class="set-row" id="rowClean"><div class="tt"><div class="n">清理存储空间</div><div class="d">释放空间，整理记录/收藏/设置完整保留</div></div><span class="arrow">›</span></div>
    </div>
    <div class="set-h2">设置</div>
    <div class="set-group">
      <div class="set-row" id="rowTheme"><div class="tt"><div class="n">外观主题</div><div class="d" id="themeDesc">${themeDesc}</div></div>
        <div class="switch ${darkOn?'on':''}" id="swTheme"></div></div>
    </div>
    <div class="set-h2">关于</div>
    <div class="set-group">
      <div class="set-row" id="rowUpdate"><div class="tt"><div class="n">检查更新</div><div class="d">检测 GitHub 最新版本</div></div><span class="arrow">›</span></div>
      <div class="set-row" id="rowIgnore" style="display:none"><div class="tt"><div class="n">忽略的更新版本</div><div class="d" id="ignoreVerD">-</div></div><span class="arrow">清除</span></div>
      <div class="set-row"><div class="tt"><div class="n">PicaPhoto</div><div class="d">v${APP_VERSION} · 适配刘海屏 / OPPO·vivo·小米·华为相册</div></div></div>
    </div>`;
  $("#calPrev").addEventListener("click", ()=>{ calMonth--; if(calMonth<0){ calMonth=11; calYear--; } renderCalendar(); });
  $("#calNext").addEventListener("click", ()=>{ calMonth++; if(calMonth>11){ calMonth=0; calYear++; } renderCalendar(); });
  renderCalendar();
  /* 外观主题：点行弹出三选（跟随系统/浅色/深色）；点开关快速切换深/浅 */
  $("#rowTheme").addEventListener("click", ()=>{
    sheet([{ic:"🌗",t:"跟随系统",f:()=>{theme="auto";localStorage.setItem("pp_theme","auto");applyTheme();renderMe();}},
      {ic:"☀️",t:"浅色",f:()=>{theme="light";localStorage.setItem("pp_theme","light");applyTheme();renderMe();}},
      {ic:"🌙",t:"深色",f:()=>{theme="dark";localStorage.setItem("pp_theme","dark");applyTheme();renderMe();}}],"外观主题");
  });
  $("#swTheme").addEventListener("click", e=>{
    e.stopPropagation();
    const cur = currentTheme();
    theme = cur==="dark" ? "light" : "dark";
    localStorage.setItem("pp_theme", theme);
    applyTheme(); renderMe();
  });
  $("#rowClean").addEventListener("click", clearStorage);
  const ci=$("#cacheInfo");
  if(ci) ci.textContent="相册缓存 "+phoneAlbums.length+" 个 · 媒体缓存 "+phoneMediaCache.size+" 个";
  $("#rowCache").addEventListener("click", ()=>{
    clearPhoneMediaCache();
    refreshPhoneAlbums();
    toast("缓存已清理");
    renderMe();
  });
  $("#rowUpdate").addEventListener("click", ()=>checkUpdate(true));
  const ig=localStorage.getItem("pp_ignore_ver");
  if(ig){
    $("#rowIgnore").style.display="";
    $("#ignoreVerD").textContent="v"+ig+"（本次不再提示）";
    $("#rowIgnore").addEventListener("click", ()=>{ localStorage.removeItem("pp_ignore_ver"); toast("已清除忽略，下次将正常提示"); renderMe(); });
  }
  /* 统计数字滚动动画 */
  document.querySelectorAll("#view-me .stat b").forEach(el=>{
    const target=parseInt(el.textContent,10)||0;
    if(target<=0) return;
    const dur=520, t0=performance.now();
    const step=(t)=>{ const p=Math.min(1,(t-t0)/dur); el.textContent=Math.round(target*(0.5-0.5*Math.cos(Math.PI*p))); if(p<1) requestAnimationFrame(step); };
    requestAnimationFrame(step);
  });
  if(prevTop>0) requestAnimationFrame(()=>{ view.scrollTop = prevTop; });
}
async function clearStorage(){
  if(!confirm("确定清理 App 内的照片/视频？\n整理记录、收藏和设置会完整保留。")) return;
  await new Promise(r=>{ tx("media","readwrite").clear().onsuccess=r; });
  await new Promise(r=>{ tx("albums","readwrite").clear().onsuccess=r; });
  await new Promise(r=>{ tx("trash","readwrite").clear().onsuccess=r; });
  media=[]; albums=[]; appTrash=[]; trashList=[];
  urls.forEach(u=>URL.revokeObjectURL(u)); urls.clear();
  await refreshTrash();
  storageCache={t:0, bytes:0};
  toast("已清理，整理记录已保留");
  if(tab==="me") renderMe(); else saveState();
}

/* 照片网格点击委托（避免逐项绑定的性能开销） */
$("#photos").addEventListener("click", e=>{
  const ph=e.target.closest ? e.target.closest(".ph") : null;
  if(!ph || !ph.dataset.key) return;
  const key=ph.dataset.key;
  const items=visibleMedia();
  const idx=items.findIndex(m=>itemKey(m)===key);
  if(idx<0) return;
  if(multi){ toggleSel(key, ph); }
  else { openViewer(items, idx, "normal"); }
});

/* ============ 导航：整理 / 我的 ============ */
function goHome(){
  orgSub="home";
  exitMulti();
  showOrg();
}
function openTrashView(){ orgSub="trash"; showOrg(); }
function showOrg(){
  hideOrgViews();
  const v = orgSub==="photos" ? "view-photos" : (orgSub==="trash" ? "view-trash" : "view-home");
  $("#"+v).classList.add("active");
  if(orgSub==="home"){ renderHome(); }
  if(orgSub==="photos"){ renderPhotos(); }
  if(orgSub==="trash"){ refreshTrash().then(renderTrash); }
  updateTitle();
  updateTopbar();
}
function hideOrgViews(){
  ["view-home","view-photos","view-trash"].forEach(id=>$("#"+id).classList.remove("active"));
}
function updateTopbar(){
  const inSub = orgSub!=="home" && tab==="org";
  $("#btn-back").style.display = inSub ? "" : "none";
  $("#btn-add").style.display = (tab==="me" || inSub) ? "none" : "";
}
function switchTab(t){
  tab = t;
  document.querySelectorAll(".tab").forEach(x=>x.classList.toggle("on", x.dataset.tab===t));
  if(t==="org"){
    $("#view-me").classList.remove("active");
    showOrg();
  } else {
    hideOrgViews();
    $("#view-me").classList.add("active");
    updateTitle();
    updateTopbar();
    renderMe();
  }
}
function refreshActiveView(){
  if(tab==="me"){ renderMe(); return; }
  if(orgSub==="home"){ renderHome(); }
  else if(orgSub==="photos"){ renderPhotos(true); }
  else if(orgSub==="trash"){ refreshTrash().then(renderTrash); }
}
document.querySelectorAll(".tab").forEach(t=>{ t.addEventListener("click", ()=>{ switchTab(t.dataset.tab); }); });
/* 左上角返回 / 右上角新建 */
$("#btn-back").addEventListener("click", ()=>{ if(tab==="org" && orgSub!=="home") goHome(); });
$("#btn-add").addEventListener("click", ()=>{
  if(tab==="me" || orgSub!=="home") return;
  if(!BRIDGE){ toast("请在 App 中使用"); return; }
  promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v); renderHome(); toast("已创建相册「"+v+"」"); } });
});
$("#trashCard").addEventListener("click", openTrashView);
$("#selDone").addEventListener("click", exitMulti);
$("#selMove").addEventListener("click", moveSelected);
$("#selDel").addEventListener("click", removeSelected);
function renderMultiAlbums(){
  const box=$("#multiAlbums");
  box.innerHTML="";
  const add=document.createElement("button"); add.className="mchip new"; add.textContent="＋ 新建相册";
  add.addEventListener("click", ()=>{ promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v, ()=>moveSelTo(v)); } }); });
  box.appendChild(add);
  albumTargets().forEach(a=>{
    const c=document.createElement("button"); c.className="mchip"; c.textContent="📁 "+a.name;
    c.addEventListener("click", ()=>{ moveSelTo(a.name); });
    box.appendChild(c);
  });
  box.classList.add("show");
}
function moveSelTo(name){
  const list=visibleMedia().filter(m=>selection.has(itemKey(m)));
  if(!list.length){ exitMulti(); return; }
  nativeMove(name, list);
}

/* ============ 安卓返回键：管理模式→弹层→查看器→上一级→退出 ============ */
window.__back = function(){
  try{
    if($("#viewer").classList.contains("open")){ closeViewer(); return true; }
    if($("#sheet").classList.contains("open")){ closeSheet(); return true; }
    if($("#dlg").classList.contains("open")){ $("#dlg").classList.remove("open"); return true; }
    if($("#updateDlg").classList.contains("open")){ $("#updateDlg").classList.remove("open"); return true; }
    if(multi){ exitMulti(); return true; }
    if(tab==="me"){ switchTab("org"); return true; }
    if(orgSub!=="home"){ goHome(); return true; }
    return false;
  }catch(e){ return false; }
};

/* ============ 自动更新 ============ */
function cmpVer(a,b){
  const pa=(a||"").split(".").map(Number), pb=(b||"").split(".").map(Number);
  for(let i=0;i<3;i++){ const x=pa[i]||0, y=pb[i]||0; if(x!==y) return x-y; }
  return 0;
}
let updateDismissed=null;
async function checkUpdate(force){
  try{
    const r=await fetch(GITHUB_API,{cache:"no-store"});
    if(!r.ok){ if(force) toast("检查更新失败"); return; }
    const rel=await r.json();
    const apks=(rel.assets||[]).filter(a=>/PicaPhoto_v\d+\.\d+\.\d+\.apk/i.test(a.name));
    apks.sort((a,b)=>{ const va=(a.name.match(/v(\d+\.\d+\.\d+)/i)||[])[1], vb=(b.name.match(/v(\d+\.\d+\.\d+)/i)||[])[1]; return cmpVer(vb,va); });
    const asset=apks[0];
    if(!asset){ if(force) toast("未找到安装包"); return; }
    const ver=(asset.name.match(/PicaPhoto_v(\d+\.\d+\.\d+)/i)||[])[1];
    if(!ver){ if(force) toast("版本信息异常"); return; }
    if(cmpVer(ver,APP_VERSION)<=0){ if(force) toast("已是最新版本 v"+APP_VERSION); return; }
    if(localStorage.getItem("pp_ignore_ver")===ver){ if(force) toast("已忽略该版本 v"+ver); return; }
    if(!force && updateDismissed===ver) return;
    updateDismissed=ver;
    $("#updVer").textContent="v"+ver+"（当前 v"+APP_VERSION+"）";
    $("#updLog").textContent=(rel.body||"暂无更新说明").trim();
    $("#updateDlg").classList.add("open");
    window._updUrl=asset.browser_download_url;
    window._updName=asset.name;
  }catch(e){ if(force) toast("检查更新失败，请检查网络"); }
}
$("#updNow").addEventListener("click", async ()=>{
  $("#updateDlg").classList.remove("open");
  let url=window._updUrl||"";
  if(!url) return;
  const name=window._updName||"";
  if(name && BRIDGE){
    // 优先用 GitHub Pages 镜像（国内更稳）；cors 探测失败回退官方下载
    const pages="https://yan16384.github.io/PicaPhoto/mobile/"+name;
    let mirrorOk=false;
    try{
      const r=await fetch(pages,{method:"HEAD",mode:"cors",cache:"no-store"});
      mirrorOk = r.ok;
    }catch(e){ mirrorOk=false; }
    if(mirrorOk) url=pages;
  }
  if(BRIDGE){ BRIDGE.downloadAndInstall(url); toast("正在下载新版本…"); }
  else { try{ window.open(url,"_blank"); }catch(e){ location.href=url; } }
});
$("#updIgnore").addEventListener("click", ()=>{
  const ver=(document.getElementById("updVer").textContent.match(/v(\d+\.\d+\.\d+)/)||[])[1];
  if(ver) localStorage.setItem("pp_ignore_ver", ver);
  $("#updateDlg").classList.remove("open");
  toast(ver ? "已忽略 v"+ver+"，本次更新不再提示" : "已忽略本次更新");
});

/* ============ 启动 ============ */
function saveState(){ refreshActiveView(); }
async function init(){
  try{ await openDB(); }catch(e){ toast("存储不可用"); }
  media=await storeGetAll("media");
  albums=await storeGetAll("albums");
  await loadStats();
  await refreshTrash();
  refreshPhoneAlbums();
  applyTheme();
  const d=new Date(); calYear=d.getFullYear(); calMonth=d.getMonth();
  showOrg();
  renderMe();
  if(!BRIDGE && navigator.serviceWorker){ navigator.serviceWorker.register("sw.js").catch(()=>{}); }
  window.addEventListener("online", ()=>toast("已联网"));
  checkUpdate(false);   // 打开自动检测新版本
}
init();
