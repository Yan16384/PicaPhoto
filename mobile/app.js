"use strict";
/* ============ PicaPhoto 移动版 · Performance V2 ============ */
/* 原生桥接 */
const BRIDGE = (typeof window !== "undefined" && window.Android) || null;
const APP_VERSION = (BRIDGE && BRIDGE.getAppVersion && BRIDGE.getAppVersion()) || "2.0.5";
const GITHUB_API = "https://api.github.com/repos/Yan16384/PicaPhoto/releases/latest";
let phoneAlbums = [];
let phoneAlbum = null;        // 当前浏览的手机相册 bucket id
let phoneMedia = [];          // 当前手机相册媒体

/* ============ 数据层（IndexedDB v5：media / albums / trash / stats / phonecache / thumbcache） ============ */
const DB_NAME = "picaphoto";
let db = null;
function openDB(){
  return new Promise((res,rej)=>{
    const rq = indexedDB.open(DB_NAME, 5);
    rq.onupgradeneeded = e => {
      const d = e.target.result;
      if(!d.objectStoreNames.contains("media")) d.createObjectStore("media", {keyPath:"id"});
      if(!d.objectStoreNames.contains("albums")) d.createObjectStore("albums", {keyPath:"id"});
      if(!d.objectStoreNames.contains("trash")) d.createObjectStore("trash", {keyPath:"id"});
      if(!d.objectStoreNames.contains("stats")) d.createObjectStore("stats", {keyPath:"key"});
      if(!d.objectStoreNames.contains("phonecache")) d.createObjectStore("phonecache", {keyPath:"albumId"});
      if(!d.objectStoreNames.contains("thumbcache")) d.createObjectStore("thumbcache", {keyPath:"uri"});
    };
    rq.onsuccess = e => { db = e.target.result; res(db); };
    rq.onerror = () => rej(rq.error);
  });
}
function tx(store, mode){ return db.transaction(store, mode).objectStore(store); }
function storeGetAll(store){ return new Promise(r => { const q = tx(store).getAll(); q.onsuccess = () => r(q.result||[]); q.onerror = () => r([]); }); }
function storePut(store, obj){ return new Promise(r => { const q = tx(store,"readwrite").put(obj); q.onsuccess = () => r(true); q.onerror = () => r(false); }); }
function storePutAll(store, objs){
  return new Promise(r=>{
    if(!objs.length){ r(true); return; }
    try{
      const tr=db.transaction(store,"readwrite"), os=tr.objectStore(store);
      objs.forEach(o=>os.put(o));
      tr.oncomplete=()=>r(true);
      tr.onerror=tr.onabort=()=>r(false);
    }catch(e){ r(false); }
  });
}
function storeDel(store, id){ return new Promise(r => { const q = tx(store,"readwrite").delete(id); q.onsuccess = () => r(true); q.onerror = () => r(false); }); }
function storeDelAll(store, ids){
  return new Promise(r=>{
    if(!ids.length){ r(true); return; }
    try{
      const tr=db.transaction(store,"readwrite"), os=tr.objectStore(store);
      ids.forEach(id=>os.delete(id));
      tr.oncomplete=()=>r(true);
      tr.onerror=tr.onabort=()=>r(false);
    }catch(e){ r(false); }
  });
}

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
let trashUndoStack = [];
let moveUndoStack = [];
let favs = new Set(JSON.parse(localStorage.getItem("pp_favs")||"[]"));
let reviewed = new Set(JSON.parse(localStorage.getItem("pp_reviewed")||"[]"));
let stats = { organizedTotal:0, organizedByDay:{}, trashTotal:0, restoreTotal:0, startDate:null };
let calYear, calMonth;
let statsDirty = 0, statsTimer = null;
let storageCache = { t:0, bytes:0 };
let gridCols = (parseInt(localStorage.getItem("pp_grid_cols")||"3",10)||3);
gridCols = Math.max(2, Math.min(6, gridCols));
let vworkPos = "bottom";
let queueOrder = localStorage.getItem("pp_queue_order")||"new";
let mediaFilter = localStorage.getItem("pp_media_filter")||"all";
let writeBatchKey = "";
function applyVWork(){ const v=$("#viewer"); if(v) v.dataset.vwork=vworkPos; }

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
  markReviewed(m);
  updateViewerChrome();
}
function markReviewed(m){
  const key=itemKey(m);
  if(!key || reviewed.has(key)) return;
  reviewed.add(key);
  try{ localStorage.setItem("pp_reviewed", JSON.stringify([...reviewed])); }catch(e){}
}
function toggleReviewed(m){
  const key=itemKey(m); if(!key) return;
  if(reviewed.has(key)) reviewed.delete(key); else reviewed.add(key);
  try{ localStorage.setItem("pp_reviewed", JSON.stringify([...reviewed])); }catch(e){}
  updateViewerChrome();
}
function vibrate(ms){ try{ navigator.vibrate && navigator.vibrate(ms||15); }catch(e){} }

/* 每个原生异步请求使用唯一回调，避免快速切换相册时全局 callback 被覆盖 */
let nativeCbSeq=0;
function nativeCallback(prefix, handler){
  const name="__pp_"+prefix+"_"+(++nativeCbSeq);
  window[name]=payload=>{
    try{ handler(payload); }
    finally{
      try{ delete window[name]; }catch(e){ window[name]=undefined; }
    }
  };
  return name;
}
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
const PHONE_CACHE_TTL = 30*24*3600*1000; // generation 不可用时的兼容兜底
const PHONE_CACHE_MAX = 32;               // 只保留最近使用的相册，避免内存无限增长
let albumsRefreshInFlight=false;
let albumOpenSeq=0;
let phoneAlbumLoading=false;
let mediaTokenCache={t:0,v:""};
const PHONE_PAGE_SIZE=120;
const PHONE_ALL_PAGE_SIZE=400;
let phonePageState=new Map(); // albumId -> {nextOffset,hasMore,loading,complete,token}

function mediaStoreToken(force){
  const now=Date.now();
  if(!force && mediaTokenCache.v && now-mediaTokenCache.t<1000) return mediaTokenCache.v;
  let v="";
  try{
    const ver=BRIDGE && BRIDGE.getMediaStoreVersion ? String(BRIDGE.getMediaStoreVersion()||"") : "";
    const gen=BRIDGE && BRIDGE.getMediaStoreGeneration ? String(BRIDGE.getMediaStoreGeneration()||"") : "";
    v=ver+"|"+gen;
  }catch(e){}
  mediaTokenCache={t:now,v};
  return v;
}
function stripHeavyThumbs(items){
  /* content:// 媒体的缩略图路径不持久化：下次由原生根据 GENERATION_MODIFIED 校验磁盘缓存。 */
  return (items||[]).map(x=>{
    if(!x) return x;
    if(x.uri && String(x.uri).indexOf("content:")===0 && (x.thumb || x._b64)){
      const y=Object.assign({},x);
      delete y.thumb; delete y._b64;
      return y;
    }
    if(x._b64){ const y=Object.assign({},x); delete y._b64; return y; }
    return x;
  });
}
function putAlbumCache(id, items, token, state){
  if(!id || id==="unfiled" || !db) return;
  const clean=stripHeavyThumbs(items);
  const st=state||phonePageState.get(id)||{};
  try{
    db.transaction("phonecache","readwrite").objectStore("phonecache")
      .put({albumId:id,items:clean,t:Date.now(),mediaToken:token||mediaStoreToken(),
            nextOffset:st.nextOffset!=null?st.nextOffset:clean.length,
            beforeDate:st.beforeDate!=null?st.beforeDate:-1,beforeId:st.beforeId!=null?st.beforeId:-1,
            hasMore:!!st.hasMore,complete:st.complete===true});
  }catch(e){}
}
function rememberAlbum(id, items, token, state){
  const clean=stripHeavyThumbs(items);
  const st=state||{};
  phoneMediaCache.set(id,{t:Date.now(),token:token||mediaStoreToken(),items:clean,
                          nextOffset:st.nextOffset!=null?st.nextOffset:clean.length,
                          beforeDate:st.beforeDate!=null?st.beforeDate:-1,beforeId:st.beforeId!=null?st.beforeId:-1,
                          hasMore:!!st.hasMore,complete:st.complete===true});
  phonePageState.set(id,{nextOffset:st.nextOffset!=null?st.nextOffset:clean.length,
                         beforeDate:st.beforeDate!=null?st.beforeDate:-1,beforeId:st.beforeId!=null?st.beforeId:-1,
                         hasMore:!!st.hasMore,complete:st.complete===true,
                         loading:false,token:token||mediaStoreToken()});
  if(phoneMediaCache.size>PHONE_CACHE_MAX){
    let oldest=null;
    for(const [k,v] of phoneMediaCache){
      if(k===phoneAlbum) continue;
      if(!oldest || v.t<oldest.v.t) oldest={k,v};
    }
    if(oldest) phoneMediaCache.delete(oldest.k);
  }
}
function removeUrisFromCachedAlbum(id, uris){
  if(!id || id==="unfiled") return;
  const set=uris instanceof Set ? uris : new Set(uris||[]);
  const c=phoneMediaCache.get(id);
  if(c){
    const before=(c.items||[]).length;
    c.items=(c.items||[]).filter(x=>!set.has(x.uri));
    const removedCount=before-c.items.length;
    c.t=Date.now(); c.token=mediaStoreToken();
    const st=phonePageState.get(id)||{nextOffset:before,beforeDate:c.beforeDate!=null?c.beforeDate:-1,beforeId:c.beforeId!=null?c.beforeId:-1,hasMore:!!c.hasMore,complete:!!c.complete};
    st.nextOffset=Math.max(0,(st.nextOffset||0)-removedCount);
    phonePageState.set(id,st);
    putAlbumCache(id,c.items,c.token,st);
    return;
  }
  if(!db) return;
  try{
    const q=db.transaction("phonecache").objectStore("phonecache").get(id);
    q.onsuccess=()=>{
      const row=q.result;
      if(!row || !row.items) return;
      const items=row.items.filter(x=>!set.has(x.uri));
      const st={nextOffset:Math.max(0,(row.nextOffset!=null?row.nextOffset:row.items.length)-set.size),
                beforeDate:row.beforeDate!=null?row.beforeDate:-1,beforeId:row.beforeId!=null?row.beforeId:-1,
                hasMore:!!row.hasMore,complete:row.complete===true};
      putAlbumCache(id,items,mediaStoreToken(),st);
    };
  }catch(e){}
}
function invalidateAlbumCache(id){
  if(!id) return;
  phoneMediaCache.delete(id);
  phonePageState.delete(id);
  if(id!=="unfiled" && db){
    try{ db.transaction("phonecache","readwrite").objectStore("phonecache").delete(id); }catch(e){}
  }
}
function adjustAlbumCounts(){
  /* 相册计数 = 系统原始数 - 已在回收站（App 内软删除）的照片数；基于 rawCount 不重复减 */
  try{
    const recycled={};
    phoneTrash.forEach(t=>{ if(t.albumId) recycled[t.albumId]=(recycled[t.albumId]||0)+1; });
    phoneAlbums.forEach(a=>{
      const raw = (a.rawCount != null ? a.rawCount : a.count) || 0;
      a.rawCount = raw;
      a.count = recycled[a.id] ? Math.max(0, raw-recycled[a.id]) : raw;
    });
  }catch(e){}
}
function applyAlbumsResult(albums, token){
  phoneAlbums=Array.isArray(albums)?albums:[];
  phoneAlbums.forEach(a=>{ a.rawCount = a.count; });
  adjustAlbumCounts();
  try{ localStorage.setItem("pp_albums_cache", JSON.stringify({t:Date.now(), token:token||mediaStoreToken(), albums:phoneAlbums})); }catch(e){}
  const ids=new Set(phoneAlbums.map(a=>a.id));
  for(const key of [...phoneMediaCache.keys()]){
    if(key!=="unfiled" && !ids.has(key)) phoneMediaCache.delete(key);
  }
}
function refreshPhoneAlbums(force){
  if(!BRIDGE) return;
  try{
    if(!BRIDGE.hasPermission || !BRIDGE.hasPermission()){ phoneAlbums=[]; return; }

    let cached=null;
    try{
      const raw=localStorage.getItem("pp_albums_cache");
      if(raw) cached=JSON.parse(raw);
    }catch(e){}

    if(cached && cached.albums && Array.isArray(cached.albums) && !phoneAlbums.length){
      phoneAlbums=cached.albums;
      adjustAlbumCounts();
    }

    const token=mediaStoreToken(force);
    if(!force && cached && cached.albums && cached.token && token && cached.token===token){
      phoneAlbums=cached.albums;
      adjustAlbumCounts();
      return;
    }
    if(!force && cached && cached.albums && !token && Date.now()-(cached.t||0)<PHONE_CACHE_TTL){
      phoneAlbums=cached.albums;
      adjustAlbumCounts();
      return;
    }
    if(albumsRefreshInFlight) return;

    const applyJson=json=>{
      albumsRefreshInFlight=false;
      let arr=[];
      try{ arr=JSON.parse(json||"[]"); }catch(e){}
      applyAlbumsResult(arr, mediaStoreToken(true));
      if(tab==="org" && orgSub==="home") renderHome();
    };

    if(BRIDGE.readAlbumsAsync){
      albumsRefreshInFlight=true;
      const cbName=nativeCallback("albums", applyJson);
      BRIDGE.readAlbumsAsync(cbName);
      return;
    }

    /* 旧桥接兼容：仅没有异步接口时才走同步查询 */
    applyJson(BRIDGE.readAlbums());
  }catch(e){
    albumsRefreshInFlight=false;
    if(!phoneAlbums.length) phoneAlbums=[];
  }
}
function filterPhoneItems(items){
  return (items||[]).filter(x=>!trashedUris.has(x.uri) && !pendingMoves.has(x.uri));
}
function sortPhoneItems(arr){
  return (arr||[]).slice().sort((a,b)=>((b.dateAdded||0)-(a.dateAdded||0)) || String(b.uri||"").localeCompare(String(a.uri||"")));
}
function parseMediaPage(json,fallbackOffset){
  try{
    const o=JSON.parse(json||"{}");
    if(Array.isArray(o)) return {items:o,nextOffset:(fallbackOffset||0)+o.length,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1};
    return {items:Array.isArray(o.items)?o.items:[],nextOffset:o.nextOffset!=null?o.nextOffset:(fallbackOffset||0),
            hasMore:!!o.hasMore,nextBeforeDate:o.nextBeforeDate!=null?o.nextBeforeDate:-1,
            nextBeforeId:o.nextBeforeId!=null?o.nextBeforeId:-1,mediaToken:o.mediaToken||""};
  }catch(e){ return {items:[],nextOffset:fallbackOffset||0,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1}; }
}
function fetchPhonePage(id,state,limit,done){
  const st=state||{},offset=st.nextOffset||0;
  if(!BRIDGE){ done({items:[],nextOffset:offset,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1}); return; }
  if(BRIDGE.readMediaPageAfterAsync){
    const bd=st.beforeDate!=null?st.beforeDate:-1,bi=st.beforeId!=null?st.beforeId:-1;
    const cbName=nativeCallback("page",json=>done(parseMediaPage(json,offset)));
    BRIDGE.readMediaPageAfterAsync(id,bd,bi,limit,cbName);
    return;
  }
  if(BRIDGE.readMediaPageAsync){
    const cbName=nativeCallback("page",json=>done(parseMediaPage(json,offset)));
    BRIDGE.readMediaPageAsync(id,offset,limit,cbName);
    return;
  }
  /* 旧桥接只能全量读取，保持兼容。 */
  if(BRIDGE.readMediaAsync){
    const cbName=nativeCallback("media",json=>{
      let items=[]; try{ items=JSON.parse(json||"[]"); }catch(e){}
      done({items:sortPhoneItems(items),nextOffset:items.length,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1});
    });
    BRIDGE.readMediaAsync(id,cbName);
    return;
  }
  done({items:[],nextOffset:offset,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1});
}
function fetchUnfiledPage(state,limit,done){
  const st=state||{},offset=st.nextOffset||0;
  if(!BRIDGE){ done({items:[],nextOffset:offset,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1}); return; }
  if(BRIDGE.readUnfiledPageAfterAsync){
    const bd=st.beforeDate!=null?st.beforeDate:-1,bi=st.beforeId!=null?st.beforeId:-1;
    const cbName=nativeCallback("unfiledpage",json=>done(parseMediaPage(json,offset)));
    BRIDGE.readUnfiledPageAfterAsync(JSON.stringify([...hiddenAlbums]),bd,bi,limit,cbName);
    return;
  }
  if(BRIDGE.readUnfiledAsync){
    const cbName=nativeCallback("unfiled",json=>{
      let items=[]; try{ items=JSON.parse(json||"[]"); }catch(e){}
      done({items:sortPhoneItems(items),nextOffset:items.length,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1});
    });
    BRIDGE.readUnfiledAsync(JSON.stringify([...hiddenAlbums]),cbName);
    return;
  }
  done({items:[],nextOffset:offset,hasMore:false,nextBeforeDate:-1,nextBeforeId:-1});
}
function readPhoneMedia(id, cb){
  const currentToken=mediaStoreToken();

  if(id==="unfiled"){
    const mem=phoneMediaCache.get("unfiled"),currentToken2=currentToken;
    const refreshFirst=silent=>{
      const st=phonePageState.get("unfiled")||{};
      if(st.loading) return;
      st.loading=true; phonePageState.set("unfiled",st);
      fetchUnfiledPage({nextOffset:0,beforeDate:-1,beforeId:-1},PHONE_PAGE_SIZE,page=>{
        const token=page.mediaToken||mediaStoreToken(true);
        const state={nextOffset:page.nextOffset!=null?page.nextOffset:page.items.length,
                     beforeDate:page.nextBeforeDate!=null?page.nextBeforeDate:-1,beforeId:page.nextBeforeId!=null?page.nextBeforeId:-1,
                     hasMore:!!page.hasMore,complete:!page.hasMore,loading:false,token};
        const items=sortPhoneItems(stripHeavyThumbs(page.items));
        rememberAlbum("unfiled",items,token,state);
        unfiledTotal=state.complete?filterPhoneItems(items).length:0;
        if(!silent) cb&&cb(filterPhoneItems(items));
        else if(phoneAlbum==="unfiled"&&tab==="org"&&orgSub==="photos"){
          phoneMedia=filterPhoneItems(items); markPhDirty(); renderPhotos(true);
        }
      });
    };
    if(mem&&mem.items&&mem.items.length){
      const state={nextOffset:mem.nextOffset!=null?mem.nextOffset:mem.items.length,
                   beforeDate:mem.beforeDate!=null?mem.beforeDate:-1,beforeId:mem.beforeId!=null?mem.beforeId:-1,
                   hasMore:!!mem.hasMore,complete:mem.complete===true,loading:false,token:mem.token||""};
      phonePageState.set("unfiled",state);
      cb&&cb(filterPhoneItems(mem.items));
      const stale=currentToken2?(!mem.token||currentToken2!==mem.token):(Date.now()-(mem.t||0)>120000);
      if(stale) refreshFirst(true);
      return;
    }
    refreshFirst(false);
    return;
  }

  const deliver=(items,token,state)=>{
    items=sortPhoneItems(stripHeavyThumbs(items));
    rememberAlbum(id,items,token||mediaStoreToken(),state);
    cb && cb(filterPhoneItems(items));
  };
  const refreshFirst=silent=>{
    const st=phonePageState.get(id)||{};
    if(st.loading) return;
    st.loading=true; phonePageState.set(id,st);
    fetchPhonePage(id,{nextOffset:0,beforeDate:-1,beforeId:-1},PHONE_PAGE_SIZE,page=>{
      const token=page.mediaToken||mediaStoreToken(true);
      const state={nextOffset:page.nextOffset!=null?page.nextOffset:page.items.length,
                   beforeDate:page.nextBeforeDate!=null?page.nextBeforeDate:-1,beforeId:page.nextBeforeId!=null?page.nextBeforeId:-1,
                   hasMore:!!page.hasMore,complete:!page.hasMore,loading:false,token};
      phonePageState.set(id,state);
      const items=sortPhoneItems(stripHeavyThumbs(page.items));
      rememberAlbum(id,items,token,state);
      putAlbumCache(id,items,token,state);
      if(!silent) cb && cb(filterPhoneItems(items));
      else if(phoneAlbum===id && tab==="org" && orgSub==="photos"){
        phoneMedia=filterPhoneItems(items);
        markPhDirty();
        renderPhotos(true);
      }
    });
  };

  const mem=phoneMediaCache.get(id);
  if(mem && mem.items && mem.items.length){
    const state={nextOffset:mem.nextOffset!=null?mem.nextOffset:mem.items.length,
                 beforeDate:mem.beforeDate!=null?mem.beforeDate:-1,beforeId:mem.beforeId!=null?mem.beforeId:-1,
                 hasMore:!!mem.hasMore,complete:mem.complete===true,loading:false,token:mem.token||""};
    phonePageState.set(id,state);
    cb && cb(filterPhoneItems(mem.items));
    const stale=currentToken ? (!mem.token || currentToken!==mem.token)
                             : (Date.now()-(mem.t||0)>PHONE_CACHE_TTL);
    if(stale) refreshFirst(true);
    return;
  }

  if(!db){ refreshFirst(false); return; }
  try{
    const q=db.transaction("phonecache").objectStore("phonecache").get(id);
    q.onsuccess=()=>{
      const row=q.result;
      if(row && row.items && row.items.length){
        const state={nextOffset:row.nextOffset!=null?row.nextOffset:row.items.length,
                     beforeDate:row.beforeDate!=null?row.beforeDate:-1,beforeId:row.beforeId!=null?row.beforeId:-1,
                     hasMore:row.hasMore===true,complete:row.complete===true,loading:false,token:row.mediaToken||""};
        deliver(row.items,row.mediaToken||"",state);
        const stale=currentToken ? (!row.mediaToken || currentToken!==row.mediaToken)
                                 : (Date.now()-(row.t||0)>PHONE_CACHE_TTL);
        if(stale) refreshFirst(true);
      }else refreshFirst(false);
    };
    q.onerror=()=>refreshFirst(false);
  }catch(e){ refreshFirst(false); }
}
function loadMorePhoneMedia(done){
  const id=phoneAlbum;
  if(!id || phoneAlbumLoading){ if(done) done(0); return; }
  const st=phonePageState.get(id);
  if(!st || !st.hasMore || st.loading){ if(done) done(0); return; }
  st.loading=true; phonePageState.set(id,st);
  const seq=albumOpenSeq, offset=st.nextOffset||phoneMedia.length;
  const pageFetch=id==="unfiled"?fetchUnfiledPage:(state,limit,cb)=>fetchPhonePage(id,state,limit,cb);
  pageFetch(st,PHONE_PAGE_SIZE,page=>{
    const cur=phonePageState.get(id)||st;
    cur.loading=false;
    if(seq!==albumOpenSeq || phoneAlbum!==id){ phonePageState.set(id,cur); if(done) done(0); return; }
    const existing=new Set(phoneMedia.map(x=>x.uri));
    const add=filterPhoneItems(stripHeavyThumbs(page.items)).filter(x=>!existing.has(x.uri));
    if(add.length) phoneMedia.push(...add);
    /* keyset/cursor pagination: native nextOffset is page-local; JS keeps a cumulative count for cache metadata/fallbacks. */
    cur.nextOffset=offset+(page.items||[]).length;
    cur.beforeDate=page.nextBeforeDate!=null?page.nextBeforeDate:-1;
    cur.beforeId=page.nextBeforeId!=null?page.nextBeforeId:-1;
    cur.hasMore=!!page.hasMore && cur.beforeDate>=0 && cur.beforeId>=0;
    cur.complete=!cur.hasMore;
    cur.token=page.mediaToken||mediaStoreToken(true);
    phonePageState.set(id,cur);
    rememberAlbum(id,phoneMedia,cur.token,cur);
    putAlbumCache(id,phoneMedia,cur.token,cur);
    if(id==="unfiled" && cur.complete) unfiledTotal=phoneMedia.length;
    appendPhonePageToGrid();
    if(done) done(add.length);
  });
}
function readPhoneMediaAll(id,cb){
  const canPage=id==="unfiled" ? (BRIDGE&&BRIDGE.readUnfiledPageAfterAsync)
                                  : (BRIDGE&&(BRIDGE.readMediaPageAfterAsync||BRIDGE.readMediaPageAsync));
  if(!canPage){ readPhoneMedia(id,cb); return; }
  const all=[]; let guard=0;
  const next=state=>{
    if(guard++>10000){ cb&&cb(filterPhoneItems(sortPhoneItems(all))); return; }
    const fetcher=id==="unfiled"?fetchUnfiledPage:(st,limit,done)=>fetchPhonePage(id,st,limit,done);
    fetcher(state,PHONE_ALL_PAGE_SIZE,page=>{
      all.push(...(page.items||[]));
      const ns={nextOffset:(state.nextOffset||0)+(page.items||[]).length,
                beforeDate:page.nextBeforeDate!=null?page.nextBeforeDate:-1,beforeId:page.nextBeforeId!=null?page.nextBeforeId:-1};
      if(page.hasMore&&ns.beforeDate>=0&&ns.beforeId>=0) next(ns);
      else cb&&cb(filterPhoneItems(sortPhoneItems(all)));
    });
  };
  next({nextOffset:0,beforeDate:-1,beforeId:-1});
}
function clearPhoneMediaCache(id){
  if(id){
    invalidateAlbumCache(id);
  } else {
    phoneMediaCache.clear();
    phonePageState.clear();
    try{ if(db) db.transaction("phonecache","readwrite").objectStore("phonecache").clear(); }catch(e){}
    /* 清理旧版本遗留的 Base64 thumbcache；V2 缩略图本体由原生磁盘 LRU 管理。 */
    try{ if(db) db.transaction("thumbcache","readwrite").objectStore("thumbcache").clear(); }catch(e){}
    try{ if(BRIDGE && BRIDGE.clearThumbCache) BRIDGE.clearThumbCache(); }catch(e){}
    try{ localStorage.removeItem("pp_albums_cache"); }catch(e){}
  }
}
function requestPhonePermission(){
  if(!BRIDGE) return;
  BRIDGE.requestPermission();
  toast("请在系统弹窗中允许访问照片");
}
window.__permissionChanged=()=>{
  mediaTokenCache={t:0,v:""};
  refreshPhoneAlbums(true);
  if(tab==="org" && orgSub==="home") renderHome();
};
window.__mediaManageChanged=()=>{
  writeBatchKey="";
  if(tab==="org" && orgSub==="home") renderHome();
  if(tab==="me") renderMe();
};
function canManageMedia(){ try{return !!(BRIDGE&&BRIDGE.canManageMedia&&BRIDGE.canManageMedia());}catch(e){return false;} }
function requestFullPhotoAccess(){
  if(!BRIDGE||!BRIDGE.requestManageMedia) return;
  BRIDGE.requestManageMedia();
}
function requestWriteBatch(items){
  if(!BRIDGE||!BRIDGE.requestWriteBatch||!Array.isArray(items)) return;
  const uris=[...new Set(items.map(m=>m&&m.uri).filter(u=>u&&u.startsWith("content:")))].slice(0,1000);
  if(!uris.length) return;
  const key=uris.length+":"+uris[0]+":"+uris[uris.length-1];
  if(writeBatchKey===key) return;
  const cb=nativeCallback("writebatch",raw=>{ if(String(raw)==="true") writeBatchKey=key; });
  try{ BRIDGE.requestWriteBatch(JSON.stringify(uris),cb); }catch(e){}
}
function openPhoneAlbum(id, name){
  const seq=++albumOpenSeq;
  stopPhotoBackgroundWork();
  phGridAlbum=null; phItems=[]; phItemMap=new Map(); phLayoutGroups=[]; phGroupByStart=new Map(); phTotalHeight=0; phWindowStart=phWindowEnd=-1; phEls=new Map();
  phoneAlbum = id; currentAlbum = null; orgSub = "photos";
  try{ localStorage.setItem("pp_resume_album", JSON.stringify({id:id,name:name||"手机相册"})); }catch(e){}
  exitMulti();
  phoneMedia = [];
  try{ const v=document.getElementById("view-photos"); if(v) v.scrollTop=0; }catch(e){}

  const c=phoneMediaCache.get(id);
  if(c && c.items){
    phoneAlbumLoading=false;
    phoneMedia=c.items.filter(x=>!trashedUris.has(x.uri) && !pendingMoves.has(x.uri));
    if(id==="unfiled") unfiledTotal=(c.complete===true)?phoneMedia.length:0;
  } else {
    phoneAlbumLoading=true;
    let sk="";
    for(let i=0;i<18;i++) sk+='<div class="ph skel"></div>';
    $("#photos").className="ph-grid";
    $("#photos").innerHTML = sk;
    applyGridCols(false);
  }
  showOrg();
  readPhoneMedia(id, items=>{
    if(seq!==albumOpenSeq || phoneAlbum!==id) return;
    phoneAlbumLoading=false;
    phoneMedia = items;
    if(id==="unfiled"){
      const st=phonePageState.get("unfiled");
      unfiledTotal=(st&&st.complete)?items.length:0;
    }
    renderPhotos();
    if(queueOrder!=="new"){
      readPhoneMediaAll(id,all=>{
        if(seq!==albumOpenSeq||phoneAlbum!==id) return;
        phoneMedia=all;
        rememberAlbum(id,all,mediaStoreToken(true),{nextOffset:all.length,hasMore:false,complete:true});
        renderPhotos(true);
      });
    }
  });
}
function exitPhoneMode(){
  ++albumOpenSeq;
  stopPhotoBackgroundWork();
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
  /* move-target albums: all phone albums EXCEPT hidden ones + created */
  const map=new Map();
  phoneAlbums.forEach(a=>{ if(!hiddenAlbums.has(a.id)) map.set(a.name, a); });
  createdAlbums().forEach(n=>{ if(!map.has(n)) map.set(n,{name:n}); });
  return [...map.values()];
}
function recentAlbumNames(){ try{return JSON.parse(localStorage.getItem("pp_recent_albums")||"[]");}catch(e){return [];} }
function rememberRecentAlbum(name){
  const items=recentAlbumNames().filter(x=>x!==name); items.unshift(name);
  try{ localStorage.setItem("pp_recent_albums",JSON.stringify(items.slice(0,8))); }catch(e){}
}
function albumPicker(title, onPick){
  const all=albumTargets(); const recent=new Set(recentAlbumNames());
  const render=q=>{
    const key=(q||"").trim().toLowerCase();
    const filtered=all.filter(a=>!key||a.name.toLowerCase().includes(key));
    const sorted=filtered.slice().sort((a,b)=>(recent.has(b.name)?1:0)-(recent.has(a.name)?1:0)||a.name.localeCompare(b.name,"zh-CN"));
    const list=$("#sheetList"); list.innerHTML='';
    const input=document.createElement("input"); input.className="album-search"; input.placeholder="搜索相册"; input.value=q||"";
    input.addEventListener("input",()=>render(input.value)); list.appendChild(input);
    if(!key && recent.size){ const hint=document.createElement("div"); hint.className="sheet-label"; hint.textContent="最近使用"; list.appendChild(hint); }
    sorted.forEach(a=>{ const el=document.createElement("div"); el.className="opt"; el.innerHTML='<span class="ic">'+(recent.has(a.name)&&!key?'🕘':'📁')+'</span><span>'+escapeHtml(a.name)+'</span>'; el.addEventListener("click",()=>{closeSheet();onPick(a.name);}); list.appendChild(el); });
    const add=document.createElement("div"); add.className="opt"; add.innerHTML='<span class="ic">➕</span><span>新建相册…</span>'; add.addEventListener("click",()=>{closeSheet();promptInput("新建相册","",v=>{if(v){createSystemAlbum(v,()=>onPick(v));}});}); list.appendChild(add);
  };
  $("#sheetTitle").textContent=title||"选择相册"; $("#sheet").classList.add("open"); render("");
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
  const titleRow=h("手机相册");
  const hideBtn=document.createElement("button");
  hideBtn.className="hide-btn";
  hideBtn.textContent="隐藏相册"+(hiddenAlbums.size?(" · "+hiddenAlbums.size):"");
  hideBtn.addEventListener("click", manageHiddenAlbums);
  titleRow.appendChild(hideBtn);
  box.appendChild(titleRow);
  if(BRIDGE && BRIDGE.readUnfiledAsync){
    const uf=document.createElement("div"); uf.className="tool-card";
    uf.innerHTML='<div class="ic" style="background:#7b5cd6">📂</div><div class="tt"><div class="n">未整理</div><div class="d">'+(hiddenAlbums.size?('隐藏相册 '+hiddenAlbums.size+' 个 · '):'')+'没有相册归属的照片，点按移入相册</div></div><span class="arrow">›</span>';
    uf.addEventListener("click", ()=>{ openPhoneAlbum("unfiled","未整理",false); });
    box.appendChild(uf);
  }
  if(BRIDGE && !BRIDGE.hasPermission()){
    const p=document.createElement("div"); p.className="full empty";
    p.innerHTML='<div class="big">🖼️</div>需要权限才能读取手机相册<br><button class="big-btn" id="btnPerm">申请相册访问权限</button>';
    box.appendChild(p);
    p.querySelector("#btnPerm").addEventListener("click", requestPhonePermission);
  } else if(BRIDGE){
    if(BRIDGE.supportsManageMedia && BRIDGE.supportsManageMedia() && !canManageMedia()){
      const access=document.createElement("div"); access.className="tool-card";
      access.innerHTML='<div class="ic" style="background:#16a36a">🔐</div><div class="tt"><div class="n">申请相册访问权限</div><div class="d">开启一次后，整理照片不再逐张询问</div></div><span class="arrow">›</span>';
      access.addEventListener("click",requestFullPhotoAccess); box.appendChild(access);
    }
    const visibleAlbs = phoneAlbums.filter(a=>!hiddenAlbums.has(a.id));
    const g=document.createElement("div"); g.className="pgalb-grid";
    visibleAlbs.forEach((a,ai)=>{
      const c=document.createElement("div"); c.className="pgalb anim-pop";
      c.dataset.albumId=a.id;
      c.innerHTML='<div class="cover">'+(a.cover?'<img loading="lazy" decoding="async" src="'+a.cover+'" alt="">':'<div class="cover-ph">'+escapeHtml((a.name||"相").charAt(0))+'</div>')+'</div><div class="name">'+escapeHtml(a.name)+'</div><div class="cnt">'+a.count+' 项</div>';
      if(ai<12) c.style.animationDelay=(ai*18)+"ms"; else c.classList.remove("anim-pop");
      c.addEventListener("click", ()=>{ openPhoneAlbum(a.id, a.name, false); });
      bindLong(c, ()=>phoneAlbumMenu(a));
      g.appendChild(c);
    });
    box.appendChild(g);
    if(!visibleAlbs.length){
      const p=document.createElement("div"); p.className="full empty";
      p.innerHTML='<div class="big">📭</div>手机相册为空'+(hiddenAlbums.size?'<br><span style="font-size:13px">已隐藏 '+hiddenAlbums.size+' 个相册</span>':'<br><span style="font-size:13px">下拉可刷新</span>');
      box.appendChild(p);
    }
    /* 隐藏相册单独板块（最下方） */
    const hiddenAlbs = phoneAlbums.filter(a=>hiddenAlbums.has(a.id));
    if(hiddenAlbs.length){
      box.appendChild(h("隐藏相册 · 照片计入未整理"));
      const hg=document.createElement("div"); hg.className="pgalb-grid hide-alb-grid";
      hiddenAlbs.forEach(a=>{
        const c=document.createElement("div"); c.className="pgalb";
        c.innerHTML='<div class="cover">'+(a.cover?'<img loading="lazy" decoding="async" src="'+a.cover+'" alt="">':'<div class="cover-ph">'+escapeHtml((a.name||"相").charAt(0))+'</div>')+'</div><span class="hide-tag">隐藏</span><div class="name">'+escapeHtml(a.name)+'</div><div class="cnt">'+a.count+' 项</div>';
        c.addEventListener("click", ()=>{ openPhoneAlbum(a.id, a.name); });
        bindLong(c, ()=>phoneAlbumMenu(a));
        hg.appendChild(c);
      });
      box.appendChild(hg);
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
/* 隐藏相册管理：多选面板（勾选多个，点完成保存） */
function manageHiddenAlbums(){
  if(!phoneAlbums.length){ toast("暂无可管理的相册"); return; }
  const list=$("#hideList"); list.innerHTML="";
  phoneAlbums.forEach(a=>{
    const row=document.createElement("div");
    row.className="hide-row"+(hiddenAlbums.has(a.id)?" on":"");
    row.innerHTML='<span class="ck">'+(hiddenAlbums.has(a.id)?"✅":"⬜")+'</span><span class="nm">'+escapeHtml(a.name)+'</span>';
    row.addEventListener("click", ()=>{
      if(hiddenAlbums.has(a.id)) hiddenAlbums.delete(a.id); else hiddenAlbums.add(a.id);
      row.classList.toggle("on");
      row.querySelector(".ck").textContent = hiddenAlbums.has(a.id)?"✅":"⬜";
      $("#hideDone").textContent="完成 ("+hiddenAlbums.size+")";
    });
    list.appendChild(row);
  });
  $("#hideDone").textContent="完成 ("+hiddenAlbums.size+")";
  $("#hidePanel").classList.add("open");
}
/* 手机相册管理：重命名 / 删除空目录但保留照片 / 隐藏 */
function phoneAlbumMenu(a){
  const opts=[];
  opts.push({ic:"✏️",t:"重命名",f:()=>{
    promptInput("重命名相册", a.name, async v=>{ if(v && v.trim() && v.trim()!==a.name){ renameAlbum(a, v.trim()); } });
  }});
  opts.push({ic:"🗑️",t:"删除相册（保留照片）",f:()=>deleteAlbumKeepPhotos(a)});
  if(hiddenAlbums.has(a.id)){
    opts.push({ic:"👁️",t:"取消隐藏",f:()=>{hiddenAlbums.delete(a.id);saveHidden();renderHome();toast("已取消隐藏「"+a.name+"」");}});
  }else{
    opts.push({ic:"🙈",t:"隐藏相册",f:()=>{hiddenAlbums.add(a.id);saveHidden();renderHome();toast("已隐藏「"+a.name+"」");}});
  }
  sheet(opts,"管理相册");
}
function renameAlbum(a, newName){
  if(!BRIDGE || !BRIDGE.moveToAlbumAsync){ toast("该版本不支持重命名"); return; }
  readPhoneMediaAll(a.id, items=>{
    const uris=(items||[]).map(x=>x.uri).filter(Boolean);
    const finish=()=>{
      const list=createdAlbums(), i=list.indexOf(a.name);
      if(i>=0) list[i]=newName; else if(!list.includes(newName)) list.push(newName);
      localStorage.setItem("pp_created",JSON.stringify(list));
      hiddenAlbums.delete(a.id); saveHidden();
      try{ if(BRIDGE.deleteEmptyAlbum) BRIDGE.deleteEmptyAlbum(a.name); }catch(e){}
      invalidateAlbumCache(a.id); refreshPhoneAlbums(true); setTimeout(renderHome,300);
      toast("已重命名为「"+newName+"」");
    };
    if(!uris.length){ try{BRIDGE.createAlbum(newName);}catch(e){} finish(); return; }
    const cb=nativeCallback("rename",raw=>{
      let res=[]; try{res=JSON.parse(raw||"[]");}catch(e){}
      const ok=res.filter(x=>x.ok).length;
      if(ok!==uris.length){ toast("已移动 "+ok+" 项，"+(uris.length-ok)+" 项重命名失败"); return; }
      finish();
    });
    try{ BRIDGE.moveToAlbumAsync(newName,JSON.stringify(uris),cb); }catch(e){toast("重命名失败："+e);}
  });
}
let pendingDelAlbumName = null;
let pendingDelAlbumId = null;
function deleteAlbumKeepPhotos(a){
  if(!confirm("删除相册「"+a.name+"」？\n照片会保留并移到 Pictures 根目录。")) return;
  readPhoneMediaAll(a.id, items=>{
    const uris=(items||[]).map(x=>x.uri).filter(u=>u && !trashedUris.has(u));
    if(!uris.length){ removeCreated(a.name); hiddenAlbums.delete(a.id); saveHidden(); try{BRIDGE.deleteEmptyAlbum(a.name);}catch(e){} refreshPhoneAlbums(true);renderHome();return; }
    const cb=nativeCallback("deleteAlbumKeep",raw=>{
      let res=[];try{res=JSON.parse(raw||"[]");}catch(e){}
      const ok=res.filter(x=>x.ok).length;
      if(ok!==uris.length){toast("已保留并移出 "+ok+" 项，"+(uris.length-ok)+" 项未移动");return;}
      removeCreated(a.name); hiddenAlbums.delete(a.id); saveHidden();
      try{if(BRIDGE.deleteEmptyAlbum)BRIDGE.deleteEmptyAlbum(a.name);}catch(e){}
      invalidateAlbumCache(a.id); refreshPhoneAlbums(true); setTimeout(renderHome,300); toast("相册已删除，照片已保留");
    });
    BRIDGE.moveToPathAsync(JSON.stringify(uris),"Pictures/",cb);
  });
}
function openPhotosView(albumId){ currentAlbum=albumId; orgSub="photos"; exitMulti(); showOrg(); }
function visibleMedia(){
  const base=phoneAlbum!==null ? phoneMedia : (currentAlbum===null?media:media.filter(m=>m.album===currentAlbum));
  const filtered=base.filter(m=>mediaFilter==="all"||(mediaFilter==="video"?isVideo(m):!isVideo(m)));
  const stable=(m)=>String(m&&m.uri||m&&m.id||"");
  return filtered.slice().sort((a,b)=>{
    let d=0;
    if(queueOrder==="old") d=(a.dateAdded||a.addedAt||0)-(b.dateAdded||b.addedAt||0);
    else if(queueOrder==="size_desc") d=(b.size||0)-(a.size||0);
    else if(queueOrder==="size_asc") d=(a.size||0)-(b.size||0);
    else d=(b.dateAdded||b.addedAt||0)-(a.dateAdded||a.addedAt||0);
    return d||stable(a).localeCompare(stable(b));
  });
}
function setMediaSort(value){
  queueOrder=value; localStorage.setItem("pp_queue_order",value);
  if(tab==="me") renderMe(); else if(orgSub==="photos") renderPhotos(true);
}
function setMediaFilter(value){
  mediaFilter=value; localStorage.setItem("pp_media_filter",value);
  if(tab==="me") renderMe(); else if(orgSub==="photos") renderPhotos(true);
}

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
/* 照片网格手势：横向滑动无感进入管理模式并持续连选（第一次滑动即选中路径上的照片，无顿挫） */
(function(){
  const v=$("#view-photos");
let gsx=null, gsy=null, gpx=null, gpy=null, gActive=false, gMode=null, gToggled=null;
  const STEP=18;   // 沿手指路径密集采样间距，避免快速横滑漏选
  function tapCell(x, y){
    const el=document.elementFromPoint(x, y);
    const ph=el && el.closest ? el.closest(".ph") : null;
    if(!ph || !ph.dataset.key || !gToggled) return;
    const key=ph.dataset.key;
    if(gToggled.has(key)) return;
    gToggled.add(key);
    if(selection.has(key)){ selection.delete(key); ph.classList.remove("sel-on"); const b=ph.querySelector(".idx"); if(b) b.textContent=""; }
    else { selection.add(key); ph.classList.add("sel-on"); }
    refreshBadges();
  }
  v.addEventListener("touchstart", e=>{
    if(e.touches.length!==1){ gActive=false; gsx=null; gMode=null; return; }
    gsx=gpx=e.touches[0].clientX; gsy=gpy=e.touches[0].clientY; gActive=true; gMode=null; gToggled=new Set();
  },{passive:true});
  v.addEventListener("touchmove", e=>{
    if(!gActive || gpx===null || e.touches.length!==1) return;
    const cx=e.touches[0].clientX, cy=e.touches[0].clientY;
    const dx=cx-gsx, dy=cy-gsy;
    if(gMode===null && (Math.abs(dx)>20 || Math.abs(dy)>20)) gMode = Math.abs(dx)>Math.abs(dy) ? "h" : "v";
    if(gMode!=="h") return;
    e.preventDefault();
    if(!multi) enterMulti();
    /* 沿上一个触点到当前点的线段密集采样，一次滑动不漏选任何格子 */
    const dist=Math.hypot(cx-gpx, cy-gpy);
    const steps=Math.max(1, Math.round(dist/STEP));
    for(let s=1;s<=steps;s++){ tapCell(gpx+(cx-gpx)*s/steps, gpy+(cy-gpy)*s/steps); }
    gpx=cx; gpy=cy;
  },{passive:false});
  v.addEventListener("touchend", ()=>{ gActive=false; gsx=gpx=null; gsy=gpy=null; gMode=null; gToggled=null; },{passive:true});
  v.addEventListener("touchcancel", ()=>{ gActive=false; gsx=gpx=null; gsy=gpy=null; gMode=null; gToggled=null; },{passive:true});
})();
/* 小图网格：双指捏合调整排列（张开=变大最多横排2，合拢=变小最少横排6） */
(function(){
  const v=$("#view-photos");
  let pinch0=0, cols0=gridCols;
  v.addEventListener("touchstart", e=>{
    if(e.touches.length===2){ pinch0=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY); cols0=gridCols; }
  },{passive:true});
  v.addEventListener("touchmove", e=>{
    if(e.touches.length<2 || pinch0<=0) return;
    e.preventDefault();   // 阻止 WebView 默认双指缩放
    const d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
    let nc = cols0 - Math.round((d-pinch0)/70);
    nc = Math.max(2, Math.min(6, nc));
    if(nc!==gridCols){
      gridCols=nc;
      try{ localStorage.setItem("pp_grid_cols", String(gridCols)); }catch(e){}
      applyGridCols(false);   // 拖动中即时响应，不做动画（不卡）
      vibrate(8);
    }
  },{passive:false});
  v.addEventListener("touchend", ()=>{ if(pinch0>0) applyGridCols(true); pinch0=0; },{passive:true});
  v.addEventListener("touchcancel", ()=>{ if(pinch0>0) applyGridCols(true); pinch0=0; },{passive:true});
})();

/* ============ 照片网格 V2：分页 + 窗口化虚拟列表 + 原生磁盘缩略图 ============ */
let phEls=new Map();
let phItemMap=new Map();
let phItems=[];
let phRendered=0; // 兼容旧逻辑：表示当前窗口结束 index
let phDirty=false;
let phGridAlbum=null;
let phScrollBound=false;
let phScrollRaf=0;
let phWindowStart=-1, phWindowEnd=-1;
let phLayoutGroups=[];
let phGroupByStart=new Map();
let phTotalHeight=0;
let phExtraTopH=0;
let phCell=100;
const PH_MAX_DOM=360;
const PH_WINDOW_BLOCK=90;
const PH_OVERSCAN_ROWS=7;
const PH_MONTH_H=30;
/* 兼容旧变量：V2 不再执行全相册自动填充/Canvas Base64 预热。 */
let phWarmTimer=null, phFillTimer=null;

function monthLabelOf(m){
  const d=m&&m.dateAdded?new Date(m.dateAdded*1000):null;
  if(!d || isNaN(d.getTime())) return null;
  return d.getFullYear()+"年"+(d.getMonth()+1)+"月"+d.getDate()+"日";
}
const VP_PLACEHOLDER="data:image/svg+xml,"+encodeURIComponent('<svg xmlns="http://www.w3.org/2000/svg" width="240" height="240"><rect width="240" height="240" fill="#262a33"/><circle cx="120" cy="120" r="42" fill="rgba(255,255,255,.14)"/><path d="M104 96v48l40-24z" fill="#fff"/></svg>');
const IP_PLACEHOLDER="data:image/svg+xml,"+encodeURIComponent('<svg xmlns="http://www.w3.org/2000/svg" width="240" height="240"><rect width="240" height="240" fill="#e7e9ee"/><path d="M48 178l48-54 32 34 22-25 42 45H48z" fill="#c3c7d1"/><circle cx="158" cy="76" r="19" fill="#c3c7d1"/></svg>');
function imgSrcOf(m){
  if(m&&m.thumb) return m.thumb;
  if(m&&m.uri&&String(m.uri).indexOf("content:")===0) return isVideo(m)?VP_PLACEHOLDER:IP_PLACEHOLDER;
  return objURL(m);
}

/* 原生磁盘缩略图队列：JS 只保留 file:// 路径，不再存 Base64 thumbcache。 */
let thPending=new Map();
let thObserver=null;
let thQueue=[];
let thActive=0;
const TH_MAX_CONCURRENT=3;
window.__thumbCb=obj=>{
  thActive=Math.max(0,thActive-1);
  try{
    const r=JSON.parse(obj||"{}");
    if(r&&r.uri){
      const entry=thPending.get(r.uri);
      if(entry){
        if(r.thumb&&r.thumb!=="null"){
          entry.m.thumb=r.thumb;
          if(entry.img&&entry.img.isConnected) entry.img.src=r.thumb;
        }
        thPending.delete(r.uri);
      }
    }
  }catch(e){}
  drainThumbQueue();
};
function requestNativeThumb(job){
  if(!BRIDGE||!job) return false;
  if(BRIDGE.getMediaThumbV2Async){ BRIDGE.getMediaThumbV2Async(job.uri,job.version!=null?job.version:-1,"__thumbCb"); return true; }
  if(BRIDGE.getMediaThumbAsync){ BRIDGE.getMediaThumbAsync(job.uri,"__thumbCb"); return true; }
  if(BRIDGE.getVideoThumbAsync){ BRIDGE.getVideoThumbAsync(job.uri,"__thumbCb"); return true; }
  return false;
}
function drainThumbQueue(){
  while(thActive<TH_MAX_CONCURRENT&&thQueue.length){
    const job=thQueue.shift();
    if(!thPending.has(job.uri)) continue;
    thActive++;
    try{
      if(!requestNativeThumb(job)){
        thActive=Math.max(0,thActive-1);
        thPending.delete(job.uri);
      }
    }catch(e){
      thActive=Math.max(0,thActive-1);
      thPending.delete(job.uri);
    }
  }
}
function ensureMediaThumb(m,el){
  if(!m||!m.uri||m.thumb||thPending.has(m.uri)) return;
  const img=el?el.querySelector("img"):null;
  if(!img) return;
  thPending.set(m.uri,{m,img});
  thQueue.push({uri:m.uri,version:m.thumbVersion!=null?m.thumbVersion:-1});
  drainThumbQueue();
}
function setupThumbObserver(){
  if(thObserver) return;
  thObserver=new IntersectionObserver(entries=>{
    entries.forEach(en=>{
      if(!en.isIntersecting) return;
      const el=en.target,key=el.dataset.key;
      const m=phItemMap.get(key);
      if(m) ensureMediaThumb(m,el);
      try{ thObserver.unobserve(el); }catch(e){}
    });
  },{root:document.getElementById("view-photos")||null,rootMargin:"240px"});
}
function stopPhotoBackgroundWork(){
  if(phFillTimer){ clearTimeout(phFillTimer); phFillTimer=null; }
  if(phWarmTimer){ clearTimeout(phWarmTimer); phWarmTimer=null; }
  if(phScrollRaf){ cancelAnimationFrame(phScrollRaf); phScrollRaf=0; }
  if(thObserver) thObserver.disconnect();
  thQueue.length=0;
  thPending.clear();
}

function buildPhotoEl(m,idx,selNo){
  const key=itemKey(m),el=document.createElement("div");
  el.className="ph"; el.dataset.key=key;
  el.innerHTML='<img loading="lazy" decoding="async" alt=""><span class="idx"></span>'+(isVideo(m)?'<span class="dur">▶</span>':'');
  const im=el.querySelector("img");
  im.src=imgSrcOf(m);
  im.onerror=()=>{
    if(m&&m.uri&&String(m.uri).indexOf("content:")===0){
      m.thumb="";
      im.onerror=null;
      im.src=isVideo(m)?VP_PLACEHOLDER:IP_PLACEHOLDER;
      im.onerror=()=>{};
      ensureMediaThumb(m,el);
      return;
    }
    el.classList.add("flyout-up");
    setTimeout(()=>{ el.remove(); phEls.delete(key); },160);
  };
  if(multi){
    el.classList.add("multi");
    if(selection.has(key)){
      el.classList.add("sel-on");
      el.querySelector(".idx").textContent=selNo||"✓";
    }
  }
  if(idx<18){ el.classList.add("anim-pop"); el.style.animationDelay=(idx*10)+"ms"; }
  if(m&&m.uri&&String(m.uri).indexOf("content:")===0&&!m.thumb){
    setupThumbObserver(); thObserver.observe(el);
  }
  phEls.set(key,el);
  return el;
}
function itemsIndexOf(m){ return visibleMedia().indexOf(m); }

function applyGridCols(animate){
  const box=$("#photos");
  if(!box||box.className!=="ph-grid") return;
  box.style.gridTemplateColumns="repeat("+gridCols+",1fr)";
  /* 列数变化后重新计算虚拟高度；不再对几百/几千节点做 FLIP。 */
  requestAnimationFrame(()=>{
    rebuildVirtualLayout();
    renderVirtualWindow(true);
  });
}
function rebuildVirtualLayout(){
  const view=document.getElementById("view-photos");
  const cols=Math.max(2,gridCols||3);
  phCell=view?Math.max(64,view.clientWidth/cols):100;
  phLayoutGroups=[]; phGroupByStart=new Map();
  phExtraTopH=(phoneAlbum==="unfiled"&&unfiledTotal>0)?44:0;
  phTotalHeight=phExtraTopH;
  if(!phItems.length) return;
  let start=0,label=monthLabelOf(phItems[0]);
  for(let i=1;i<=phItems.length;i++){
    const next=i<phItems.length?monthLabelOf(phItems[i]):"__END__";
    if(i===phItems.length||next!==label){
      const count=i-start,header=label?PH_MONTH_H:0;
      const rows=Math.ceil(count/cols);
      const g={start,end:i,label,top:phTotalHeight,header,rows,height:header+rows*phCell};
      phLayoutGroups.push(g); phGroupByStart.set(start,g); phTotalHeight+=g.height;
      start=i; label=next;
    }
  }
}
function groupForIndex(index){
  if(!phLayoutGroups.length) return null;
  let lo=0,hi=phLayoutGroups.length-1;
  while(lo<=hi){
    const mid=(lo+hi)>>1,g=phLayoutGroups[mid];
    if(index<g.start) hi=mid-1;
    else if(index>=g.end) lo=mid+1;
    else return g;
  }
  return index>=phItems.length?phLayoutGroups[phLayoutGroups.length-1]:phLayoutGroups[0];
}
function indexAtY(y){
  if(!phLayoutGroups.length) return 0;
  y=Math.max(0,Math.min(phTotalHeight-1,y));
  let lo=0,hi=phLayoutGroups.length-1,g=phLayoutGroups[0];
  while(lo<=hi){
    const mid=(lo+hi)>>1,x=phLayoutGroups[mid];
    if(y<x.top) hi=mid-1;
    else if(y>=x.top+x.height) lo=mid+1;
    else { g=x; break; }
  }
  const cols=Math.max(2,gridCols||3);
  const local=Math.max(0,y-g.top-g.header);
  const row=Math.floor(local/Math.max(1,phCell));
  return Math.min(g.end-1,g.start+row*cols);
}
function startOffsetForIndex(index){
  if(index<=0) return 0;
  if(index>=phItems.length) return phTotalHeight;
  const g=groupForIndex(index),cols=Math.max(2,gridCols||3);
  if(!g) return 0;
  if(index===g.start) return g.top;
  const delta=Math.max(0,index-g.start);
  return g.top+g.header+Math.floor(delta/cols)*phCell;
}
function endOffsetForIndex(index){
  if(index<=0) return 0;
  if(index>=phItems.length) return phTotalHeight;
  const g=groupForIndex(Math.max(0,index-1)),cols=Math.max(2,gridCols||3);
  if(!g) return phTotalHeight;
  const count=Math.max(0,index-g.start);
  return g.top+g.header+Math.ceil(count/cols)*phCell;
}
function makeVirtualSpacer(px,id){
  const d=document.createElement("div");
  if(id) d.id=id;
  d.className="ph-virtual-spacer";
  d.style.gridColumn="1 / -1";
  d.style.height=Math.max(0,px)+"px";
  d.style.pointerEvents="none";
  return d;
}
function renderVirtualWindow(force){
  const box=$("#photos"),view=document.getElementById("view-photos");
  if(!box||!view||!phItems.length) return;
  if(!phLayoutGroups.length) rebuildVirtualLayout();
  const cols=Math.max(2,gridCols||3),overscan=PH_OVERSCAN_ROWS*phCell;
  let rawStart=indexAtY(Math.max(0,view.scrollTop-overscan));
  let start=Math.max(0,Math.floor(rawStart/PH_WINDOW_BLOCK)*PH_WINDOW_BLOCK);
  const gs=groupForIndex(start);
  if(gs) start=gs.start+Math.floor((start-gs.start)/cols)*cols;
  /* 固定大小窗口：滚动一小段不会反复 replaceChildren。 */
  let end=Math.min(phItems.length,start+PH_MAX_DOM);
  if(end<phItems.length&&end>start){
    const ge=groupForIndex(end-1);
    if(ge) end=Math.min(ge.end,ge.start+Math.ceil((end-ge.start)/cols)*cols);
  }
  if(!force&&start===phWindowStart&&end===phWindowEnd) {
    maybeLoadNextPhonePage();
    return;
  }
  phWindowStart=start; phWindowEnd=end; phRendered=end;
  if(thObserver) thObserver.disconnect();
  phEls=new Map();
  const frag=document.createDocumentFragment();
  const topH=startOffsetForIndex(start);
  if(topH>0.5) frag.appendChild(makeVirtualSpacer(topH,"phTopSpacer"));
  if(start===0&&phoneAlbum==="unfiled"&&unfiledTotal>0){
    const prog=document.createElement("div");
    prog.className="unfiled-progress full"; prog.style.gridColumn="1 / -1"; prog.style.height=phExtraTopH+"px"; prog.style.boxSizing="border-box";
    prog.innerHTML='📊 已整理 <b>'+(unfiledTotal-phItems.length)+'</b> / '+unfiledTotal;
    frag.appendChild(prog);
  }
  let selOrder=null;
  if(multi&&selection.size){ selOrder=new Map(); let n=1; for(const k of selection) selOrder.set(k,n++); }
  for(let i=start;i<end;i++){
    const g=phGroupByStart.get(i);
    if(g&&g.label){
      const sep=document.createElement("div");
      sep.className="ph ph-month";
      sep.textContent=g.label;
      sep.style.gridColumn="1 / -1";
      sep.style.height=PH_MONTH_H+"px";
      sep.style.minHeight=PH_MONTH_H+"px";
      sep.style.boxSizing="border-box";
      frag.appendChild(sep);
    }
    const m=phItems[i];
    frag.appendChild(buildPhotoEl(m,i,selOrder?selOrder.get(itemKey(m)):0));
  }
  const endH=endOffsetForIndex(end);
  const bottomH=Math.max(0,phTotalHeight-endH);
  if(bottomH>0.5) frag.appendChild(makeVirtualSpacer(bottomH,"phBottomSpacer"));
  const st=phoneAlbum?phonePageState.get(phoneAlbum):null;
  if(end>=phItems.length&&st&&st.hasMore){
    const more=document.createElement("div");
    more.id="phMore"; more.className="ph-more"; more.style.gridColumn="1 / -1";
    more.textContent=st.loading?"正在加载更多…":"继续下滑加载更多";
    frag.appendChild(more);
  }
  box.replaceChildren(frag);
  maybeLoadNextPhonePage();
}
function scheduleVirtualRender(force){
  if(phScrollRaf) return;
  phScrollRaf=requestAnimationFrame(()=>{ phScrollRaf=0; renderVirtualWindow(!!force); });
}
function maybeLoadNextPhonePage(){
  if(!phoneAlbum) return;
  const st=phonePageState.get(phoneAlbum),view=document.getElementById("view-photos");
  if(!st||!st.hasMore||st.loading||!view) return;
  const threshold=Math.max(600,phCell*5);
  if(view.scrollTop+view.clientHeight>=phTotalHeight-threshold) loadMorePhoneMedia();
}
function bindPhScroll(){
  if(phScrollBound) return;
  phScrollBound=true;
  const view=document.getElementById("view-photos");
  if(!view) return;
  view.addEventListener("scroll",()=>scheduleVirtualRender(false),{passive:true});
}
/* 保留旧函数名，其他模块无需改调用。 */
function maybeRenderMore(){ scheduleVirtualRender(false); }
function renderChunk(){ renderVirtualWindow(true); }
function renderMoreTo(px){ const v=document.getElementById("view-photos"); if(v) v.scrollTop=px||0; renderVirtualWindow(true); }
function ensureSentinel(){ /* V2 由虚拟窗口中的 phMore 负责分页提示 */ }
function markPhDirty(){ phDirty=true; }
function appendPhonePageToGrid(){
  if(orgSub!=="photos") return;
  phItems=visibleMedia();
  phItemMap=new Map(phItems.map(m=>[itemKey(m),m]));
  rebuildVirtualLayout();
  renderVirtualWindow(true);
}
function renderPhotos(keepScroll){
  const box=$("#photos"),items=visibleMedia(),view=document.getElementById("view-photos");
  const prevTop=keepScroll&&view?view.scrollTop:0;
  const ctx=phoneAlbum!==null?"p:"+phoneAlbum:(currentAlbum===null?"all":"a:"+currentAlbum);
  if(phoneAlbumLoading&&phoneAlbum!==null&&!items.length){ phGridAlbum=ctx; return; }
  const same=!phDirty&&phGridAlbum===ctx;
  phGridAlbum=ctx; phDirty=false;
  phItems=items; phItemMap=new Map(items.map(m=>[itemKey(m),m]));
  if(!items.length){
    stopPhotoBackgroundWork();
    phEls=new Map(); phWindowStart=phWindowEnd=-1; phLayoutGroups=[]; phTotalHeight=0;
    box.className="";
    box.innerHTML='<div class="empty"><div class="big">📷</div>还没有照片<br><span style="font-size:13px">点击上方相册进入</span></div>';
    return;
  }
  box.className="ph-grid";
  box.style.gridTemplateColumns="repeat("+gridCols+",1fr)";
  bindPhScroll();
  rebuildVirtualLayout();
  if(!keepScroll&&!same&&view) view.scrollTop=0;
  else if(keepScroll&&view) view.scrollTop=prevTop;
  phWindowStart=phWindowEnd=-1;
  renderVirtualWindow(true);
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
  if(!multi){
    selection.clear();
    $("#selbar").classList.remove("show");
    $("#multiAlbums").classList.remove("show");
    if(orgSub==="photos") updateTitle();
    return;
  }
  multi = false; selection.clear();
  /* 只有真正处于多选模式才遍历已渲染节点 */
  phEls.forEach(el=>{ el.classList.remove("multi","sel-on"); const b=el.querySelector(".idx"); if(b) b.textContent=""; });
  $("#selbar").classList.remove("show");
  $("#multiAlbums").classList.remove("show");
  $("#multiAlbums").innerHTML = "";
  if(orgSub==="photos") updateTitle();
}
function selectAll(){
  const items=visibleMedia();
  const st=phoneAlbum?phonePageState.get(phoneAlbum):null;
  const allSelected=(!st||!st.hasMore)&&items.length&&items.every(m=>selection.has(itemKey(m)));
  if(allSelected){
    selection=new Set();
    phEls.forEach(el=>{ el.classList.remove("sel-on"); const b=el.querySelector(".idx"); if(b) b.textContent=""; });
    refreshBadges();
    return;
  }
  if(phoneAlbum&&st&&st.hasMore){
    toast("正在加载完整相册用于全选…");
    const id=phoneAlbum,seq=albumOpenSeq;
    readPhoneMediaAll(id,all=>{
      if(phoneAlbum!==id||seq!==albumOpenSeq) return;
      phoneMedia=all;
      const token=mediaStoreToken(true);
      const last=all[all.length-1]||{};
      const doneState={nextOffset:all.length,beforeDate:last.dateAdded!=null?last.dateAdded:-1,
                       beforeId:last.uri?parseInt(String(last.uri).split("/").pop(),10)||-1:-1,
                       hasMore:false,complete:true,loading:false,token};
      rememberAlbum(id,phoneMedia,token,doneState);
      putAlbumCache(id,phoneMedia,token,doneState);
      selection=new Set(phoneMedia.map(m=>itemKey(m)));
      markPhDirty(); renderPhotos(true); refreshBadges();
    });
    return;
  }
  selection=new Set(items.map(m=>itemKey(m)));
  renderVirtualWindow(true);
  refreshBadges();
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
  albumPicker("移动到相册",name=>nativeMove(name,list));
}
function nativeMove(name, list){
  if(!list || !list.length) return;
  try {
    const uris = JSON.stringify(list.map(m=>m.uri));
    /* 乐观移入：先从当前网格移除对应 DOM（不重建，其他照片不重新加载），后台慢慢移动，失败自动恢复 */
    const removed=[];
    for(const m of list){
      const k=itemKey(m);
      const idx=phoneMedia.indexOf(m); if(idx>=0){ phoneMedia.splice(idx,1); removed.push(m); }
      const el=phEls.get(k); if(el){ el.remove(); phEls.delete(k); }
    }
    appendPhonePageToGrid();
    exitMulti();
    if(!BRIDGE || !BRIDGE.moveToAlbumAsync){ for(const m of removed) phoneMedia.push(m); renderPhotos(true); toast("移动失败"); return; }
    const moveCb=nativeCallback("move", resJson => {
      let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
      const ok=res.filter(r=>r.ok).length, fail=res.length-ok;
      if(ok) recordStats("move", ok);
      updateFabDone();
      if(ok>0){
        rememberRecentAlbum(name);
        const okUris=new Set(res.filter(r=>r.ok).map(r=>r.uri));
        removed.filter(m=>okUris.has(m.uri)).forEach(markReviewed);
        const sourceId=(phoneAlbum && phoneAlbum!=="unfiled") ? phoneAlbum : (removed[0]&&removed[0].albumId);
        if(sourceId) removeUrisFromCachedAlbum(sourceId,okUris);
        else phoneMediaCache.delete("unfiled");
        const target=phoneAlbums.find(a=>a.name===name);
        if(target) invalidateAlbumCache(target.id);
        try{ localStorage.removeItem("pp_albums_cache"); }catch(e){}
        const undoItems=res.filter(r=>r.ok && r.from).map(r=>{
          const item=removed.find(m=>m.uri===r.uri);
          return item ? {item:item,from:r.from} : null;
        }).filter(Boolean);
        if(undoItems.length) moveUndoStack.push({items:undoItems,name:name});
        syncViewerActions();
      }
      if(fail>0){
        /* 失败项恢复显示 */
        const failedUris=new Set(res.filter(r=>!r.ok).map(r=>r.uri));
        for(const m of removed){ if(failedUris.has(m.uri) && phoneMedia.indexOf(m)<0) phoneMedia.push(m); }
        renderPhotos(true);
        const denied=res.some(r=>r.err==="write_permission_denied");
        toast(ok>0 ? ("已移动 "+ok+" 项，「"+name+"」"+fail+" 项未移动") : (denied ? "未获得系统移动授权" : "移动失败：无法修改照片"));
      } else {
        toast("已移入「"+name+"」"+ok+" 项", undoItems.length ? "撤销" : "", undoItems.length ? undoLastMove : null);
      }
      if(ok>0 && BRIDGE && BRIDGE.hasPermission) refreshPhoneAlbums(true);
    });
    BRIDGE.moveToAlbumAsync(name, uris, moveCb);
    /* 后台等 MediaStore 更新后再刷新相册计数 */
    setTimeout(()=>{
      try{ if(BRIDGE && BRIDGE.hasPermission) refreshPhoneAlbums(true); if(orgSub==="home") renderHome(); }catch(e){}
    }, 1500);
  } catch(e){ toast("移动失败："+e); }
}
function undoLastMove(){
  const move=moveUndoStack.pop();
  if(!move || !move.items.length || !BRIDGE || !BRIDGE.moveToPathAsync) return;
  const byPath=new Map();
  move.items.forEach(x=>{ if(!byPath.has(x.from)) byPath.set(x.from,[]); byPath.get(x.from).push(x); });
  let restored=0, failed=0, pending=byPath.size; const failedItems=[];
  toast("正在撤销移动…");
  byPath.forEach((items,path)=>{
    const cb=nativeCallback("undoMove", raw=>{
      let res=[]; try{res=JSON.parse(raw);}catch(e){}
      const okUris=new Set(res.filter(r=>r.ok).map(r=>r.uri));
      restored+=okUris.size; failed+=res.length-okUris.size;
      items.forEach(x=>{ if(!okUris.has(x.item.uri)) failedItems.push(x); });
      items.forEach(x=>{
        if(!okUris.has(x.item.uri)||phoneMedia.indexOf(x.item)>=0) return;
        if(Number.isInteger(x.viewerIndex)) phoneMedia.splice(Math.max(0,Math.min(x.viewerIndex,phoneMedia.length)),0,x.item);
        else phoneMedia.push(x.item);
      });
      pending--;
      if(!pending){
        if(failedItems.length) moveUndoStack.push({items:failedItems,name:move.name});
        if(restored){ const focus=items.find(x=>okUris.has(x.item.uri)&&Number.isInteger(x.viewerIndex)); if(focus) restoreViewerItem(focus.item,focus.viewerIndex); else renderPhotos(true); }
        refreshPhoneAlbums(true);
        syncViewerActions();
        toast(failed ? ("已撤销 "+restored+" 项，"+failed+" 项未恢复") : "已撤销移动");
      }
    });
    BRIDGE.moveToPathAsync(JSON.stringify(items.map(x=>x.item.uri)),path,cb);
  });
}
async function removeSelected(){
  const list = visibleMedia().filter(m=>selection.has(itemKey(m)));
  if(!list.length) return;
  /* 移入回收站无需确认（可恢复）；一次性全部消失（一起飞走再移除，不是一张张变少） */
  if(phoneAlbum!==null){
    for(const m of list){ await trashPhone(m); }
    list.forEach(m=>{ const el=phEls.get(itemKey(m)); if(el) el.classList.add("flyout-up"); });
    await new Promise(r=>setTimeout(r,150));
    list.forEach(m=>{ const el=phEls.get(itemKey(m)); if(el){ el.remove(); phEls.delete(itemKey(m)); } });
    exitMulti();
    renderPhotos(true);
    await refreshTrash();
    refreshPhoneAlbums();
    toast("已移入回收站 "+list.length+" 项");
    return;
  }
  const ids = [...selection].filter(k => k && !k.startsWith("content:"));
  if(!ids.length) return;
  for(const k of ids){
    const m = media.find(x=>x.id===k);
    if(m){
      await trashOne(m);
      const el=phEls.get(k); if(el){ el.remove(); phEls.delete(k); }
    }
  }
  exitMulti();
  saveState();
}

/* ============ 回收站（App 内软删除：系统文件不动，清空回收站时才真正删除） ============ */
let trashedUris = new Set();   // 已回收的手机相册 uri，用于从相册中过滤
let pendingMoves = new Set();  // kept empty: moves are true background moves now
let hiddenAlbums = new Set(JSON.parse(localStorage.getItem("pp_hidden")||"[]"));
let unfiledTotal = 0;   // 未整理视图加载总数（已整理 = 总数 - 当前剩余）  // 隐藏相册 id → 照片计入“未整理”
function saveHidden(){
  try{ localStorage.setItem("pp_hidden", JSON.stringify([...hiddenAlbums])); }catch(e){}
  phoneMediaCache.delete("unfiled"); phonePageState.delete("unfiled"); unfiledTotal=0;
  try{ if(db) db.transaction("phonecache","readwrite").objectStore("phonecache").delete("unfiled"); }catch(e){}
}
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
function renderTrash(){
  const box=$("#trash");
  const view=$("#view-trash");
  const prevTop = view ? view.scrollTop : 0;
  box.className="ph-grid";
  box.innerHTML="";
  if(!trashList.length){
    box.innerHTML='<div class="empty full"><div class="big">🗑️</div>回收站是空的<br><span style="font-size:13px">查看照片时上滑即可移入回收站</span></div>';
    return;
  }
  const frag=document.createDocumentFragment();
  trashList.forEach((m,i)=>{
    frag.appendChild(trashEl(m, i));
  });
  box.appendChild(frag);
  const actions=document.createElement("div");
  actions.className="trash-actions full";
  actions.innerHTML='<button class="big-btn ghost" id="btnRestoreAll">↩️ 全部恢复</button><button class="big-btn danger" id="btnEmpty">清空回收站</button>';
  box.appendChild(actions);
  $("#btnRestoreAll").addEventListener("click", restoreAllTrash);
  $("#btnEmpty").addEventListener("click", emptyTrash);
  if(view && prevTop>0) requestAnimationFrame(()=>{ view.scrollTop = prevTop; });
}
function trashEl(m, i){
  const el=document.createElement("div"); el.className="ph";
  el.innerHTML='<img loading="lazy" decoding="async" src="'+(m.thumb||m.uri||objURL(m))+'" alt="">'+(m.isVideo?'<span class="dur">▶</span>':'');
  if(i < 60){ el.classList.add("anim-pop"); el.style.animationDelay=(i*20)+"ms"; }
  el.addEventListener("click", ()=>{ openViewer(trashList, trashList.indexOf(m), "trash"); });
  bindLong(el, ()=>sheetTrashItem(m));
  return el;
}
function sheetTrashItem(m){
  sheet([{ic:"↩️",t:"恢复",f:()=>restoreFromTrash(m)},
          {ic:"🗑️",t:"彻底删除",f:()=>permanentDelete(m)}],"回收站操作");
}
/* 手机照片移入回收站：只做 App 内标记，系统文件不动 */
async function trashPhone(m){
  const rec={id:"p_"+m.uri, uri:m.uri, name:m.name, mime:m.mime||m.type||"", isVideo:!!((m.mime||m.type)||"").startsWith("video/"), trashedAt:Date.now(), fromPhone:true, albumId:m.albumId||null};
  await storePut("trash", rec);
  trashedUris.add(m.uri);
  const idx=phoneMedia.indexOf(m); if(idx>=0) phoneMedia.splice(idx,1);
  markPhDirty();
  trashUndoStack.push({type:"phone", uri:m.uri, id:rec.id});
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
  const affected = all.filter(t=>t.fromPhone && set.has(t.uri));
  const delIds = affected.map(t=>t.id);
  await storeDelAll("trash", delIds);
  affected.forEach(t=>{
    trashedUris.delete(t.uri);
    if(t.albumId) removeUrisFromCachedAlbum(t.albumId,[t.uri]);
  });
  if(pendingDelAlbumId){ invalidateAlbumCache(pendingDelAlbumId); pendingDelAlbumId=null; }
  if(pendingDelAlbumName){ removeCreated(pendingDelAlbumName); pendingDelAlbumName=null; }
  /* 已确认删除的源照片从待删列表移除 */
  if(set.size){
    pendingMoves = new Set([...pendingMoves].filter(u=>!set.has(u)));
    updateFabDone();
  }
  await refreshTrash();
  syncViewerActions();
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
    trashUndoStack.push({type:"app", item:tr});
    recordStats("trash",1);
    toastTrash();
  }
  await refreshTrash();
}
function toastTrash(){ toast("已移入回收站","撤销",()=>undoTrash()); }
async function undoTrash(){
  const t=trashUndoStack.pop();
  if(!t) return;
  if(t.type==="phone"){
    await storeDel("trash", t.id || ("p_"+t.uri));
    trashedUris.delete(t.uri);
    recordStats("restore",1);
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
  if(t.item&&Number.isInteger(t.viewerIndex)) restoreViewerItem(t.item,t.viewerIndex);
  refreshActiveView();
  updateViewerChrome();
  syncViewerActions();
}

/* ============ 全屏查看器（窗口化渲染 + 邻居预加载） ============ */
let viewerList=[], viewerIdx=0, viewerMode="normal";
let g=null, longT=null, lastTap=0, zoomed=false, pinch=0;
let vSlots=[]; const VWIN=2;

function restoreViewerItem(item,index){
  if(!item||!$("#viewer").classList.contains("open")||viewerMode!=="normal") return;
  if(viewerList.indexOf(item)<0) viewerList.splice(Math.max(0,Math.min(index,viewerList.length)),0,item);
  viewerIdx=Math.max(0,viewerList.indexOf(item));
  buildSlides(); setTrack(0,0,1,false); updateViewerChrome();
}

function openViewer(list, idx, mode){
  viewerList=list; viewerIdx=idx; viewerMode=mode||"normal"; zoomed=false; lastTap=0;
  $("#viewer").classList.add("open");
  applyVWork();
  buildSlides();
  setTrack(0,0,1,false);
  updateViewerChrome();
  if(viewerMode==="normal") requestWriteBatch(viewerList);
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
  /* 普通模式且网格未变：保留当前网格不重建，返回不卡顿 */
  if(viewerMode==="normal" && orgSub==="photos" && !phDirty){ return; }
  phDirty=false;
  refreshActiveView();
}
function setTrack(dx, dy, sc, animate){
  const t=$("#vTrack");
  t.style.transition = animate ? "transform .22s cubic-bezier(.2,.8,.2,1)" : "none";
  t.style.transform = "translate(calc("+(-viewerIdx*100)+"% + "+dx+"px), 0)";
}
function setCurrentLift(dy, sc, animate){
  const cur=vSlots.find(s=>s.idx===viewerIdx);
  if(!cur) return;
  const dx=dy<0 ? Math.min(150,-dy*.35) : 0;
  cur.el.style.transition=animate ? "transform .22s cubic-bezier(.2,.8,.2,1)" : "none";
  cur.el.style.transform="translateX(calc("+(viewerIdx*100)+"% + "+dx+"px)) translateY("+dy+"px) scale("+sc+")";
}
function resetCurrentLift(animate){ setCurrentLift(0,1,animate); }
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
    /* 关键：复用 slide 时清除动画残留（flyout-up 会 opacity:0 导致黑屏） */
    slot.el.classList.remove("flyout-up","peek","zoomed");
    slot.el.style.transition="none";
    slot.el.style.transform="translateX("+(i*100)+"%)";
    setSlideContent(slot.el, viewerList[i], i===viewerIdx);
    keep.add(slot);
  }
  vSlots=vSlots.filter(s=>{
    if(!keep.has(s)){ track.removeChild(s.el); return false; }
    return true;
  });
  preloadIdx(viewerIdx+VWIN+1);
  preloadIdx(viewerIdx-VWIN-1);
}
function setSlideContent(el, m, current){
  const src=objURL(m);
  if(isVideo(m)){
    delete el.dataset.mediaSrc; delete el.dataset.thumbSrc;
    let v=el.querySelector("video");
    if(!v){ el.innerHTML='<video src="'+src+'" playsinline controls autoplay preload="auto"></video>'; v=el.querySelector("video"); }
    else if(v.src!==src){ v.src=src; v.controls=true; }
    else v.controls=true;
    if(current){ v.currentTime=0; v.play().catch(()=>{}); }
    else { try{v.pause();}catch(e){} }
  } else {
    /* 重建复用卡片，避免相邻照片的旧缩略图残留在当前照片后方形成叠影。 */
    const thumb = m.thumb || "";
    if(el.dataset.mediaSrc===src && el.dataset.thumbSrc===thumb) return;
    el.dataset.mediaSrc=src; el.dataset.thumbSrc=thumb;
    el.innerHTML=(thumb?'<img class="thumb" src="'+thumb+'" alt="" decoding="async">':'')+'<img class="full" src="'+src+'" alt="" decoding="async">';
    const full=el.querySelector("img.full");
    if(!thumb) full.classList.add("show");
    full.onload=()=>{ full.classList.add("show"); const old=el.querySelector("img.thumb"); if(old) old.remove(); };
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
    let chips='<div class="vchip new" id="vNew">＋ 新建</div>';
    albumTargets().forEach(a=>{ chips+='<div class="vchip" data-alb="'+escapeHtml(a.name)+'">'+escapeHtml(a.name)+'</div>'; });
    work.innerHTML='<div class="vw-albums">'+chips+'</div>';
    work.querySelectorAll(".vchip").forEach(c=>{
      c.addEventListener("click", ()=>{
        if(c.id==="vNew"){ promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v, ()=>moveCurrentTo(v)); } }); }
        else if(c.classList.contains("on")){ moveOutCurrent(c.dataset.alb); }
        else { moveCurrentTo(c.dataset.alb); }
      });
    });
    /* 高亮当前照片所属相册（照片自带 albumNames；旧数据/异常时 fallback 原生查询） */
    try{
      const names = new Set((m.albumNames||[]).map(n=>String(n)));
      if(!names.size && BRIDGE && BRIDGE.readAlbumOf && m.uri && m.uri.startsWith("content:")){
        try{
          const list=JSON.parse(BRIDGE.readAlbumOf(m.uri)||"[]");
          list.forEach(a=>names.add(String(a.name)));
        }catch(e){}
      }
      if(names.size){
        work.querySelectorAll(".vchip[data-alb]").forEach(c=>{
          if(names.has(c.dataset.alb)) c.classList.add("on");
        });
      }
    }catch(e){}
    syncViewerActions();
  }
}
/* 大图浏览：把当前照片移出所属相册（移到 PicaPhoto 整理区） */
function moveOutCurrent(name){
  const m=viewerList[viewerIdx];
  if(!m) return;
  if(!m.uri || !m.uri.startsWith("content:")){ toast("仅系统相册照片支持移出"); return; }
  /* 乐观移出 */
  const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
  const pi=phoneMedia.indexOf(m); if(pi>=0) phoneMedia.splice(pi,1);
  markPhDirty();
  afterViewerRemove();
  toast("正在移出「"+name+"」…");
  if(!BRIDGE || !BRIDGE.moveOutAlbumAsync){ if(pi>=0) phoneMedia.splice(pi,0,m); if(i>=0) viewerList.splice(i,0,m); afterViewerRemove(); toast("移出失败"); return; }
  try{
    const moCb=nativeCallback("moveout", resJson => {
      let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
      if(res[0]&&res[0].ok){
        recordStats("move",1);
        const sourceId=(m.albumId || (phoneAlbum!=="unfiled"?phoneAlbum:null));
        if(sourceId) removeUrisFromCachedAlbum(sourceId,[m.uri]); else phoneMediaCache.delete("unfiled");
        try{ localStorage.removeItem("pp_albums_cache"); }catch(e){}
        if(res[0].from) moveUndoStack.push({items:[{item:m,from:res[0].from}],name:name});
        syncViewerActions();
        toast("已移出「"+name+"」到 PicaPhoto", res[0].from ? "撤销" : "", res[0].from ? undoLastMove : null);
        updateFabDone();
      } else {
        if(i>=0 && viewerList.indexOf(m)<0) viewerList.splice(i,0,m);
        if(pi>=0 && phoneMedia.indexOf(m)<0) phoneMedia.splice(pi,0,m);
        afterViewerRemove();
        toast("移出失败");
      }
    });
    BRIDGE.moveOutAlbumAsync(JSON.stringify([m.uri]), moCb);
  }catch(e){ toast("移出失败："+e); }
}
function afterViewerRemove(){
  if(!viewerList.length){ closeViewer(); return; }
  if(viewerIdx>=viewerList.length) viewerIdx=viewerList.length-1;
  buildSlides();
  setTrack(0,0,1,false);
  updateViewerChrome();
}
function maybeLoadViewerPage(cb){
  if(viewerMode!=="normal"||!phoneAlbum){ if(cb) cb(0); return; }
  const st=phonePageState.get(phoneAlbum);
  if(!st||!st.hasMore){ if(cb) cb(0); return; }
  loadMorePhoneMedia(n=>{
    /* viewerList 通常和 phoneMedia 是同一数组；若不是则补齐引用。 */
    if(viewerList!==phoneMedia){ viewerList=phoneMedia; }
    buildSlides(); updateViewerChrome();
    if(cb) cb(n);
  });
}
function moveViewer(step){
  if(step>0 && viewerIdx>=viewerList.length-1){
    const st=phoneAlbum?phonePageState.get(phoneAlbum):null;
    if(st&&st.hasMore){
      maybeLoadViewerPage(()=>{
        if(viewerIdx<viewerList.length-1) moveViewer(1);
        else setTrack(0,0,1,true);
      });
      return;
    }
  }
  if(step>0 && viewerIdx>=viewerList.length-4) maybeLoadViewerPage();
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
    /* 乐观移入：立即从大图列表移除，后台移动，失败恢复 */
    const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
    const pi=phoneMedia.indexOf(m); if(pi>=0) phoneMedia.splice(pi,1);
    afterViewerRemove();
    if(!BRIDGE || !BRIDGE.moveToAlbumAsync){ if(pi>=0) phoneMedia.splice(pi,0,m); if(i>=0) viewerList.splice(i,0,m); afterViewerRemove(); toast("移动失败"); return; }
    try{
      const mcCb=nativeCallback("movecurrent", resJson => {
        let res=[]; try{ res=JSON.parse(resJson); }catch(e){}
      if(res[0]&&res[0].ok){
          recordStats("move",1);
          const sourceId=(m.albumId || (phoneAlbum!=="unfiled"?phoneAlbum:null));
          if(sourceId) removeUrisFromCachedAlbum(sourceId,[m.uri]); else phoneMediaCache.delete("unfiled");
          const target=phoneAlbums.find(a=>a.name===name);
          if(target) invalidateAlbumCache(target.id);
          try{ localStorage.removeItem("pp_albums_cache"); }catch(e){}
          if(res[0].from) moveUndoStack.push({items:[{item:m,from:res[0].from,viewerIndex:i}],name:name});
          syncViewerActions();
          toast("已移入「"+name+"」", res[0].from ? "撤销" : "", res[0].from ? undoLastMove : null);
          updateFabDone();
          afterViewerRemove();
        } else {
          /* 恢复 */
          if(i>=0 && viewerList.indexOf(m)<0) viewerList.splice(i,0,m);
          if(pi>=0 && phoneMedia.indexOf(m)<0) phoneMedia.splice(pi,0,m);
          afterViewerRemove();
          toast("移动失败");
        }
      });
      BRIDGE.moveToAlbumAsync(name, JSON.stringify([m.uri]), mcCb);
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
$("#vPreview").addEventListener("touchstart", e=>{
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
      $("#vHint").textContent = viewerMode==="trash" ? "↑ 上滑删除 · ↓ 下滑返回" : "↑ 上滑整理 · ↓ 下滑返回";
    }
  },360);
},{passive:true});

$("#vPreview").addEventListener("touchmove", e=>{
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
    setCurrentLift(cy, sc, false);
    const zone=$("#vTrashZone");
    zone.classList.toggle("show", viewerMode==="normal" && cy<-70);
    $("#vHint").classList.toggle("show", !(cy<-70));
    if(cy<-70) $("#vHint").textContent="松手移入回收站";
    else if(cy>80) $("#vHint").textContent="松手返回";
    else $("#vHint").textContent = viewerMode==="trash" ? "↑ 上滑删除 · ↓ 下滑返回" : "↑ 上滑回收 · ↓ 下滑返回";
  }
},{passive:false});

$("#vPreview").addEventListener("touchend", e=>{
  clearTimeout(longT);
  if(!g) return;
  const g0=g; g=null;
  const cur=vSlots.find(s=>s.idx===viewerIdx);
  if(cur) cur.el.classList.remove("peek");
  $("#vHint").classList.remove("show");
  $("#vTrashZone").classList.remove("show");
  if(g0.long && g0.mode==="v"){
    if(g0.dy<-70) quickOrganizeCurrent();
    else if(g0.dy>70) closeViewer();
    else resetCurrentLift(true);
    return;
  }
  if(g0.mode==="h"){
    if(g0.dx<-60) moveViewer(1);
    else if(g0.dx>60) moveViewer(-1);
    else setTrack(0,0,1,true);
    return;
  }
  if(g0.mode==="v"){
    if(g0.dy<-70){ quickOrganizeCurrent(); }
    else if(g0.dy>70){ closeViewer(); }
    else { resetCurrentLift(true); }
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

$("#vPreview").addEventListener("touchcancel", ()=>{
  clearTimeout(longT); g=null;
  const cur=vSlots.find(s=>s.idx===viewerIdx); if(cur) cur.el.classList.remove("peek");
  resetCurrentLift(true);
  $("#vHint").classList.remove("show"); $("#vTrashZone").classList.remove("show");
});
$("#vClose").addEventListener("click", closeViewer);
$("#vDelete").addEventListener("click", ()=>{ doTrashCurrent(); });
$("#vUndoCompact").addEventListener("click", ()=>{ if(moveUndoStack.length) undoLastMove(); else undoTrash(); });
function syncViewerActions(){
  const undo=$("#vUndoCompact");
  if(undo) undo.hidden=!(moveUndoStack.length || trashUndoStack.length);
}

async function doTrashCurrent(){
  const m=viewerList[viewerIdx];
  if(!m) return;
  const cur=vSlots.find(s=>s.idx===viewerIdx);
  /* 当前照片克隆到飞走层：一张飞走的同时，下一张立即在原位显示，可连续上滑 */
  if(cur){
    const img=cur.el.querySelector("img.full.show")||cur.el.querySelector("img.full")||cur.el.querySelector("img.thumb");
    if(img && img.src){
      const ghost=document.createElement("img");
      ghost.src=img.src; ghost.alt=""; ghost.className="ghost-fly";
      document.body.appendChild(ghost);
      requestAnimationFrame(()=>requestAnimationFrame(()=>ghost.classList.add("fly")));
      setTimeout(()=>{ if(ghost.parentNode) ghost.parentNode.removeChild(ghost); },260);
    }
  }
  const i=viewerList.indexOf(m); if(i>=0) viewerList.splice(i,1);
  afterViewerRemove();
  if(viewerMode==="trash"){ await permanentDelete(m); }
  else { await trashOne(m); const top=trashUndoStack[trashUndoStack.length-1]; if(top){top.item=m;top.viewerIndex=i;} }
}
function quickOrganizeCurrent(){
  doTrashCurrent();
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
  const manageSupported=!!(BRIDGE&&BRIDGE.supportsManageMedia&&BRIDGE.supportsManageMedia());
  const manageDesc=manageSupported ? (canManageMedia()?"已开启，不再逐张询问":"未开启，点按申请") : "Android 11 将按整理队列批量申请";
  s.innerHTML=`
    <div class="me-head">
      <img src="icon-192.png" alt="">
      <div><div class="me-name">PicaPhoto</div><div class="me-ver">移动版 v${APP_VERSION} · 自动更新</div></div>
    </div>
    <div class="stat-grid">
      <div class="stat"><b>${stats.organizedTotal}</b><span>累计整理</span></div>
      <div class="stat"><b>${todayN}</b><span>今日整理</span></div>
      <div class="stat"><b>${stats.trashTotal}</b><span>累计回收</span></div>
      <div class="stat"><b>${stats.restoreTotal}</b><span>累计恢复</span></div>
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
      <div class="set-row" id="rowManageMedia"><div class="tt"><div class="n">申请相册访问权限</div><div class="d">${manageDesc}</div></div><span class="arrow">${canManageMedia()?"已开启":"›"}</span></div>
      <div class="set-row" id="rowTheme"><div class="tt"><div class="n">外观主题</div><div class="d" id="themeDesc">${themeDesc}</div></div>
        <div class="switch ${darkOn?'on':''}" id="swTheme"></div></div>
      <div class="set-row" id="rowQueue"><div class="tt"><div class="n">整理排序</div><div class="d">${queueOrder==="new"?"最新时间优先":queueOrder==="old"?"最早时间优先":queueOrder==="size_desc"?"大文件优先":"小文件优先"}</div></div><span class="arrow">›</span></div>
      <div class="set-row" id="rowMediaFilter"><div class="tt"><div class="n">媒体筛选</div><div class="d">${mediaFilter==="all"?"照片和视频":mediaFilter==="photo"?"仅照片":"仅视频"}</div></div><span class="arrow">›</span></div>
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
  $("#rowManageMedia").addEventListener("click",()=>{
    if(canManageMedia()){toast("相册访问权限已开启");return;}
    if(manageSupported) requestFullPhotoAccess(); else toast("进入照片整理时会一次申请当前队列权限");
  });
  /* 外观主题：点行弹出三选（跟随系统/浅色/深色）；点开关快速切换深/浅 */
  $("#rowTheme").addEventListener("click", ()=>{
    sheet([{ic:"🌗",t:"跟随系统",f:()=>{theme="auto";localStorage.setItem("pp_theme","auto");applyTheme();renderMe();}},
      {ic:"☀️",t:"浅色",f:()=>{theme="light";localStorage.setItem("pp_theme","light");applyTheme();renderMe();}},
      {ic:"🌙",t:"深色",f:()=>{theme="dark";localStorage.setItem("pp_theme","dark");applyTheme();renderMe();}}],"外观主题");
  });
  $("#rowQueue").addEventListener("click",()=>sheet([
    {ic:"🆕",t:"最新时间优先",f:()=>setMediaSort("new")},
    {ic:"🕘",t:"最早时间优先",f:()=>setMediaSort("old")},
    {ic:"🐘",t:"大文件优先",f:()=>setMediaSort("size_desc")},
    {ic:"🪶",t:"小文件优先",f:()=>setMediaSort("size_asc")}
  ],"整理排序"));
  $("#rowMediaFilter").addEventListener("click",()=>sheet([
    {ic:"🖼️",t:"照片和视频",f:()=>setMediaFilter("all")},
    {ic:"📷",t:"仅照片",f:()=>setMediaFilter("photo")},
    {ic:"🎬",t:"仅视频",f:()=>setMediaFilter("video")}
  ],"媒体筛选"));
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

/* 小图长按预览：长按照片显示大图，松手取消 */
let phLongKey=null, phLongT=null, phLongSuppress=false;
function showPhPreview(m){
  const p=$("#phPreview");
  if(!p) return;
  p.innerHTML='<img src="'+imgSrcOf(m)+'" alt="">';
  p.classList.add("show");
}
function hidePhPreview(){ const p=$("#phPreview"); if(p) p.classList.remove("show"); }
(function(){
  const box=$("#photos");
  let sx=0, sy=0;
  box.addEventListener("touchstart", e=>{
    if(multi || e.touches.length!==1) return;
    const el=document.elementFromPoint(e.touches[0].clientX, e.touches[0].clientY);
    const ph=el&&el.closest?el.closest(".ph"):null;
    if(!ph || !ph.dataset.key) return;
    phLongKey=ph.dataset.key; sx=e.touches[0].clientX; sy=e.touches[0].clientY; phLongSuppress=false;
    clearTimeout(phLongT);
    phLongT=setTimeout(()=>{
      if(phLongKey===null) return;
      phLongSuppress=true;
      const items=visibleMedia();
      const m=items.find(x=>itemKey(x)===phLongKey);
      if(m){ showPhPreview(m); vibrate(12); }
    },420);
  },{passive:true});
  box.addEventListener("touchmove", e=>{
    if(phLongKey===null) return;
    const dx=e.touches[0].clientX-sx, dy=e.touches[0].clientY-sy;
    if(Math.abs(dx)>14 || Math.abs(dy)>14){ clearTimeout(phLongT); hidePhPreview(); phLongKey=null; }
  },{passive:true});
  box.addEventListener("touchend", ()=>{ clearTimeout(phLongT); hidePhPreview(); phLongKey=null; setTimeout(()=>{ phLongSuppress=false; },50); });
  box.addEventListener("touchcancel", ()=>{ clearTimeout(phLongT); hidePhPreview(); phLongKey=null; });
})();
/* 照片网格点击委托（避免逐项绑定的性能开销） */
$("#photos").addEventListener("click", e=>{
  if(phLongSuppress){ return; }
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
  ++albumOpenSeq;
  phoneAlbumLoading=false;
  stopPhotoBackgroundWork();
  orgSub="home";
  exitMulti();
  showOrg();
}
function openTrashView(){
  ++albumOpenSeq;
  phoneAlbumLoading=false;
  stopPhotoBackgroundWork();
  orgSub="trash";
  showOrg();
}
function showOrg(){
  hideOrgViews();
  const v = orgSub==="photos" ? "view-photos" : (orgSub==="trash" ? "view-trash" : "view-home");
  $("#"+v).classList.add("active");
  if(orgSub==="home"){ renderHome(); }
  if(orgSub==="photos"){
    const ctx = phoneAlbum!==null ? "p:"+phoneAlbum : (currentAlbum===null?"all":"a:"+currentAlbum);
    if(phoneAlbumLoading){ /* skeleton 已提前放好，等待 IndexedDB/原生回调 */ }
    else if(phDirty || phGridAlbum!==ctx || !phEls.size){ renderPhotos(); }
    else { phDirty=false; }
  }
  if(orgSub==="trash"){ refreshTrash().then(renderTrash); }
  updateFabDone();
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
    ++albumOpenSeq;
    stopPhotoBackgroundWork();
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
/* 回收站卡片右侧小方块：一键清空回收站 */
$("#trashClear").addEventListener("click", e=>{ e.stopPropagation(); emptyTrash(); });
$("#selDone").addEventListener("click", exitMulti);
$("#hideDone").addEventListener("click", ()=>{ saveHidden(); $("#hidePanel").classList.remove("open"); renderHome(); toast(hiddenAlbums.size?("已隐藏 "+hiddenAlbums.size+" 个相册，照片计入未整理"):"未隐藏任何相册"); });
$("#hideCancel").addEventListener("click", ()=>{ $("#hidePanel").classList.remove("open"); });
/* moves take effect automatically in background; only deletion needs system confirm */
function updateFabDone(){ const b=$("#fabDone"); if(b) b.style.display="none"; }
$("#selAll").addEventListener("click", selectAll);
$("#selMove").addEventListener("click", moveSelected);
$("#selDel").addEventListener("click", removeSelected);
function renderMultiAlbums(){
  const box=$("#multiAlbums");
  box.innerHTML="";
  const add=document.createElement("button"); add.className="mchip new"; add.textContent="＋ 新建相册";
  add.addEventListener("click", ()=>{ promptInput("新建相册","",async v=>{ if(v){ createSystemAlbum(v, ()=>moveSelTo(v)); } }); });
  box.appendChild(add);
  albumTargets().forEach(a=>{
    const c=document.createElement("button"); c.className="mchip";
    c.textContent="\uD83D\uDCC1 "+a.name;
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

let lifecycleBound=false;
let initRunning=false;
let appReadySent=false;
function signalAppReady(){
  if(appReadySent) return;
  appReadySent=true;
  try{ if(BRIDGE && BRIDGE.appReady) BRIDGE.appReady(); }catch(e){}
}
function bindLifecycle(){
  if(lifecycleBound) return;
  lifecycleBound=true;
  document.addEventListener("visibilitychange", ()=>{
    if(document.hidden) return;
    mediaTokenCache={t:0,v:""};
    const albumsBox=$("#albums"), photosBox=$("#photos");
    const empty=(!albumsBox || !albumsBox.childElementCount) && (!photosBox || !photosBox.childElementCount);
    if(empty){
      try{ if(db) db.close(); db=null; }catch(e){}
      init();
    }else if(BRIDGE && BRIDGE.hasPermission && BRIDGE.hasPermission()){
      refreshPhoneAlbums(false);
      if(orgSub==="home") renderHome();
    }
  });
  window.addEventListener("online",()=>toast("已联网"));
}
async function init(){
  if(initRunning) return;
  initRunning=true;
  try{
    try{ await openDB(); }catch(e){ toast("存储不可用"); }
    try{ if(navigator.storage && navigator.storage.persist){ navigator.storage.persist().catch(()=>{}); } }catch(e){}

    /* 不再启动时 getAll(phonecache)：当前相册需要时才按 albumId 读取 */
    const core=await Promise.all([
      storeGetAll("media"),
      storeGetAll("albums"),
      loadStats().catch(()=>{}),
      refreshTrash().catch(()=>{})
    ]);
    media=core[0]||[];
    albums=core[1]||[];

    /* 相册列表先使用小型 localStorage 缓存，系统扫描走异步桥接 */
    refreshPhoneAlbums(false);
    applyTheme();
    const d=new Date(); calYear=d.getFullYear(); calMonth=d.getMonth();
    showOrg();

    /* “我的”页面内容很多，不在冷启动首屏主动渲染 */
    bindLifecycle();
    requestAnimationFrame(signalAppReady);

    if(!BRIDGE && navigator.serviceWorker){ navigator.serviceWorker.register("sw.js").catch(()=>{}); }
    setTimeout(()=>checkUpdate(false),1200);
  }finally{
    initRunning=false;
  }
}
init();
