const CACHE = "picaphoto-v2";
self.addEventListener("install", e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll([
    "./", "index.html", "app.css", "app.js", "manifest.webmanifest", "icon-192.png", "icon-512.png"
  ])).then(() => self.skipWaiting()));
});
self.addEventListener("activate", e => {
  e.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener("fetch", e => {
  if (e.request.method !== "GET") return;
  e.respondWith(
    caches.match(e.request).then(hit => hit || fetch(e.request).then(res => {
      const copy = res.clone();
      if (e.request.url.startsWith(self.location.origin) && !e.request.url.includes("blob:")) {
        caches.open(CACHE).then(c => c.put(e.request, copy));
      }
      return res;
    }).catch(() => caches.match("./index.html")))
  );
});
