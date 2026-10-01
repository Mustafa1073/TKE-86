const V='m86-v1',A=['./','index.html','manifest.webmanifest','icons/icon-192.png','icons/icon-512.png','icons/icon-maskable-512.png','icons/apple-touch-icon.png','icons/favicon-32.png'];
self.addEventListener('install',e=>{e.waitUntil(caches.open(V).then(c=>c.addAll(A)).then(()=>self.skipWaiting()))});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(k=>Promise.all(k.filter(x=>x!==V).map(x=>caches.delete(x)))).then(()=>self.clients.claim()))});
self.addEventListener('fetch',e=>{const r=e.request;if(r.method!=='GET')return;e.respondWith(fetch(r).then(s=>{if(s.ok||s.type==='opaque'){const c=s.clone();caches.open(V).then(x=>x.put(r,c))}return s}).catch(()=>caches.match(r).then(m=>m||caches.match('index.html'))))});
