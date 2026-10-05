const V='m86-v5';
const CORE=['./','index.html','script.js','manifest.webmanifest','splash/splash-title.svg',
'icons/favicon.ico','icons/favicon-16.png','icons/favicon-32.png',
'icons/apple-touch-icon.png','icons/apple-touch-icon-120.png','icons/apple-touch-icon-152.png','icons/apple-touch-icon-167.png','icons/apple-touch-icon-180.png',
...[48,72,96,128,144,152,192,256,384,512].map(n=>'icons/icon-'+n+'.png'),
'icons/icon-maskable-192.png','icons/icon-maskable-512.png',
'https://fonts.googleapis.com/css2?family=Sora:wght@600;800&display=swap'];

self.addEventListener('install',e=>{
  e.waitUntil(caches.open(V).then(c=>Promise.allSettled(CORE.map(u=>
    fetch(new Request(u,{cache:'reload',mode:u.startsWith('http')?'no-cors':'same-origin'}))
      .then(r=>{if(r.ok||r.type==='opaque')return c.put(u,r)})
  ))).then(()=>self.skipWaiting()));
});

self.addEventListener('activate',e=>{
  e.waitUntil(caches.keys().then(k=>Promise.all(k.filter(x=>x!==V).map(x=>caches.delete(x)))).then(()=>self.clients.claim()));
});

self.addEventListener('fetch',e=>{
  const r=e.request;
  if(r.method!=='GET'||!r.url.startsWith('http'))return;
  e.respondWith(
    caches.open(V).then(c=>c.match(r,{ignoreSearch:true}).then(hit=>{
      const net=fetch(r).then(s=>{
        if(s&&(s.ok||s.type==='opaque'))c.put(r,s.clone());
        return s;
      });
      if(hit){net.catch(()=>{});return hit;}   // from cache, refresh in background
      return net.catch(()=>
        r.mode==='navigate'
          ?c.match('index.html').then(m=>m||c.match('./')).then(m=>m||Response.error())
          :Response.error());
    }))
  );
});
