/* Ulm Dojo service worker.
 * Precache the whole app on install; serve cache-first so the installed PWA
 * opens with no network at all. Bump CACHE on every deploy — the version is
 * what makes an update land. */
const CACHE = 'ulm-dojo-v2';
const ASSETS = [
  './', 'index.html', 'styles.css', 'app.js', 'data.js', 'review-core.js', 'review-data.js', 'manifest.webmanifest',
  'icons/icon-192.png', 'icons/icon-512.png', 'icons/icon-maskable-512.png',
  'icons/apple-touch-icon.png',
];

self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE)
      // addAll is all-or-nothing; add individually so one 404 cannot
      // leave the app uninstallable. Bypass the HTTP cache: verdicts are bound
      // to hashes, so the code and its data must come from the same deploy.
      .then(c => Promise.all(ASSETS.map(a => c.add(new Request(a, { cache: 'reload' })).catch(() => {}))))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      .then(ks => Promise.all(ks.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);

  // Google Fonts: cache opportunistically, never block the page on them.
  if (url.origin !== location.origin) {
    e.respondWith(
      caches.match(req).then(hit => hit || fetch(req).then(res => {
        const copy = res.clone();
        caches.open(CACHE).then(c => c.put(req, copy)).catch(() => {});
        return res;
      }).catch(() => hit))
    );
    return;
  }

  // Same-origin: cache-first, fall back to the shell for navigations.
  e.respondWith(
    caches.match(req).then(hit => hit || fetch(req).then(res => {
      const copy = res.clone();
      caches.open(CACHE).then(c => c.put(req, copy)).catch(() => {});
      return res;
    }).catch(() => req.mode === 'navigate' ? caches.match('index.html') : undefined))
  );
});
