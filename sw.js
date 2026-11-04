/* Ulm Dojo service worker.
 * Precache the whole app on install; serve cache-first so the installed PWA
 * opens with no network at all. Bump CACHE on every deploy — the version is
 * what makes an update land. */
const CACHE = 'ulm-dojo-v3';
const PREFIX = 'ulm-dojo-';
const ASSETS = [
  './', 'index.html', 'styles.css', 'app.js', 'data.js', 'review-core.js', 'review-data.js',
  'review-sources.js', 'manifest.webmanifest',
  'icons/icon-192.png', 'icons/icon-512.png', 'icons/icon-maskable-512.png',
  'icons/apple-touch-icon.png',
];

self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE)
      // addAll is all-or-nothing on purpose: a failed install leaves the working
      // version in charge. Bypass the HTTP cache: verdicts are bound to hashes,
      // so the code and its data must come from the same deploy.
      .then(c => c.addAll(ASSETS.map(a => new Request(a, { cache: 'reload' }))))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      // The origin is shared with other apps, so only ever delete our own caches.
      .then(ks => Promise.all(ks.filter(k => k.startsWith(PREFIX) && k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

/* Serve from this version's cache only, and never store a failed response. */
async function cacheFirst(req, fallback) {
  const cache = await caches.open(CACHE);
  const hit = await cache.match(req);
  if (hit) return hit;
  try {
    const res = await fetch(req);
    if (res.ok) cache.put(req, res.clone()).catch(() => {});
    return res;
  } catch (err) {
    const alt = fallback && await cache.match(fallback);
    if (alt) return alt;
    throw err;
  }
}

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  e.respondWith(cacheFirst(req, req.mode === 'navigate' ? 'index.html' : null));
});
