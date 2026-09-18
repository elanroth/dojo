// Generates the PWA icons with no image dependencies: raw RGBA -> PNG via zlib.
// The mark is the Ulm filtration G ⊇ pG ⊇ p²G ⊇ … drawn as a descending stair.
// Run: node scripts/make-icons.mjs
import { deflateSync } from 'node:zlib';
import { writeFileSync, mkdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');

const crcTable = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
const crc32 = buf => {
  let c = -1;
  for (let i = 0; i < buf.length; i++) c = crcTable[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
};
const chunk = (type, data) => {
  const len = Buffer.alloc(4);
  len.writeUInt32BE(data.length);
  const td = Buffer.concat([Buffer.from(type, 'ascii'), data]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(td));
  return Buffer.concat([len, td, crc]);
};
function png(width, height, rgba) {
  const raw = Buffer.alloc((width * 4 + 1) * height);
  for (let y = 0; y < height; y++) {
    raw[y * (width * 4 + 1)] = 0; // filter: none
    rgba.copy(raw, y * (width * 4 + 1) + 1, y * width * 4, (y + 1) * width * 4);
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr[8] = 8;  // bit depth
  ihdr[9] = 6;  // truecolour + alpha
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk('IHDR', ihdr),
    chunk('IDAT', deflateSync(raw, { level: 9 })),
    chunk('IEND', Buffer.alloc(0)),
  ]);
}

const hex = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
const GROUND = hex('#2c3c22');   // deep olive — Folio's room colour, darkened
const MARK   = hex('#dfe8c6');   // pale chalk

// Four descending bars: each step is shorter and inset, the way p^α·G shrinks.
// Drawn in a 0..1 coordinate space so it scales to any size.
const BARS = [
  { x: 0.20, y: 0.250, w: 0.60, h: 0.085 },
  { x: 0.20, y: 0.383, w: 0.46, h: 0.085 },
  { x: 0.20, y: 0.516, w: 0.32, h: 0.085 },
  { x: 0.20, y: 0.649, w: 0.18, h: 0.085 },
];

function render(size, { maskable }) {
  const buf = Buffer.alloc(size * size * 4);
  // Maskable icons get cropped to a circle by the launcher, so the mark is
  // scaled into the central safe zone rather than filling the square.
  const k = maskable ? 0.8 : 1.0;
  const off = (1 - k) / 2;
  const radius = maskable ? 0 : size * 0.22; // full-bleed for maskable, rounded otherwise

  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4;
      // rounded-rect mask on the ground
      let inside = true;
      if (radius > 0) {
        const cx = Math.min(Math.max(x + 0.5, radius), size - radius);
        const cy = Math.min(Math.max(y + 0.5, radius), size - radius);
        inside = (x + 0.5 - cx) ** 2 + (y + 0.5 - cy) ** 2 <= radius * radius;
      }
      let [r, g, b] = GROUND;
      let a = inside ? 255 : 0;

      const u = (x / size - off) / k;
      const v = (y / size - off) / k;
      for (const bar of BARS) {
        if (u >= bar.x && u <= bar.x + bar.w && v >= bar.y && v <= bar.y + bar.h) {
          [r, g, b] = MARK;
          break;
        }
      }
      buf[i] = r; buf[i + 1] = g; buf[i + 2] = b; buf[i + 3] = a;
    }
  }
  return png(size, size, buf);
}

mkdirSync(join(ROOT, 'icons'), { recursive: true });
const out = [
  ['icons/icon-192.png', 192, { maskable: false }],
  ['icons/icon-512.png', 512, { maskable: false }],
  ['icons/icon-maskable-512.png', 512, { maskable: true }],
  ['icons/apple-touch-icon.png', 180, { maskable: false }],
];
for (const [name, size, opts] of out) {
  const data = render(size, opts);
  writeFileSync(join(ROOT, name), data);
  console.log(name.padEnd(32), size + 'px', (data.length / 1024).toFixed(1) + ' KB');
}
