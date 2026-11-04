/* The publication gate, run as the real CLI against throwaway repos. Every case here
 * refuses before reaching GitHub, so no network is needed. */
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const SCRIPT = join(ROOT, 'scripts/build-review.mjs');
const git = (cwd, ...a) => execFileSync('git', ['-c', 'user.email=t@t', '-c', 'user.name=t', ...a], { cwd, encoding: 'utf8' });

function repo() {
  const dir = mkdtempSync(join(tmpdir(), 'dojo-gate-'));
  const r = join(dir, 'r');
  mkdirSync(join(r, 'Lib'), { recursive: true });
  writeFileSync(join(r, 'Lib/A.lean'), 'def d : Nat := 1\ntheorem t : d = 1 := rfl\n');
  writeFileSync(join(r, 'lean-toolchain'), 'leanprover/lean4:test\n');
  writeFileSync(join(r, 'lake-manifest.json'), '{"packages":[]}');
  git(r, 'init', '-q');
  git(r, 'add', '-A');
  git(r, 'commit', '-qm', 'x');
  return { dir, r, out: join(dir, 'o.js') };
}
const run = (...a) => spawnSync('node', [SCRIPT, ...a], { encoding: 'utf8' });
const refused = (res, re) => { assert.notEqual(res.status, 0); assert.match(res.stderr, re); };

test('a folder that is not the named repo is refused', () => {
  const { r, out } = repo();
  refused(run(r, '--slug', 'elanroth/UlmsTheorem', '--target', 't', '--out', out), /no GitHub remote/);
  git(r, 'remote', 'add', 'origin', 'https://github.com/elanroth/private-thing.git');
  refused(run(r, '--slug', 'elanroth/UlmsTheorem', '--target', 't', '--out', out), /no GitHub remote/);
  assert.ok(!existsSync(out));
});

test('a source path outside the repo is refused', () => {
  const { r, out } = repo();
  refused(run(r, '--slug', 'a/b', '--target', 't', '--lib', '../priv', '--out', out), /stay inside the repo/);
  refused(run(r, '--slug', 'a/b', '--target', 't', '--lib', '/etc', '--out', out), /stay inside the repo/);
});

test('only one target is accepted, since the app shows one', () => {
  const { r, out } = repo();
  refused(run(r, '--slug', 'a/b', '--target', 't', '--target', 'd', '--out', out), /one target/);
});

test('ignored and uncommitted files are never read', () => {
  const { r, out } = repo();
  writeFileSync(join(r, '.gitignore'), 'Lib/ignored.lean\n');
  writeFileSync(join(r, 'Lib/ignored.lean'), 'def IGNORED_SECRET : Nat := 1\n');
  writeFileSync(join(r, 'Lib/A.lean'), 'def WORKING_COPY_SECRET : Nat := 1\ndef d : Nat := 1\ntheorem t : d = 1 := rfl\n');
  const res = run(r, '--slug', 'a/b', '--target', 't', '--unchecked', '--out', out);
  assert.equal(res.status, 0, res.stderr);
  const text = readFileSync(out, 'utf8');
  assert.ok(!text.includes('IGNORED_SECRET') && !text.includes('WORKING_COPY_SECRET'));
});

test('unchecked output is stamped and cannot reach the shipped file by any name', () => {
  const { dir, r, out } = repo();
  assert.equal(run(r, '--slug', 'a/b', '--target', 't', '--unchecked', '--out', out).status, 0);
  assert.ok(readFileSync(out, 'utf8').includes('"unchecked": true'));
  const before = readFileSync(join(ROOT, 'review-data.js'), 'utf8');
  refused(run(r, '--slug', 'a/b', '--target', 't', '--unchecked'), /shipped/);
  refused(run(r, '--slug', 'a/b', '--target', 't', '--unchecked', '--out', join(ROOT, 'REVIEW-DATA.JS')), /shipped/);
  const link = join(dir, 'link.js');
  symlinkSync(join(ROOT, 'review-data.js'), link);
  refused(run(r, '--slug', 'a/b', '--target', 't', '--unchecked', '--out', link), /shipped/);
  assert.equal(readFileSync(join(ROOT, 'review-data.js'), 'utf8'), before);
});

test('unreadable Lean stops the build with its location', () => {
  const { r, out } = repo();
  writeFileSync(join(r, 'Lib/A.lean'), 'alias x := y\n');
  git(r, 'add', '-A');
  git(r, 'commit', '-qm', 'y');
  refused(run(r, '--slug', 'a/b', '--target', 't', '--unchecked', '--out', out), /Lib\/A\.lean:1: unrecognised command/);
});

test('the service worker precaches every file the app needs, and only touches its own caches', () => {
  const sw = readFileSync(join(ROOT, 'sw.js'), 'utf8');
  const assets = [...sw.match(/const ASSETS = \[([\s\S]*?)\];/)[1].matchAll(/'([^']+)'/g)].map(m => m[1]);
  for (const a of assets) if (a !== './') assert.ok(existsSync(join(ROOT, a)), a);
  const walk = (f, seen = new Set()) => {
    if (seen.has(f)) return seen;
    seen.add(f);
    for (const m of readFileSync(join(ROOT, f), 'utf8').matchAll(/from '\.\/([^']+)'/g)) walk(m[1], seen);
    return seen;
  };
  for (const f of walk('app.js')) assert.ok(assets.includes(f), f + ' missing from ASSETS');
  assert.match(sw, /k\.startsWith\(PREFIX\) && k !== CACHE/);
  assert.match(sw, /addAll/);
  assert.match(sw, /if \(res\.ok\)/);
});
