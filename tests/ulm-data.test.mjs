import assert from 'node:assert/strict';
import { test } from 'node:test';
import { REVIEW } from '../review-data.js';
import { summarize } from '../review-core.js';
import { SOURCES } from '../review-sources.js';

const base = () => summarize('ulm_theorem', [], REVIEW).base.map(x => x.decl.name);

test('shipped data comes from the public Ulm repo', () => {
  assert.equal(REVIEW.repo, 'elanroth/UlmsTheorem');
  assert.match(REVIEW.rev, /^[0-9a-f]{40}$/);
  for (const d of REVIEW.decls) assert.ok(d.file.startsWith('Lib/'));
});

test('the trust base holds what the statement rests on', () => {
  const names = base();
  for (const n of ['IsReducedPGroup', 'IsPReduced', 'IsPrimaryPGroup', 'ulmInvariant', 'ulmQuotient',
    'ulmDenSubmodule', 'pSocleAt', 'pSocle', 'ulmSubgroup', 'pImage']) {
    assert.ok(names.includes(n), n);
  }
  assert.equal(names.at(-1), 'ulm_theorem');
});

test('near-misses used only elsewhere stay out', () => {
  const names = base();
  for (const n of ['layerInvariant', 'layerQuotient', 'IsPSeparable', 'hillInvariant']) {
    assert.ok(!names.includes(n), n);
  }
});

test('the theorem payload hides the proof', () => {
  const t = REVIEW.decls.find(d => d.name === 'ulm_theorem');
  assert.ok(t.code.includes('Nonempty (G ≃+ H)') && !t.code.includes('constructor'));
});

test('no sorry, axioms or risky features in the source', () => {
  assert.deepEqual(REVIEW.sorries, {});
  assert.deepEqual(REVIEW.axioms, []);
  assert.deepEqual(REVIEW.risky, {});
});

test('shipped data is the real thing', () => {
  assert.equal(REVIEW.unchecked, undefined);
  assert.equal(REVIEW.targets.length, 1);
});

test('every source passage belongs to a real declaration behind the theorem', () => {
  const roots = new Set(REVIEW.decls.filter(d => d.root).map(d => d.name));
  for (const [name, s] of Object.entries(SOURCES)) {
    assert.ok(roots.has(name), name);
    assert.ok(s.cite && s.passage && ['quote', 'paraphrase'].includes(s.kind), name);
    assert.ok(s.passage.split(/\s+/).length <= 30, name + ' is too long for a public page');
  }
  assert.ok(SOURCES.ulm_theorem.passage.startsWith('Two reduced countable primary'));
});
