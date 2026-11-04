import assert from 'node:assert/strict';
import { test } from 'node:test';
import { REVIEW } from '../review-data.js';
import { summarize } from '../review-core.js';

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

test('no sorry and no axioms in the source', () => {
  assert.deepEqual(REVIEW.sorries, {});
  assert.deepEqual(REVIEW.axioms, []);
  assert.deepEqual(REVIEW.warnings, []);
});
