import assert from 'node:assert/strict';
import { test } from 'node:test';
import { buildIndex, headerEnd, maskComments, parseFile, reviewPayload } from '../scripts/lean-extract.mjs';
import {
  latestEvents, lineDiff, makeEvent, nextInQueue, parseLedger, serializeLedger, staleReason,
  statusOf, summarize,
} from '../review-core.js';

const BASE = `import Mathlib

/-! Module doc mentioning def notADecl -/

variable (p : ℕ)

/-- The base. -/
def base (x : ℕ) : ℕ := x + p

-- a line comment with def alsoNotADecl
/-- Built on base. -/
def built (x : ℕ) : ℕ :=
  base p x

/-- Not used by the target. -/
def bystander : ℕ := 3

structure Holder where
  val : ℕ

instance : Inhabited Holder := ⟨⟨0⟩⟩

noncomputable instance builtInst : Inhabited (Fin (built 1 2 + 1)) := ⟨0⟩

namespace Holder

/-- Inside a namespace. -/
def twice (h : Holder) : ℕ := h.val + h.val

end Holder

theorem main_thm (x : ℕ) : built p x = x + p := by
  simp [built, base, bystander]

lemma helper : bystander = 3 := rfl
`;

const index = (src = BASE) => buildIndex({ 'Lib/A.lean': src });
const data = (src = BASE, extra = {}) => ({
  repo: 'o/r', rev: 'abc', toolchain: 'lean:1', mathlib: 'm1',
  ...reviewPayload(index(src), ['main_thm']), ...extra,
});
const decl = (d, n) => d.decls.find(x => x.name === n);
const approve = (d, n, at = 1000) => makeEvent(decl(d, n), 'approved', '', d, at);
const stateAfter = (src, name) => {
  const before = data();
  const after = data(src);
  return statusOf(decl(after, name), latestEvents([approve(before, name)], 'o/r'), after);
};

test('comments never produce declarations, and docstrings attach', () => {
  const { decls } = parseFile('A.lean', BASE);
  const names = decls.map(d => d.name);
  assert.ok(!names.includes('notADecl') && !names.includes('alsoNotADecl'));
  assert.equal(decls.find(d => d.name === 'base').doc, 'The base.');
  assert.equal(decls.find(d => d.name === 'bystander').code, 'def bystander : ℕ := 3');
});

test('nested block comments and strings are handled', () => {
  const { masked } = maskComments('/- a /- b -/ c -/ def x := "-- not comment" -- yes\n');
  assert.ok(masked.includes('def x := "-- not comment"'));
  assert.ok(!masked.includes('yes') && !masked.includes(' a '));
});

test('headerEnd finds the depth-zero assignment', () => {
  const t = 'foo (x : ℕ := 1) : ℕ := x';
  assert.equal(t.slice(headerEnd(t)), ':= x');
});

test('namespaces qualify names and anonymous instances get ids', () => {
  const ix = index();
  assert.ok(ix.byName.has('Holder.twice'));
  assert.ok(ix.byName.has('instance#Lib/A.lean#1'));
});

test('the trust base follows the statement, not the proof', () => {
  const d = data();
  const names = summarize('main_thm', [], d).base.map(x => x.decl.name);
  assert.ok(names.includes('built') && names.includes('base'));
  assert.ok(!names.includes('bystander'), 'mentioned only in the proof');
  assert.equal(names.at(-1), 'main_thm');
  assert.ok(names.indexOf('base') < names.indexOf('built'), 'leaves first');
});

test('an instance about a definition joins its closure', () => {
  const d = data();
  assert.ok(decl(d, 'main_thm').closure.includes('builtInst'));
  assert.ok(decl(d, 'bystander').closure.length === 0);
});

test('theorem payload shows the statement only', () => {
  const code = decl(data(), 'main_thm').code;
  assert.ok(code.startsWith('theorem main_thm') && !code.includes('simp'));
});

test('other theorems are not reviewable', () => {
  assert.equal(decl(data(), 'helper'), undefined);
});

test('an approval stays current when nothing formal changed', () => {
  const reformat = BASE.replace('def base (x : ℕ) : ℕ := x + p', 'def base (x : ℕ) : ℕ :=\n    x   + p  -- tidy');
  assert.equal(stateAfter(reformat, 'base').state, 'approved');
  assert.equal(stateAfter(BASE.replace('The base.', 'Reworded.'), 'base').state, 'approved');
});

test('editing a proof does not invalidate the statement', () => {
  const s = BASE.replace('simp [built, base, bystander]', 'omega');
  assert.equal(stateAfter(s, 'main_thm').state, 'approved');
});

test('editing a definition makes it stale, naming the reason', () => {
  const s = stateAfter(BASE.replace('x + p', 'x * p'), 'base');
  assert.equal(s.state, 'stale');
  assert.deepEqual(s.stale.map(r => r.type), ['own']);
});

test('editing a dependency makes its users stale, naming the dependency', () => {
  const s = stateAfter(BASE.replace('x + p', 'x * p'), 'built');
  assert.equal(s.state, 'stale');
  assert.deepEqual(s.stale, [{ type: 'deps', changed: ['base'] }]);
});

test('editing a theorem statement makes it stale', () => {
  assert.equal(stateAfter(BASE.replace('= x + p', '= p + x'), 'main_thm').state, 'stale');
});

test('changing a variable in scope makes declarations stale', () => {
  assert.equal(stateAfter(BASE.replace('variable (p : ℕ)', 'variable (p : ℤ)'), 'base').state, 'stale');
});

test('changing an attached instance makes dependents stale', () => {
  const s = stateAfter(BASE.replace('built 1 2 + 1)) := ⟨0⟩', 'built 1 2 + 1)) := ⟨1⟩'), 'main_thm');
  assert.equal(s.state, 'stale');
  assert.deepEqual(s.stale[0].changed, ['builtInst']);
});

test('adding a dependency makes the user stale', () => {
  const s = BASE.replace('  base p x', '  base p x + bystander');
  const st = stateAfter(s, 'built');
  assert.equal(st.state, 'stale');
  assert.ok(st.stale.find(r => r.type === 'deps').changed.includes('bystander'));
});

test('a toolchain or Mathlib bump makes approvals stale', () => {
  const before = data();
  const after = data(BASE, { toolchain: 'lean:2', mathlib: 'm2' });
  const reasons = staleReason(decl(after, 'base'), approve(before, 'base'), after).map(r => r.type);
  assert.deepEqual(reasons, ['toolchain', 'mathlib']);
});

test('the latest verdict wins and history is kept', () => {
  const d = data();
  const events = [approve(d, 'base', 1), makeEvent(decl(d, 'base'), 'flagged', 'wrong sign', d, 2)];
  assert.equal(statusOf(decl(d, 'base'), latestEvents(events, 'o/r'), d).state, 'flagged');
  assert.equal(events.length, 2);
});

test('a flag needs a note', () => {
  const d = data();
  assert.throws(() => makeEvent(decl(d, 'base'), 'flagged', '  ', d));
});

test('trust needs every item approved and current', () => {
  const d = data();
  const names = summarize('main_thm', [], d).base.map(x => x.decl.name);
  const events = names.map((n, i) => approve(d, n, i + 1));
  assert.equal(summarize('main_thm', events.slice(1), d).trusted, false);
  assert.equal(summarize('main_thm', events, d).trusted, true);
  events.push(makeEvent(decl(d, 'base'), 'flagged', 'no', d, 99));
  assert.equal(summarize('main_thm', events, d).trusted, false);
  const edited = data(BASE.replace('x + p', 'x * p'));
  assert.equal(summarize('main_thm', names.map((n, i) => approve(d, n, i + 1)), edited).trusted, false);
});

test('the queue offers stale first, skips flagged, and leaves unsure for last', () => {
  const d = data();
  const names = summarize('main_thm', [], d).base.map(x => x.decl.name);
  assert.equal(nextInQueue('main_thm', [], d).name, names[0]);
  const flagged = makeEvent(decl(d, names[0]), 'flagged', 'bad', d, 1);
  assert.equal(nextInQueue('main_thm', [flagged], d).name, names[1]);
  const unsure = makeEvent(decl(d, names[1]), 'unsure', '', d, 2);
  assert.equal(nextInQueue('main_thm', [flagged, unsure], d).name, names[2]);
  const edited = data(BASE.replace('x + p', 'x * p'));
  const baseEvent = approve(d, 'base', 3);
  assert.equal(nextInQueue('main_thm', [baseEvent], edited).name, 'base');
  assert.equal(nextInQueue('main_thm', names.map((n, i) => approve(d, n, i + 1)), d), null);
});

test('ledger round-trips and import drops malformed events', () => {
  const d = data();
  const text = serializeLedger([approve(d, 'base')], d, 5);
  assert.equal(parseLedger(text).events.length, 1);
  const hostile = JSON.parse(text);
  hostile.events.push({ id: 1, verdict: 'approved' }, { ...hostile.events[0], verdict: 'owned' },
    { ...hostile.events[0], code: 7 }, { ...hostile.events[0], note: {} }, { ...hostile.events[0], closure: [] });
  assert.deepEqual(
    (({ events, skipped }) => [events.length, skipped])(parseLedger(hostile)), [1, 5]);
  assert.throws(() => parseLedger('{"format":"other","events":[]}'));
});

test('lineDiff marks only the changed line', () => {
  assert.deepEqual(lineDiff('a\nb\nc', 'a\nB\nc').map(x => x.t).join(''), ' -+ ');
});

test('verdict snapshot records what was read', () => {
  const d = data();
  const e = approve(d, 'built');
  assert.equal(e.code, decl(d, 'built').code);
  assert.equal(e.toolchain, 'lean:1');
  assert.equal(e.closure.base, decl(d, 'base').ownHash);
});
