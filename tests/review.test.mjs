import assert from 'node:assert/strict';
import { test } from 'node:test';
import { buildIndex, headerEnd, maskComments, parseFile, reviewPayload } from '../scripts/lean-extract.mjs';
import {
  LEDGER_FORMAT, latestEvents, lineDiff, makeEvent, nextInQueue, nextTimestamp, parseLedger, planImport,
  serializeLedger, staleReason, statusOf, summarize,
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
  assert.ok(ix.decls.some(d => d.name.startsWith('instance#Lib/A.lean#')));
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
  assert.equal(nextInQueue('main_thm', [unsure, flagged], d, { after: names[2], includeUnsure: false }).name, names[3]);
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

/* ── regressions from the bug checks ───────────────────────────────── */

const one = src => buildIndex({ 'Lib/A.lean': src });
const stops = (src, re) => assert.throws(() => one(src), re);

test('a newer verdict wins even if the clock moved backwards', () => {
  const d = data();
  const later = approve(d, 'base', 5000);
  const at = nextTimestamp([later], 'o/r', 'base', 1000);
  assert.equal(at, 5001);
  const flag = makeEvent(decl(d, 'base'), 'flagged', 'wrong', d, at);
  assert.equal(statusOf(decl(d, 'base'), latestEvents([later, flag], 'o/r'), d).state, 'flagged');
});

test('import refuses future dates and conflicting ids', () => {
  const d = data();
  const good = approve(d, 'base', 1000);
  const ledger = events => ({ format: LEDGER_FORMAT, events });
  assert.equal(parseLedger(ledger([{ ...good, at: 9e15 }]), 1000).skipped, 1);
  assert.equal(parseLedger(ledger([{ ...good, at: 1e308 }]), 1000).skipped, 1);
  const dup = parseLedger(ledger([{ ...good, verdict: 'approved' }, { ...good, verdict: 'unsure' }]), 2000);
  assert.deepEqual([dup.events.length, dup.conflicts], [0, 1]);
  assert.equal(parseLedger(ledger([good, good]), 2000).events.length, 1);
});

test('planImport marks new events and never replaces stored ones', () => {
  const d = data();
  const a = approve(d, 'base', 1000);
  const plan = planImport([a, { ...a, id: 'x' }, { ...a, id: a.id, note: 'changed' }], [a]);
  assert.deepEqual(plan.fresh.map(e => [e.id, e.imported]), [['x', true]]);
  assert.deepEqual([plan.same, plan.conflicts], [1, 1]);
});

test('imported approvals are counted, and sorry blocks trust', () => {
  const d = data();
  const events = summarize('main_thm', [], d).base.map((x, i) => ({ ...approve(d, x.decl.name, i + 1), imported: true }));
  const s = summarize('main_thm', events, d);
  assert.equal(s.counts.imported, s.counts.total);
  assert.equal(s.trusted, true);
  decl(d, 'base').hasSorry = true;
  assert.equal(summarize('main_thm', events, d).trusted, false);
});

test('a changed "not sure" comes before new work', () => {
  const d = data();
  const ev = makeEvent(decl(d, 'built'), 'unsure', '', d, 1);
  const edited = data(BASE.replace('  base p x', '  base p (x + 1)'));
  assert.equal(nextInQueue('main_thm', [ev], edited).name, 'built');
});

test('a deep hash mismatch with no visible difference still expires', () => {
  const d = data();
  const ev = { ...approve(d, 'built'), deepHash: 'forged' };
  assert.equal(statusOf(decl(d, 'built'), latestEvents([ev], 'o/r'), d).state, 'stale');
});

test('a theorem statement is never cut at a let, match or absolute value', () => {
  const ix = one('def evil : Prop := True\ntheorem t : let x := 1; evil ∧ x = 1 := by simp\n');
  assert.ok(ix.byName.get('t').code.includes('evil ∧ x = 1'));
  assert.deepEqual(ix.byName.get('t').deps, ['evil']);
  const abs = one('def evil : Nat := 1\ntheorem t (n : Int) :\n  |n| = n + evil := by simp\n');
  assert.ok(abs.byName.get('t').code.includes('n + evil'));
  const pat = one('theorem t : ∀ n : Nat, n = n\n  | 0 => rfl\n  | _ => rfl\n');
  assert.ok(!pat.byName.get('t').code.includes('rfl'));
});

test('attribute on its own line belongs to the declaration, and changes its hash', () => {
  const a = one('def base : Nat := 1\n@[reducible]\ndef x : Nat := base\n');
  const b = one('def base : Nat := 1\n@[irreducible]\ndef x : Nat := base\n');
  assert.deepEqual(a.decls.map(d => d.name), ['base', 'x']);
  assert.notEqual(a.byName.get('x').ownHash, b.byName.get('x').ownHash);
});

test('char and raw string literals do not derail parsing', () => {
  const src = v => `def q : Char := '"'\ndef x : Nat := 1\ndef y : Nat := 2\ndef s : String := "-- " ++ toString ${v}\n`;
  assert.notEqual(one(src('x')).byName.get('s').ownHash, one(src('y')).byName.get('s').ownHash);
  assert.ok(one(src('x')).byName.get('s').deps.includes('x'));
  assert.deepEqual(one('def r : String := r"\\"\ndef u : Nat := 1\n').decls.map(d => d.name), ['r', 'u']);
});

test('a string containing Lean is not Lean', () => {
  const ix = one('def s : String := "\ndef ghost : Nat := 1\n"\ndef after : Nat := 2\n');
  assert.deepEqual(ix.decls.map(d => d.name), ['s', 'after']);
});

test('spaces inside a string are meaning', () => {
  assert.notEqual(one('def s := "a b"\n').byName.get('s').ownHash, one('def s := "a  b"\n').byName.get('s').ownHash);
});

test('a docstring on the same line does not hide the declaration', () => {
  const ix = one('/-- doc -/ def hidden : Nat := 1\ndef user : Nat := hidden\n');
  assert.deepEqual(ix.byName.get('user').deps, ['hidden']);
  assert.equal(ix.byName.get('hidden').doc, 'doc');
});

test('variable binders count as dependencies', () => {
  const ix = one('class R (n : Nat) : Prop\nvariable (n : Nat) [R n]\ntheorem t : n = n := rfl\n');
  assert.deepEqual(ix.byName.get('t').deps, ['R']);
});

test('names are resolved every plausible way', () => {
  const deps = (src, n = 'user') => one(src).byName.get(n).deps;
  assert.ok(deps('namespace M\ndef x : Nat := 1\nend M\nopen M in\ndef user : Nat := x\n').includes('M.x'));
  assert.ok(deps('namespace A\nnamespace M\ndef x : Nat := 1\nend M\nopen M\ndef user : Nat := x\nend A\n', 'A.user').includes('A.M.x'));
  assert.ok(deps('namespace M\ndef x : Nat := 1\nend M\nopen M renaming x → y\ndef user : Nat := y\n').includes('M.x'));
  assert.ok(deps('namespace M\ndef x : Nat := 1\nend M\nexport M (x)\ndef user : Nat := x\n').includes('M.x'));
  assert.ok(deps('def Foo.baz : Nat := 1\ndef Foo.user : Nat := baz\n', 'Foo.user').includes('Foo.baz'));
  assert.ok(deps('inductive Color\n  | red\nopen Color\ndef user : Color := red\n').includes('Color'));
  assert.ok(deps('structure S where\n  v : Nat\ndef S.g (s : S) : Nat := s.v\ndef user (s : S) : Nat := (s).g\n').includes('S.g'));
  const both = deps('def foo : Nat := 1\nnamespace M\ndef foo : Bool := true\nend M\nopen M\ndef user : Bool := foo\n');
  assert.ok(both.includes('foo') && both.includes('M.foo'));
  assert.ok(deps('def «hid den» : Nat := 1\ndef user : Nat := «hid den»\n').includes('«hid den»'));
  assert.ok(deps('def hidden.{u} : Type u := PUnit\ndef user := hidden\n').includes('hidden'));
});

test('instances declared by attribute are attached', () => {
  const a = one('class C where\n  v : Nat\n@[instance] def i1 : C := ⟨1⟩\ndef u : Nat := C.v\n');
  assert.ok(a.byName.get('u').closure.includes('i1'));
  const b = one('class C where\n  v : Nat\ndef i1 : C := ⟨1⟩\nattribute [instance] i1\ndef u : Nat := C.v\n');
  assert.ok(b.byName.get('u').closure.includes('i1'));
  assert.ok(one('class C where\n  v : Nat\nlocal instance i2 : C := ⟨1⟩\ndef u : Nat := C.v\n').byName.get('u').closure.includes('i2'));
});

test('local notation counts as a dependency of what follows', () => {
  const ix = one('def hidden : Nat := 1\nlocal notation "𝔸" => hidden\ndef user : Nat := 𝔸\n');
  assert.deepEqual(ix.byName.get('user').deps, ['hidden']);
});

test('namespaces split by component, and nothing leaks', () => {
  const ix = one('namespace A.B\ndef x : Nat := 1\nend B\ndef y : Nat := 2\nend A\ndef z : Nat := 3\n');
  assert.deepEqual(ix.decls.map(d => d.name), ['A.B.x', 'A.y', 'z']);
});

test('deriving stays with its declaration', () => {
  const a = one('inductive T\n  | a\nderiving DecidableEq\ndef u : Nat := 1\n');
  const b = one('inductive T\n  | a\ndef u : Nat := 1\n');
  assert.notEqual(a.byName.get('T').ownHash, b.byName.get('T').ownHash);
});

test('open-in only applies to the next command', () => {
  const ix = one('open Nat in\n#check succ\ndef a : Nat := 1\n');
  assert.ok(!ix.byName.get('a').code.includes('open'));
});

test('anonymous instance ids do not shift when another is added', () => {
  const src = 'class C where\n  v : Nat\nclass D where\n  v : Nat\ninstance : D := ⟨1⟩\n';
  const before = one(src).decls.find(d => d.name.startsWith('instance#')).name;
  const after = one('class C where\n  v : Nat\nclass D where\n  v : Nat\ninstance : C := ⟨1⟩\ninstance : D := ⟨1⟩\n').decls.map(d => d.name);
  assert.ok(after.includes(before));
});

test('unknown or unfollowable Lean stops the build', () => {
  stops('alias foo := bar\n', /unrecognised command/);
  stops('irreducible_def x : Nat := 1\n', /unrecognised command/);
  stops('namespace N\n  def hidden : Nat := 1\nend N\n', /indented command/);
  stops('mutual\n  def a : Nat := 1\nend\n', /mutual|indented/);
  stops('notation "𝔸" => 1\n', /non-local notation/);
  stops('macro "x" : term => `(1)\n', /macro/);
  stops('deriving instance Repr for Nat\n', /deriving instance/);
  stops('namespace M\ndef x : Nat := 1\nend M\nopen M in def hidden : Nat := x\n', /on one line/);
  stops('namespace N\ndef x : Nat := 1\n', /unclosed/);
  stops('end N\n', /without a matching/);
  assert.throws(() => buildIndex({ 'A.lean': 'def h : Nat := 1\n', 'B.lean': 'def h : Nat := 2\n' }), /declared twice/);
});

test('sorry variants and risky features are reported', () => {
  const ix = one('def a : Nat := sorry\ntheorem t : True := by admit\ndef b : Nat := by native_decide\n');
  assert.equal(ix.sorries['Lib/A.lean'], 2);
  assert.deepEqual(ix.risky['Lib/A.lean'], ['native_decide']);
});

test('module references are collected per file', () => {
  const ix = one('/-!\n# T\n\n## References\n- Fuchs, Chapter 11\n- Kaplansky, Theorem 14\n-/\ndef a : Nat := 1\n');
  assert.deepEqual(ix.refs['Lib/A.lean'], ['Fuchs, Chapter 11', 'Kaplansky, Theorem 14']);
});
