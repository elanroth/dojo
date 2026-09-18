/* Ground truth for the dojo.
 *
 * Every project signature, import edge and declaration count below was quoted
 * verbatim from disk. Two Mathlib entries (Module.rank, Ordinal) carry
 * unverified paths and say so in their own `warn` field; the AddSubgroup.comap
 * and AddSubgroup.subtype signatures are one-line renderings of multi-line
 * to_additive source, also flagged. Sources:
 *   - project Lean  : ~/pure/research/ulm  (elanroth/UlmsTheorem, PUBLIC)
 *                     toolchain leanprover/lean4:v4.30.0-rc1
 *   - Mathlib       : that repo's pinned .lake/packages/mathlib, commit 389a421660
 *
 * PUBLICATION RULE: this file ships to a public web page. Only UlmsTheorem
 * content may appear here. research/ACM, acm-v2-proofs and acm-v3-proofs are
 * private repositories and must never be quoted in this project.
 */

export const MATHLIB_REV = '389a421660';
export const TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc1';
export const REPO = 'elanroth/UlmsTheorem';

export const GLOSSARY = {
  ulmInvariant: {
    qual: 'ulmInvariant', origin: 'project', file: 'Lib/PGroups/UlmInvariants.lean:108',
    sig: 'noncomputable def ulmInvariant {G : Type*} [AddCommGroup G]\n    (α : Ordinal) : Cardinal :=\n  Module.rank (ZMod p) (ulmQuotient p α (G := G))',
    gloss: 'The classical Ulm invariant f_G(α) — the ℤ/pℤ-dimension of P_α / P_{α+1}, where P_α is the p-socle cut down to stage α of the filtration. This is the invariant Ulm’s theorem is about.',
    warn: 'Not the same as layerInvariant. See Decide.',
  },
  layerInvariant: {
    qual: 'layerInvariant', origin: 'project', file: 'Lib/PGroups/UlmInvariants.lean:79',
    sig: 'noncomputable def layerInvariant {G : Type*} [AddCommGroup G]\n    (α : Ordinal) : Cardinal :=\n  Module.rank (ZMod p) (layerQuotient p α (G := G))',
    gloss: 'The raw filtration-layer rank dim(G_α / G_{α+1}). Useful auxiliary data — but the docstring on the underlying layerQuotient (:39–41) says it “is not the classical Ulm invariant”.',
    warn: 'Easy to mistake for the real thing. The quotient is taken in G, not in the socle.',
  },
  pSocleAt: {
    qual: 'pSocleAt', origin: 'project', file: 'Lib/PGroups/Socle.lean:35',
    sig: 'noncomputable def pSocleAt (α : Ordinal) : AddSubgroup G :=\n  pSocle p ⊓ ulmSubgroup p α',
    gloss: 'P_α = the elements killed by p that also survive to stage α of the filtration. The meet of the p-socle and the α-th Ulm subgroup.',
    warn: null,
  },
  pSocle: {
    qual: 'pSocle', origin: 'project', file: 'Lib/PGroups/Socle.lean:14',
    sig: 'def pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where\n  carrier   := {x | p • x = 0}',
    gloss: 'The p-socle: everything of order dividing p. A ℤ/pℤ-vector space, which is why ranks make sense.',
    warn: null,
  },
  ulmSubgroup: {
    qual: 'ulmSubgroup', origin: 'project', file: 'Lib/PGroups/UlmSubgroups.lean:17',
    sig: 'noncomputable def ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :\n    AddSubgroup G :=\n  α.limitRecOn\n    ⊤\n    (fun _β Hβ ↦ pImage p Hβ)\n    (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)',
    gloss: 'p^α·G, defined by transfinite recursion: G at 0, multiply by p at successors, intersect at limits. This is where the ordinals enter — it is not an elementary construction.',
    warn: null,
  },
  ulmQuotient: {
    qual: 'ulmQuotient', origin: 'project', file: 'Lib/PGroups/UlmInvariants.lean:91',
    sig: 'abbrev ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :\n    Type _ :=\n  (pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α',
    gloss: 'P_α / P_{α+1} — the thing whose dimension is the Ulm invariant.',
    warn: null,
  },
  Ordinal: {
    qual: 'Ordinal', origin: 'mathlib', file: 'Mathlib/SetTheory/Ordinal/Basic.lean',
    sig: '-- the filtration is indexed by Ordinal',
    gloss: 'Order types of well-ordered sets. The Ulm filtration runs through the ordinals, not just ℕ — this is the reason the formalization is not elementary.',
    warn: 'File path is the conventional home for this declaration; I did not confirm the exact line in the pinned checkout.',
  },
  'Ordinal.limitRecOn': {
    qual: 'Ordinal.limitRecOn', origin: 'mathlib', file: 'Mathlib/SetTheory/Ordinal/Arithmetic.lean',
    sig: 'def limitRecOn {motive : Ordinal → Sort*} (o : Ordinal)\n    (zero : motive 0) (succ : ∀ o, motive o → motive (succ o))\n    (limit : ∀ o, IsSuccLimit o → (∀ o’ < o, motive o’) → motive o) : motive o',
    gloss: 'Transfinite recursion: to define something at every ordinal, give the zero case, the successor step, and the limit step. ulmSubgroup is built with exactly this.',
    warn: null,
  },
  ZMod: {
    qual: 'ZMod', origin: 'mathlib', file: 'Mathlib/Data/ZMod/Defs.lean',
    sig: 'def ZMod : ℕ → Type\n  | 0     => ℤ\n  | n + 1 => Fin (n + 1)',
    gloss: 'ℤ/nℤ, defined by cases so that ZMod 0 is ℤ itself. Here p is prime, so ZMod p is a field and “rank” means vector-space dimension.',
    warn: null,
  },
  'Module.rank': {
    qual: 'Module.rank', origin: 'mathlib', file: 'Mathlib/LinearAlgebra/Dimension/… (not pinned)',
    sig: 'Module.rank (R) (M) : Cardinal',
    gloss: 'The dimension of a module as a cardinal — the supremum of sizes of linearly independent sets. Cardinal-valued, so it works for infinite-dimensional socle quotients.',
    warn: 'I confirmed Module.rank is used in the pinned Mathlib (e.g. Mathlib/Analysis/RCLike/Lemmas.lean:40) but could not locate its definition site by grep. Treat the path as unverified.',
  },
  'AddCommGroup.zmodModule': {
    qual: 'AddCommGroup.zmodModule', origin: 'mathlib', file: 'Mathlib/Algebra/Module/ZMod.lean:44',
    sig: 'abbrev AddCommGroup.zmodModule {G : Type*} [AddCommGroup G] (h : ∀ (x : G), n • x = 0) :\n    Module (ZMod n) G',
    gloss: 'Upgrades an abelian group where every element is killed by n into a ZMod n-module. This is the bridge that lets you say “dimension” about a socle quotient.',
    warn: null,
  },
  'AddSubgroup.comap': {
    qual: 'AddSubgroup.comap', origin: 'mathlib', file: 'Mathlib/Algebra/Group/Subgroup/Map.lean:72',
    sig: '@[to_additive] def Subgroup.comap {N : Type*} [Group N] (f : G →* N) (H : Subgroup N) : Subgroup G',
    gloss: 'Preimage of a subgroup along a homomorphism. Used to view P_{α+1} as sitting inside P_α.',
    warn: 'Generated by to_additive from Subgroup.comap — searching Mathlib source for “def AddSubgroup.comap” finds nothing. Search the multiplicative name. The line above is a one-line rendering; the source reads “def comap” inside namespace Subgroup, under a multi-line @[to_additive] at :69–71.',
  },
  'AddSubgroup.subtype': {
    qual: 'AddSubgroup.subtype', origin: 'mathlib', file: 'Mathlib/Algebra/Group/Subgroup/Defs.lean:222',
    sig: '@[to_additive (attr := coe)] protected def Subgroup.subtype : H →* G',
    gloss: 'The inclusion homomorphism from a subgroup back into the group.',
    warn: 'Also to_additive-generated. Same search caveat as AddSubgroup.comap. The line above is a one-line rendering; the source reads “protected def subtype” with the attribute on :220–221.',
  },
};

export const READING = {
  source: 'Fuchs, Abelian Groups, Ch. 11 §1 · Kaplansky, Infinite Abelian Groups, Thm 14',
  english: [
    'For a prime p and a reduced abelian p-group G, the <b>Ulm invariant</b> at ordinal α is the {ZMod}-dimension of {ulmQuotient}, where {pSocleAt} is the p-socle cut down to stage α of the filtration.',
    'The filtration itself, {ulmSubgroup}, is built by transfinite recursion: it starts at all of G, multiplies by p at each successor, and intersects at each limit stage.',
    'The file also keeps a second, similar-looking quantity — {layerInvariant}, the rank of G_α / G_{α+1}. It is useful auxiliary data, but it is <b>not</b> the classical Ulm invariant.',
  ],
  lean: [
    { t: '/-- The classical Ulm invariant `f_G(α) = dim_{ℤ/pℤ}(P_α / P_{α+1})`. -/\n' },
    { t: 'noncomputable def ' }, { t: 'ulmInvariant', k: 'ulmInvariant' },
    { t: ' {G : Type*} [AddCommGroup G]\n    (α : Ordinal) : Cardinal :=\n  ' },
    { t: 'Module.rank', k: 'Module.rank' }, { t: ' (' }, { t: 'ZMod', k: 'ZMod' },
    { t: ' p) (' }, { t: 'ulmQuotient', k: 'ulmQuotient' }, { t: ' p α (G := G))' },
  ],
  leanSrc: 'Lib/PGroups/UlmInvariants.lean:107–110',
};

export const QUESTIONS = [
  {
    q: 'Which definition is the one Ulm’s theorem is actually about?',
    opts: [
      { t: 'ulmInvariant — rank of P_α / P_{α+1}', ok: true,
        why: 'Right. The quotient is taken inside the socle P_α = pSocle ⊓ ulmSubgroup, not inside G.' },
      { t: 'layerInvariant — rank of G_α / G_{α+1}', ok: false,
        why: 'This is the raw filtration layer. The docstring on its underlying layerQuotient says it “is not the classical Ulm invariant”.' },
    ],
    cite: 'Lib/PGroups/UlmInvariants.lean:39–41, :108',
  },
  {
    q: 'ulmSubgroup is defined by α.limitRecOn. What does that commit you to?',
    opts: [
      { t: 'A transfinite recursion with a separate limit case', ok: true,
        why: 'Yes — zero, successor and limit are three distinct obligations. Any lemma about it usually splits the same three ways.' },
      { t: 'Ordinary induction on ℕ, lifted to ordinals', ok: false,
        why: 'No. Limit ordinals have no predecessor, so the limit stage (an ⨅ over β < o) is genuinely extra structure.' },
    ],
    cite: 'Lib/PGroups/UlmSubgroups.lean:17–22',
  },
  {
    q: 'Why can we speak of the dimension of P_α / P_{α+1} at all?',
    opts: [
      { t: 'Every element is killed by p, so it is a ℤ/pℤ-vector space', ok: true,
        why: 'Correct — and the repo proves exactly this (ulmQuotient_orderOf_dvd_p) before installing the Module instance.' },
      { t: 'Because G is countable', ok: false,
        why: 'Countability is used in the hard direction of the theorem, not to make the quotient a vector space.' },
    ],
    cite: 'Lib/PGroups/UlmInvariants.lean:96–105',
  },
  {
    q: 'Searching Mathlib source for `def AddSubgroup.comap` returns nothing. Why?',
    opts: [
      { t: 'It is generated by @[to_additive] from Subgroup.comap', ok: true,
        why: 'Right. Many additive names exist only as to_additive images — search the multiplicative name in source, or use the docs.' },
      { t: 'It was removed from this Mathlib revision', ok: false,
        why: 'No — the Ulm files use it and compile against this pin (' + MATHLIB_REV + ').' },
    ],
    cite: 'Mathlib/Algebra/Group/Subgroup/Map.lean:69–72',
  },
];

/* Real import DAG of ~/pure/research/ulm/Lib. Declaration counts are
 * `grep -cE '^(noncomputable )?(abbrev|def|theorem|lemma) '` per file;
 * every file greps 0 for `sorry`. */
export const DAG = [
  { id: 'Lib.Basic', dep: [], d: 0, role: 'Ambient imports only.' },
  { id: 'Lib.PGroups.Basic', dep: ['Lib.Basic'], d: 0, role: 'Re-export layer.' },
  { id: 'Lib.PGroups.Subgroups', dep: ['Lib.PGroups.Basic'], d: 7, role: 'pImage and subgroup plumbing.' },
  { id: 'Lib.PGroups.UlmSubgroups', dep: ['Lib.PGroups.Subgroups'], d: 11, role: 'p^α·G by transfinite recursion. The filtration.' },
  { id: 'Lib.PGroups.Heights', dep: ['Lib.PGroups.UlmSubgroups'], d: 10, role: 'Height function over the filtration.' },
  { id: 'Lib.PGroups.Defs', dep: ['Lib.PGroups.Heights'], d: 0, role: 'IsReducedPGroup and friends.' },
  { id: 'Lib.PGroups.Socle', dep: ['Lib.PGroups.Defs'], d: 7, role: 'pSocle and pSocleAt — P_α.' },
  { id: 'Lib.PGroups.UlmInvariants', dep: ['Lib.PGroups.Socle'], d: 38, role: 'ulmInvariant, layerInvariant, marked-graded variants.' },
  { id: 'Lib.Ulm.Invariance', dep: ['Lib.PGroups.UlmInvariants'], d: 4, role: 'Invariants are preserved by isomorphism. The easy direction.' },
  { id: 'Lib.PGroups.Morphisms', dep: ['Lib.Ulm.Invariance'], d: 0, role: 'Morphism layer.' },
  { id: 'Lib.Ulm.Pure', dep: ['Lib.PGroups.Morphisms', 'Lib.PGroups.Socle'], d: 33, role: 'Purity — the technical heart of the back-and-forth.' },
  { id: 'Lib.Ulm.Extension', dep: ['Lib.Ulm.Pure'], d: 55, role: 'Extension lemmas. Largest file in the repo.' },
  { id: 'Lib.Ulm.Classification', dep: ['Lib.Ulm.Extension'], d: 3, role: 'Equal invariants ⇒ isomorphic. The hard direction.' },
  { id: 'Lib.Ulm.Theorem', dep: ['Lib.Ulm.Classification', 'Lib.Ulm.Invariance'], d: 5, role: 'Public entry point: ulm_theorem, both directions.' },
];

export const THEOREM =
`theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)`;

export const PACKS = [
  { id: 'ulm-core', name: 'Ulm core', sub: 'Socle · UlmSubgroups · UlmInvariants · 56 decls', mb: 1.4, on: true },
  { id: 'ulm-hard', name: 'Hard direction', sub: 'Pure · Extension · Classification · 91 decls', mb: 2.1, on: false },
  { id: 'gloss', name: 'Definition glossary', sub: '13 terms, project + Mathlib signatures', mb: 0.1, on: true },
  { id: 'dag', name: 'Dependency map', sub: '14 nodes, real import edges', mb: 0.05, on: true },
  { id: 'goals', name: 'Last goal traces', sub: 'Cached states from the most recent check', mb: 0.6, on: false },
  { id: 'mathlib-sig', name: 'Mathlib signatures', sub: 'Cited decls only, not the 7 GB cache', mb: 0.3, on: true },
];
