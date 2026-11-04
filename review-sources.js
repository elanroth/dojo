/* The mathematical source to compare each definition against.
 *
 * PUBLICATION RULE: this file ships to a public web page. Keep entries short, mostly
 * paraphrase, and give the exact page. Never write one from memory: a misremembered
 * definition here would make the check worthless. These were read from the printed
 * pages of the scan, Infinite Abelian Groups (Kaplansky, Ann Arbor, 1954).
 *
 * Shape: declaration -> { cite, kind: 'quote' | 'paraphrase', passage }
 * Math notation needs a separator before a subscripted letter: write p·G_α, not pG_α.
 */
const K = 'Kaplansky, Infinite Abelian Groups, ';

export const SOURCES = {
  pImage: {
    cite: K + 'p. 26', kind: 'paraphrase',
    passage: 'Each successor stage multiplies the previous one by p: G_{α+1} = p·G_α.',
  },
  ulmSubgroup: {
    cite: K + 'p. 26', kind: 'paraphrase',
    passage: 'G_n = p^n·G for finite n. In general G_{α+1} = p·G_α, and at a limit ordinal α, G_α is the intersection of the G_β for β < α.',
  },
  IsPReduced: {
    cite: K + 'p. 26', kind: 'paraphrase',
    passage: 'The series stabilises at some ordinal λ, and G_λ is the maximal divisible subgroup. For a reduced group, G_λ = 0.',
  },
  IsReducedPGroup: {
    cite: K + 'pp. 26–27', kind: 'paraphrase',
    passage: 'Theorem 14 is about groups that are both reduced and primary.',
  },
  pSocle: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'P is the group of all elements with px = 0.',
  },
  pSocleAt: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'P_α = P ∩ G_α.',
  },
  pSocleAt_succ_subgroupOf: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'The quotient P_α / P_{α+1} is taken with P_{α+1} inside P_α.',
  },
  ulmDenSubmodule: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'The denominator of the quotient P_α / P_{α+1}, which is a vector space over the integers mod p.',
  },
  pSocleAt_quot_module: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'P_α / P_{α+1} is regarded as a vector space over the integers mod p.',
  },
  ulmQuotient: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'The quotient group P_α / P_{α+1}, a vector space over the integers mod p.',
  },
  ulmInvariant: {
    cite: K + 'p. 27', kind: 'paraphrase',
    passage: 'f(α), the α-th Ulm invariant of G, is the dimension of P_α / P_{α+1}. The invariants form a function from the ordinals to the cardinals.',
  },
  ulm_theorem: {
    cite: K + 'Theorem 14, p. 27', kind: 'quote',
    passage: 'Two reduced countable primary abelian groups are isomorphic if and only if they have the same Ulm invariants.',
  },
};
