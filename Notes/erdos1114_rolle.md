# erdos1114_rolle

- Statement: `Erdos1114.erdos_1114.variants.rolle` (category textbook)
- Source: `FormalConjectures/ErdosProblems/1114.lean`, line 85
- Date: 2026-10-29

Proof idea: Rolle's theorem (`exists_deriv_eq_zero`, with `Polynomial.deriv`) gives, for each k < N, a zero c k of f'
in the open interval (a+kd, a+(k+1)d). These intervals are pairwise disjoint (`interval_eq`), so c is injective
on range N and gives N distinct zeros. Since deg f = N+1, f' ≠ 0 and deg f' ≤ N, so f' has at most N distinct roots
(`card_roots'`). Hence every zero of f' is one of the c k (otherwise insert it and get N+1 distinct roots). This gives
both uniqueness in each interval (a second zero would be some c j with j = k by disjointness) and the second
conjunct (every zero lies in some interval).

Axioms: `'Erdos1114.erdos_1114.variants.rolle' depends on axioms: [propext, Classical.choice, Quot.sound]`

Note: `import Mathlib.Analysis.Calculus.LocalExtr.Polynomial` made the compile time out; the three targeted imports
in the file compile quickly.
