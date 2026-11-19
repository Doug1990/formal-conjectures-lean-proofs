# Erdos669.erdos_669.variants.upper_bound + erdos_669.variants.limit_le

- Source: FormalConjectures/ErdosProblems/669.lean:229 and :241 (both category research solved)
- Date: 2026-11-10
- Axioms (both): `[propext, Classical.choice, Quot.sound]`

Proof idea: double counting. For a point set S with |S| = n, each line L through ≥ k points of S
contributes the family of 2-subsets of S ∩ L, which has ≥ C(k,2) members. Two distinct
determined lines share no 2-subset, because two distinct points p ≠ q on a line spanned by a ≠ b
already span that line (`UB.line_eq`: affineSpan{p,q} ≤ affineSpan{a,b}, and both directions are
1-dimensional, `finrank_span_singleton`). The disjoint union lies inside the 2-subsets of S, so
#lines · C(k,2) ≤ C(n,2), and `csSup_le'` gives F_k(n) ≤ C(n,2)/C(k,2) (ℕ division, then cast).
For limit_le: F_k(n)·k(k−1) ≤ n(n−1) ≤ n², so F_k(n)/n² ≤ 1/(k(k−1)) for all n (n = 0 gives 0),
and `le_of_tendsto'` passes the bound to the limit. The definitions are restated locally (ℝ² as
`EuclideanSpace ℝ (Fin 2)`), with targeted imports.
