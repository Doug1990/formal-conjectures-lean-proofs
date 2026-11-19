# erdos661_lenz

- Statement: `Erdos661.erdos_661.variants.lenz` (category research solved)
- Source: `FormalConjectures/ErdosProblems/661.lean:138`
- Date: 2026-11-02

Proof idea: Lenz's construction. For k < n put a_k = k/(2(n+1)) ∈ [0, 1/2) and
b_k = √(1/2 − a_k²) > 0, so a_k² + b_k² = 1/2. Take A = {(a_k, b_k, 0, 0)} and
B = {(0, 0, a_k, b_k)}. Both maps k ↦ point are injective (the a_k are distinct), so
|A| = |B| = n; A and B are disjoint because the 4th coordinate is 0 on A and b_k > 0 on B;
and every cross distance is √(1/2 + 1/2) = 1 via `EuclideanSpace.dist_eq` and `Fin.sum_univ_four`.

Axioms: `'Erdos661.erdos_661.variants.lenz' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles: 1 (clean on the first try).
