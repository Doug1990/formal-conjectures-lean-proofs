# erdos987_fin

- Statement: `Erdos987.erdos_987.variants.finite_distinct_points` (category research solved, Liu / Clunie)
- Source: `FormalConjectures/ErdosProblems/987.lean` (line 179) in google-deepmind/formal-conjectures
- Proof file: `results/erdos987_fin.lean` (identical copy of `work/erdos987_fin.lean`). `additiveChar`/`e` and `A` are restated locally and targeted imports are used.

## Proof idea
Let S be the finite set of values of x. For any a, pigeonhole on the maps y ↦ ⌊4·fract(j·L·y)⌋ ∈ Fin 4 (y ∈ S), for j = 0..|S → Fin 4| with L = a+1, gives i ≠ j with the same buckets. Then k = |j−i|·L ≥ a satisfies dist(k·y, ℤ) < 1/4, so cos(2πky) > 0 for every y ∈ S (simultaneous Dirichlet approximation). With c = min_{y∈S} cos(2πky) > 0 we get ‖Σ_{j<n} e(k x_j)‖ ≥ Re ≥ n·c → ∞, so the limsup in EReal is ⊤. This holds for infinitely many k. The hypothesis x_j ∈ (0,1) is not needed. The checkout's external formal proof was not used.

## Axioms
'Erdos987.erdos_987.variants.finite_distinct_points' depends on axioms: [propext, Classical.choice, Quot.sound]

## Date
2026-11-13
