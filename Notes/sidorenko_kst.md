# sidorenko_kst

- Statement: `SidorenkoConjecture.sidorenko_conjecture.variants.complete_bipartite` (category research solved, Sidorenko 1993)
- Source: `FormalConjectures/Wikipedia/SidorenkoConjecture.lean:775` in the checkout
- Date: 2026-11-03

## Proof idea
Homomorphisms K_{s,t} → G correspond to a tuple x ∈ W^s plus a map Fin t → (common neighbourhood of x),
so homCount = Σ_x c(x)^t. Double counting gives Σ_x c(x) = Σ_y deg(y)^s. Two applications of the
power-mean inequality (`pow_sum_div_card_le_sum_pow`, in the form (Σf)^m·N ≤ (Σf^m)·N^m, which also
covers m = 0) give D^s·N ≤ (Σ deg^s)·N^s with D = Σ deg = 2e(G), and (Σ c)^t·N^s ≤ (Σ c^t)·N^{st}.
Combining them gives (D/N²)^{st} ≤ Σ c^t / N^{s+t}, which is the claim because e(K_{s,t}) = st
(from Mathlib's `encard_edgeSet_completeBipartiteGraph`) and homCount(K₂, G) = 2e(G) (darts).
`homCount` / `homDensity` are restated locally from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/HomDensity.lean
(the same definitions), with targeted Mathlib imports.

## Axioms
`'SidorenkoConjecture.sidorenko_conjecture.variants.complete_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles: 2 (1st had one rewrite error in the final algebra step; 2nd clean apart from an unused-hypothesis lint on the helper `key`). The results copy was written by hand from the verified work file and not compiled separately.
