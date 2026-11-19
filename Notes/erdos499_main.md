# erdos499_main

- Statement: `Erdos499.erdos_499` (category research solved, Marcus–Minc 1962)
- Source: `FormalConjectures/ErdosProblems/499.lean:41`
- Date: 2026-11-12

Proof idea: Birkhoff–von Neumann (`exists_eq_sum_perm_of_mem_doublyStochastic`) gives
M = Σ_σ w_σ P_σ with w ≥ 0 and Σ w = 1. Double counting shows
Σ_σ w_σ · Σ_i log M_{i,σ(i)} = Σ_{i,j} M_ij log M_ij (Lean's log 0 = 0 makes zero entries harmless).
Each row is a probability vector, so its entropy bound (from log x ≥ 1 − 1/x) gives
Σ_j M_ij log M_ij ≥ −log n, and the weighted average is ≥ −n log n. So some σ with w_σ > 0 has
Σ_i log M_{i,σ(i)} ≥ −n log n. Its entries satisfy M_{i,σ(i)} ≥ w_σ > 0, so taking exp gives
∏_i M_{i,σ(i)} ≥ n^{−n}. The case n = 0 is σ = 1 with the empty product. This argument avoids
van der Waerden's permanent bound.

Axioms: `[propext, Classical.choice, Quot.sound]`
