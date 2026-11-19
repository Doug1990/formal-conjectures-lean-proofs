# erdos499_one_le

- Statement: `Erdos499.erdos_499.variants.one_le` (category research solved)
- Source: `FormalConjectures/ErdosProblems/499.lean:72`
- Date: 2026-11-12

Proof idea: Birkhoff–von Neumann (`exists_eq_sum_perm_of_mem_doublyStochastic`) writes M = Σ_σ w_σ P_σ
with w ≥ 0 and Σ w = 1, so M_ij = Σ_{σ i = j} w_σ. Double counting gives
Σ_σ w_σ · Σ_i M_{i,σ(i)} = Σ_{i,j} M_ij², and Cauchy–Schwarz on each row (row sum 1) gives
Σ_j M_ij² ≥ 1/n, so the weighted average is ≥ 1 = Σ w. Hence some σ with w_σ > 0 has
Σ_i M_{i,σ(i)} ≥ 1, and every entry M_{i,σ(i)} ≥ w_σ > 0.

Axioms: `[propext, Classical.choice, Quot.sound]`
