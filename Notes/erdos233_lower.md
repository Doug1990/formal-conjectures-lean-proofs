# erdos233_lower

- Statement: `Erdos233.erdos_233.variants.lower_bound` (category research solved), source `FormalConjectures/ErdosProblems/233.lean:59` in the checkout.
- Verified file: `work/erdos233_lower.lean`. `results/erdos233_lower.lean` is an identical copy. It uses targeted imports and restates `primeGap` from `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean` locally.

Proof idea: the prime gaps telescope, so Σ_{n<N} g_n = p_N − 2. Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) gives Σ g_n² ≥ (p_N − 2)²/N. For the size of p_N, Chebyshev's θ(p_N) ≤ p_N·log 4 (`Chebyshev.theta_le_log4_mul_x`) is combined with θ(p_N) ≥ Σ_{N/2 ≤ k < N} log p_k ≥ (N/2)·log(N/2+2) ≥ (N/4)·log N, using p_k ≥ k+2. Hence N log N ≤ 4 log 4 · p_N ≤ 8 log 4 · (p_N − 2), and so N (log N)² ≤ 4c²·Σ g_n² for N ≥ 16 with c = 4 log 4. The prime number theorem is not needed.

Axioms: `'Erdos233.erdos_233.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-10
