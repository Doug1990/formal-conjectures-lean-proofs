# Erdős 367: k_ge_three_lower and parts.ii

- Statements: `Erdos367.erdos_367.variants.k_ge_three_lower` (research solved) and `Erdos367.erdos_367.parts.ii` (research solved, question), source `FormalConjectures/ErdosProblems/367.lean` lines 79 and 59 in the checkout.
- Verified file: `work/erdos367_k3.lean`. This file is a hand copy of it, with identical content.

Proof idea: iterate the Chebyshev map t ↦ 4t³ − 3t starting at t = 3. It is encoded without subtraction as m_i = 2P_i² + 1, with P_0 = 1 and P_{i+1} = P_i(4P_i² + 3), so that m_{i+1} + 3m_i = 4m_i³. By induction, m_i − 1 = 2P_i², m_i + 1 = 4Q_i² (invariant P² + 1 = 2Q²), and 3^{i+1} ∣ m_i (since m' = m(4m² − 3) with 3 ∣ 4m² − 3). Also 2m_i ≤ 6^{3^i}. A generic lemma says that n = c·s² implies n ≤ c·B₂(n), because the primes that occur exactly once divide c (`Finset.prod_primes_dvd`). So for n = m_i − 1 we get B₂(n) ≥ n/2, B₂(n+2) ≥ n+2 and B₂(n+1) ≥ 3^{i+1} (i ≥ 1). Since log n ≤ 3^i·log 6 ≤ 5·3^i, the product over [n, n+3) is ≥ (1/4)·n² log n for infinitely many n, with c = 1/4. parts.ii follows with k = 3: an O(n²) bound would contradict log n → ∞.

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-10
