# Bugeaud06.exists_dense_of_growth + exists_dense_of_growth_and_sparsity

- Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean`, lines 122 and 136 (both `category research solved`).
- Proof file: `results/bugeaud06_growth_sparsity.lean` (copy of `work/bugeaud06_sparsity.lean`; `work/bugeaud06_growth.lean` has the first theorem alone).

**Idea.** Take m(n) = n + H(⌊√n⌋), where H(k) = Σ_{i<(k+1)²} g(i). The index blocks [k², (k+1)²) map to runs of 2k+1 consecutive integers, so m is strictly increasing and m(n) ≥ g(n). For an irrational ξ, the ℤ-multiples of ξ are dense on ℝ/ℤ (`AddCircle.denseRange_zsmul_coe_iff`). Compactness then gives a finite L such that {z·ξ : |z| ≤ L} is ε-dense. A run centred at a = k²+k+H(k) with k ≥ L contains a+z for all |z| ≤ L, and translation is an isometry, so the values ξ·m(n) are ε-dense. For the sparsity claim, take g(n) = max(f(n), ⌈exp(exp(n+1))⌉). If m(n) ≤ N, then exp(exp(⌊√n⌋+1)) ≤ N, so n+1 ≤ (⌊√n⌋+1)² ≤ (log log N)². Hence countingFn ≤ ⌊(log log N)²⌋ for every N, which is stronger than "eventually".

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
