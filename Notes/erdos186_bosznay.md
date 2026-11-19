# erdos186_bosznay

- Statement: `Erdos186.erdos_186.variants.bosznay` (∃ c > 0, eventually c·N^{1/4} ≤ F(N), F = max non-averaging subset of [1,N])
- Source: `FormalConjectures/ErdosProblems/186.lean:93` (category research solved, Bosznay [Bo89])
- Date: 2026-11-14

Proof idea: no literature construction was consulted. For k ≥ 1, take A_k = {i² + k³·i : 1 ≤ i ≤ k} ⊆ [1, 2k⁴]. Suppose a set T ∌ i of other indices has Σ_T (j² + k³j) = |T|(i² + k³i). Put E = Σ_T (j² − i²) and D = Σ_T (j − i). Then E + k³D = 0 and |E| ≤ (k−1)(k²−1) < k³, so D = 0 and E = 0. Hence Σ_T (j − i)² = E − 2iD = 0, which contradicts T ≠ ∅ with j ≠ i. This is a strict-convexity argument for (j, j²) points, encoded in base k³. So F(N) ≥ k whenever 2k⁴ ≤ N. With k = ⌊N^{1/4}/2⌋ and N ≥ 256 this gives F(N) ≥ N^{1/4}/4, so c = 1/4. The checkout definitions (NonAveraging, F, card_le_F) are restated locally with targeted Mathlib imports.

Axioms: `'Erdos186.erdos_186.variants.bosznay' depends on axioms: [propext, Classical.choice, Quot.sound]`
