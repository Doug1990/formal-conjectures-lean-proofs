# Erdos1026.erdos_1026.variants.weighted_erdos_szekeres

- Source: `FormalConjectures/ErdosProblems/1026.lean:137` (category research solved; Tidor–Wang–Yang / Wagner / Cambie's weighted Erdős–Szekeres)
- Statement: for distinct positive reals x_1..x_{k²} with Σ x_i = 1 there is a monotone subsequence with sum ≥ 1/k.
- Verified file: `work/erdos1026_wes.lean` (`results/erdos1026_wes.lean` is an identical copy). `monotonicSubsequenceSums` is restated locally, and the file uses targeted imports.

**Proof idea.** For each index i, let L_i (resp. D_i) be the largest sum of an increasing (resp. decreasing) subsequence ending at i. Both are defined generically as a `Finset.sup'` over the chains for a relation r. If i < j and x_i < x_j, then L_j ≥ L_i + x_j; if x_i > x_j, then D_j ≥ D_i + x_j. So the squares (L_i − x_i, L_i] × (D_i − x_i, D_i] are pairwise disjoint, and they all lie in [0, L*] × [0, D*]. Lebesgue measure (`measure_biUnion_finset`, `Measure.prod_prod`) gives Σ x_i² ≤ L*·D*. Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) gives 1 ≤ k²·Σ x_i², so max(L*, D*) ≥ 1/k, and the maximiser is the sum of an actual monotone subsequence.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
