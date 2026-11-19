# Bugeaud09.problem_10_9.variants.measure_zero and Bugeaud09.problem_10_9.variants.dimH_lt_one

Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_9.lean`, lines 64 and 73 (both `category research solved`).
`IsZNumber` is restated word for word from `FormalConjecturesForMathlib/NumberTheory/DiophantineApproximation/ZNumber.lean`, because the work files use targeted Mathlib imports instead of FormalConjecturesUtil.

Proof idea (Mahler's argument): write g_n = ⌊ξ(3/2)^n⌋. If both {ξ(3/2)^n} and {ξ(3/2)^{n+1}} are < 1/2, a parity case split shows g_{n+1} = ⌊(3g_n+1)/2⌋ (lemma `step`). So for a Z-number every g_n with n ≥ 1 is determined by g_1. If two Z-numbers ξ, η have the same g_1, then all their floors agree, so |ξ−η|(3/2)^n < 1/2 for every n ≥ 1, which forces ξ = η. The map ξ ↦ ⌊3ξ/2⌋ is therefore injective on Z-numbers, and the set of Z-numbers is countable. Countable sets have Lebesgue measure 0 (`Set.Countable.measure_zero`) and Hausdorff dimension 0 < 1 (`Set.Countable.dimH_zero`). Both statements are actually weaker than the countability that is proved here.

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
