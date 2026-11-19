# Erdos1026.erdos_1026.variants.lower_bound

- Source: `FormalConjectures/ErdosProblems/1026.lean:109` (category research solved; Hanani's 1/√2 bound)
- Statement: `1 / Real.sqrt 2 ∈ admissibleConstants`.
- Verified file: `work/erdos1026_lb.lean` (`results/erdos1026_lb.lean` is an identical copy). `monotonicSubsequenceSums` and `admissibleConstants` are restated locally, and the file uses targeted imports.

**Proof idea.** This proof does not use Hanani's decomposition. It proves the stronger `WES.mem_of_le_one`: every c ≤ 1 is admissible, so in particular 1 ∈ admissibleConstants, which is the lower half of `erdos_1026`. It reuses the area argument from `erdos1026_wes`, where the disjoint squares give Σx_i² ≤ L*·D*. Cauchy–Schwarz for arbitrary n gives (Σx)² ≤ n·Σx², so max(L*, D*) ≥ Σx/√n for every n ≥ 1 (`WES.main`). Since c − ε ≤ 1 and Σx/√n ≥ 0, the bound (c−ε)/√n·Σx ≤ S follows.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
