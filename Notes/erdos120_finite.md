# Erdos120.erdos_120.variants.finite_set

- Source: `FormalConjectures/ErdosProblems/120.lean:55` (category research solved, Steinhaus 1920)
- Statement: for a finite `A ⊆ ℝ`, `¬ Erdos120For A`, i.e. every measurable `E` of positive measure contains some `a • A + b` with `a ≠ 0`.
- Date: 2026-11-12

## Proof idea
Lebesgue density (`Besicovitch.ae_tendsto_measure_inter_div` for `volume.restrict E`, which is nonzero) gives a point `x` with
`|E ∩ B(x,r)| / |B(x,r)| → 1`. With `n = |A|` and `δ = 1/(4(n+1))`, pick `r > 0` with `|B(x,r) \ E| < δ·2r`. Scale `s = r/(2M)` with `|a| ≤ M` on `A`,
so `b + s·a ∈ B(x,r)` for every `b ∈ B(x,r/2)`. If every `b ∈ B(x,r/2)` had some `b + s·a ∉ E`, then `B(x,r/2)` would be covered by the `n` translates
`(· + s·a)⁻¹' (B \ E)`, giving `r ≤ n·|B \ E| < n·δ·2r < r`. So some `b` works, and `s·A + b ⊆ E`. The definition `Erdos120For` is restated locally (same text); the import is targeted Mathlib instead of FormalConjecturesUtil.

## Axioms
`'Erdos120.erdos_120.variants.finite_set' depends on axioms: [propext, Classical.choice, Quot.sound]`
