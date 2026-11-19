# Green42.green_42.variants.dimension_one

- Source: `FormalConjectures/GreensOpenProblems/42.lean:104` (category research solved, Cohn–Elkies 2003, d = 1)
- Statement: `CohnElkiesOptimal 1 (1 / 2)`
- Proof file: `results/green42_dim1.lean` (targeted imports; the `ℝ^` notation, `fHat`, `CohnElkiesAdmissible`, `SatisfiesCohnElkiesScheme`, `CohnElkiesOptimal` are restated verbatim from the source; the `@[category]` attribute is dropped because it needs FormalConjecturesUtil)

## Proof idea
The witness is the triangle function F(x) = max(0, 1 − ‖x‖/2) on ℝ¹. It is continuous, radial, vanishes for ‖x‖ ≥ 2, and F(0) = 1. Via the linear isometry ℝ ≃ ℝ¹ given by `(OrthonormalBasis.singleton (Fin 1) ℝ).repr` and `Real.fourier_comp_linearIsometry`, the Fourier transform reduces to the 1D transform of tri(x) = max(0, 1 − |x|/2). Its real part is ∫_{-2}^{2} tri(x) cos(2πsx) dx. Explicit antiderivatives on [−2,0] and [0,2] (FTC) give 2·(sin ω/ω)² with ω = 2πs for s ≠ 0, and 2 for s = 0. So F̂ ≥ 0 and F̂(0) = 2, which gives the ratio 1/2. Admissibility uses C = 9 and δ = 1: |F(x)|(1+‖x‖)² ≤ 9 holds trivially, and F̂(s)(1+|s|)² ≤ 9 follows from (sin ω/ω)² ≤ 1 for |s| ≤ 1 and from (sin ω/ω)²·ω² ≤ 1 with ω² ≥ (1+|s|)² for |s| > 1.

## Axioms
`'Green42.green_42.variants.dimension_one' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-10-31
