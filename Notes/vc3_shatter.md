# VCDimConvex.exists_infinite_convex_r3_shatters

- Source: `FormalConjectures/Other/VCDimConvex.lean:47` (category research solved)
- Statement: `∃ A C : Set ℝ³, A.Infinite ∧ Convex ℝ C ∧ Shatters {t +ᵥ C | t : ℝ³} A`
- Lean file: `results/vc3_shatter.lean`. The statement is unchanged. `Shatters` is restated locally from `FormalConjecturesForMathlib/Combinatorics/SetFamily/VCDim.lean`, and `ℝ³` is a local notation for `EuclideanSpace ℝ (Fin 3)`.

## Proof idea
Let pt(x, y) = (x, y, x² + y²) be a point on the paraboloid. Take A = {pt(k, 0) : k ∈ ℕ}. Choose an injection q : Set ℕ → ℝ, which exists by cardinality (#Set ℕ = 2^ℵ₀ = 𝔠 = #ℝ). Let C be the convex hull of G = {pt(k, q T) : k ∈ T}.

For a subset B of A, let S = {k : pt(k, 0) ∈ B} and translate C by −pt(0, q S). Then pt(k, 0) lies in the translate if and only if pt(k, q S) ∈ C, because pt(0, y) + pt(x, 0) = pt(x, y). If k ∈ S, this point is in G. If k ∉ S, every point of G differs from pt(k, q S) in its (x, y) coordinates. The linear functional f(v) = v₂ − 2p₁v₀ − 2p₂v₁ satisfies f(pt(x, y)) + p₁² + p₂² = (x − p₁)² + (y − p₂)². So G lies in the open half-space f > −(p₁² + p₂²), while pt(p₁, p₂) lies on its boundary. The half-space is convex, so pt(p₁, p₂) is not in conv G.

## Axioms
`'VCDimConvex.exists_infinite_convex_r3_shatters' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-04 (4 compiles)
