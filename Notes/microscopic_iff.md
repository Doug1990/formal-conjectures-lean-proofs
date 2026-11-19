# microscopic_iff

- Statement: `Arxiv.«2607.05349».hasMicroscopicWeighting_iff_of_isUnit` (category research solved; Roff–Willerton Theorem 3.8)
- Source: `FormalConjectures/Arxiv/2607.05349/MicroscopicWeighting.lean:164`
- Date: 2026-10-31
- Compiles: 2 (clean on the 2nd, including `#print axioms`). The file also contains `hasFiniteConcentration_of_hasMicroscopicWeighting` (see microscopic_con.md); the work copy is identical to work/microscopic_iff.lean.

## Proof idea
(⇒) is `hasFiniteConcentration_of_hasMicroscopicWeighting`. (⇐) Let `B(t)_{ij} = (1 - e^{-t d_ij})/t`, so `Z(t) = J - t B(t)` and `B(t) → D` as `t → 0⁺`. Since `det D ≠ 0`, `B(t)⁻¹ = det⁻¹ • adjugate → D⁻¹` by continuity. Put `u(t) = B(t)⁻¹ 1`, `σ(t) = Σ u(t) - t`, and `v(t) = σ(t)⁻¹ u(t)`. A direct computation gives `Z(t) v(t) = 1` (a Sherman–Morrison-type identity). Because `Z(t)` is invertible for small `t > 0` (analytic determinant, as in microscopic_con), `w(t) = v(t)`. Any gauging `g` with `D g = c·1` and `Σ g = 1` equals `c • D⁻¹1`, so `s₀ = Σ D⁻¹1 ≠ 0`. Hence `v(t) → s₀⁻¹ • D⁻¹1`, and the microscopic weighting exists.

## Axioms
`'Arxiv.«2607.05349».hasMicroscopicWeighting_iff_of_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]`
