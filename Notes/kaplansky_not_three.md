# KaplanskyUInvariant.u_invariant_values.variants.not_three

- Source: `FormalConjectures/Paper/KaplanskyUInvariant.lean:153` (category research solved; Kaplansky 1953, Theorem 2)
- Statement: `¬ IsUInvariant 3` (no field of characteristic ≠ 2 has u-invariant 3)
- `IsUInvariant` and `QuadraticForm.anisotropicDims` are restated verbatim from the checkout (targeted Mathlib imports; FormalConjecturesUtil is not built).

## Proof idea
Diagonalize the anisotropic 3-dimensional form (`QuadraticForm.equivalent_weightedSumSquares`, using 2 invertible) and rescale it to ⟨1, a, b⟩. Then ⟨1, a, b, ab⟩ is anisotropic too. Suppose x² + ay² + bz² + abt² = 0. If z² + at² = 0, anisotropy of ⟨1, a, b⟩ gives z = t = 0 and then x = y = 0. Otherwise put c = z² + at². The two-squares identity (x² + ay²)(z² + at²) = (xz − ayt)² + a(xt + yz)² gives (xz − ayt)² + a(xt + yz)² + b·c² = 0, so anisotropy forces c = 0, which is a contradiction. Hence 4 ∈ anisotropicDims (nondegeneracy is automatic in characteristic ≠ 2), so 3 is not the greatest element.

## Axioms
`'KaplanskyUInvariant.u_invariant_values.variants.not_three' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-01. Compiles: 1.
