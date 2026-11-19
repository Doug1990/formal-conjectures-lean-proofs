# Hadamard.isHadamard_equiv_isHadamard'

- Source: `FormalConjectures/Wikipedia/Hadamard.lean:54` (tagged category test, but upstream it has a TODO and a `sorry` in the ⇐ direction, which is the equality case of Hadamard's inequality)
- Date: 2026-11-03
- Compiles: 2 (1st: missing `StarOrderedRing ℝ` instance → import Mathlib.Algebra.Order.Star.Real; 2nd: clean + axioms)

## Proof idea
⇒: det(MᵀM) = det(n·I) = nⁿ, so |det M|² = nⁿ = (n^{n/2})². ⇐ (the missing direction): G = MᵀM is
positive semidefinite (`posSemidef_conjTranspose_mul_self`), its diagonal entries are n because the entries
are ±1, so trace G = n², and det G = |det M|² = nⁿ. The eigenvalues λᵢ ≥ 0 therefore have sum n²
and product nⁿ, so the equality case of the weighted AM-GM inequality
(`Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'` with weights 1/n) forces every λᵢ = n. The spectral
theorem then gives G = U (n·I) U* = n·I, because the conjugation star-algebra automorphism fixes scalars. The case n = 0 is trivial.
The definitions are restated locally, and the file uses targeted imports.

Reusable helpers: `HE.amgm_eq` (equality case of unweighted AM-GM), `HE.rpow_sq`, `HE.fwd`, `HE.bwd`.

## Axioms
`'Hadamard.isHadamard_equiv_isHadamard'' depends on axioms: [propext, Classical.choice, Quot.sound]`
