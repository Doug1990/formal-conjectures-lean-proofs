# erdos1082_ii

- Statement: `Erdos1082.erdos_1082.parts.ii` (research solved), checkout file `FormalConjectures/ErdosProblems/1082.lean:56`.
- Claim: it is not true that every finite non-empty set A ⊂ ℝ² with no three points collinear has a point with at least ⌊|A|/2⌋ distinct distances to the other points.

## Proof idea
Counterexample with 8 points: the square corners (±1, ±1) and the axis points (±a, 0), (0, ±a) with a = √3 − 1. Two coincidences make it work: (1 + a)² + 1 = 4 (the square side squared) and 2a² = (1 − a)² + 1 = 8 − 4√3. So each corner sees only the squared distances {4, 8, 8 − 4√3}, and each axis point sees only {16 − 8√3, 8 − 4√3, 4}. That is 3 < 4 = 8/2 distances from every point. All coordinates lie in ℤ[√3]. Distinctness, all 336 ordered non-collinearity determinants, and the distance counts are computed in `Zsqrtd 3` by kernel `decide`. They are transferred to ℝ via the ring hom `Zsqrtd.lift ⟨√3, _⟩`, which is injective by `Zsqrtd.lift_injective` because 3 is not a square. Collinearity of {p, q, r} gives a vanishing 2×2 determinant (via `collinear_iff_of_mem`), and dist = √(φ(Δx² + Δy²)). The checkout definitions `distinctDistancesFrom`, `Set.Triplewise` and `EuclideanGeometry.NonTrilinear` are restated locally, with the same bodies. The unused Oriented/finrank instance arguments of the original `NonTrilinear` section were dropped. The construction was found during this run; the upstream formal proof was not consulted.

## Axioms
'Erdos1082.erdos_1082.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-14
