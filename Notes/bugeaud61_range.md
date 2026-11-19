# Bugeaud61.problem_10_61.variants.covering_criterion_range

- Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_61.lean:131` (category research solved, [Ste26, Theorem C(ii)])
- Date: 2026-10-31
- Compiles: 2 (1st: two `rw` pattern failures)

Proof idea: the conjugate β = a − α satisfies β·α = aα − α² = −b, so ρ = |β| = |b|/α. Then ρ > 0
because b ≠ 0, and log ρ⁻¹ = log α − log|b| > 0 because ρ < 1. With L = log 2, x = log α > 0 and
y = log α − log|b| > 0, the Route A exponent is L/x + L/y, and logb 2 α − logb 2 |b| = y/L.
Both sides of the iff are equivalent to L·(x+y) < x·y: clear the denominators
((x/L−1)(y/L−1) − 1 = (xy − L(x+y))/L²). `routeAExponent` is restated locally with the same body
(the original file imports FormalConjecturesUtil, which is not built here).

Axioms: `[propext, Classical.choice, Quot.sound]`
