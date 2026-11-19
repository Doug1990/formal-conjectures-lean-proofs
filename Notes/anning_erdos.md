# anning_erdos

- Statement: `ErdosUlamProblem.erdos_ulam_problem.variants.anning_erdos` (category research solved, Anning–Erdős 1945)
- Source: `FormalConjectures/Wikipedia/ErdosUlamProblem.lean:82`
- Verified file: `work/anning_erdos.lean` (copied to `results/anning_erdos.lean`)

## Proof idea
Pick two distinct points a, b of S. If some c ∈ S is off the line ab, then A = a, B = b, C = c are
non-collinear (det(B−A, C−B) ≠ 0), and S is finite, which is a contradiction. The finiteness argument is Erdős's. For P ∈ S the
differences k = |PA|−|PB| and l = |PB|−|PC| are integers bounded by |AB| and |BC| (triangle
inequality), so they take finitely many values. Each fibre (fixed k, l) has at most two points.
Expanding the squared distances gives ⟨P−Q, B−A⟩ = k(r_P−r_Q) and ⟨P−Q, C−B⟩ = l(r_P−r_Q) with
r = |·C|. Since B−A and C−B span the plane, three distinct points P1, P2, P3 of a fibre then lie on
a line P1 + s·V with s = r − r1. The equations |P1 + sV − Z| = ρ + s for two distinct nonzero s
force |V| = 1 and P1 − Z = ρV for Z = A, B, C. Hence B − A = kV and C − B = lV, contradicting
non-collinearity. This avoids any algebraic-geometry fact about hyperbola intersections.

## Axioms
`'ErdosUlamProblem.erdos_ulam_problem.variants.anning_erdos' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-03
