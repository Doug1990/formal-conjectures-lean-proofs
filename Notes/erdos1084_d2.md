# Erdos1084.erdos_1084.variants.easy_upper_d2

- Source: `FormalConjectures/ErdosProblems/1084.lean:58` (category research solved)
- Statement: for `n ≠ 0`, `f 2 n < 3 * n` (a 1-separated set of n points in the plane spans fewer than 3n unit distances).
- Verified file: `work/erdos1084_d2.lean` (identical copy here). The definitions `unitDistNum`, `Metric.IsSeparated'` and the `ℝ^` notation are restated locally from FormalConjecturesForMathlib, as in `erdos1084_d1.lean`.

## Proof idea
For a point v, put each unit neighbour w into the angular class ⌈(arg(w−v)+π)·3/π⌉ ∈ {1,…,6}. Two neighbours in the same class have arguments less than π/3 apart, so cos(Δ) > 1/2 and |w−w'|² = 2−2cos Δ < 1, which contradicts 1-separation. So every degree is ≤ 6. For the point m with the smallest first coordinate, all neighbours satisfy Re ≥ 0, so arg ∈ [−π/2, π/2] and the class lies in {2,…,5}, which gives degree ≤ 4. A handshake bound (Bool × unit pairs ↪ ordered unit pairs via `out` / `out.swap`) gives 2·#E ≤ Σ deg ≤ 6(n−1)+4, so #E ≤ 3n−1. The supremum bound then uses `ciSup_le'`.

## Axioms
`'Erdos1084.erdos_1084.variants.easy_upper_d2' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
