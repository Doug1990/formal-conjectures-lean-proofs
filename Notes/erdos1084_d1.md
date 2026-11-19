# Erdos1084.erdos_1084.variants.upper_d1

- Source: FormalConjectures/ErdosProblems/1084.lean:53 (category research solved, "easy to check")
- Statement: f 1 n = n − 1, where f d n is the maximum number of unit-distance pairs among n 1-separated points in ℝ^d.

Proof idea: upper bound (D1.ub, generic over any metric space with an isometric real coordinate c). Map each unit-distance pair to its endpoint with the larger coordinate. This map is injective, because the other endpoint is the unique point with coordinate one less. It never hits the point of minimal coordinate, so there are at most n − 1 unit pairs, and separation is not even needed. Lower bound: the points 0, 1, …, n−1 on the line are 1-separated, and the n − 1 consecutive pairs inject into the unit pairs. The bounded ⨆ is handled by `ciSup_le'` and `le_ciSup_of_le` three times. `unitDistNum`, `Metric.IsSeparated'` (on PseudoEMetricSpace) and the `ℝ^` notation are restated locally from FormalConjecturesForMathlib, with targeted imports.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-09 (3 compiles: 1 had a redundant `rfl`; 2 was clean; 3 was clean after matching IsSeparated' to PseudoEMetricSpace as in the source)
