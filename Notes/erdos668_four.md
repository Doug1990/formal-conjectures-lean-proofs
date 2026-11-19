# erdos668_four

- Statement: `Erdos668.erdos_668.variants.four_points` (research solved, AMS 52)
- Source: `FormalConjectures/ErdosProblems/668.lean:84` in the checkout
- Definitions `unitDistNum` (FormalConjecturesForMathlib/Geometry/Metric.lean), `Erdos90.unitDistanceCounts` and `Erdos90.maxUnitDistances` (ErdosProblems/90.lean) are restated verbatim; `ℝ²` is a local notation for `EuclideanSpace ℝ (Fin 2)`. Only targeted Mathlib imports are used.

## Proof idea
The witness is a = (0, √3/2), b = (−1/2, 0), c = (1/2, 0), d = (0, −√3/2): two unit equilateral triangles that share the edge bc. Everything is done in coordinates.
- No four points in the plane are pairwise at distance 1. With u, v, w = b−a, c−a, d−a, the 3×3 Gram determinant of three vectors in ℝ² vanishes identically (`ring`), but these Gram entries give 1/2.
- So every 4-set has at most 5 unit pairs, and `maxUnitDistances 4 = 5` (IsGreatest.csSup_eq).
- A 4-set with exactly 5 unit pairs has exactly one non-unit pair (two missing pairs would give at most 4, by counting inside the 6 off-diagonal Sym2 pairs). That pair is found by a 6-way case split.
- Two-circle lemma: if |b−c| = 1 and both a and d are at distance 1 from b and c, with a ≠ d, then d = b + c − a.
- The isometry is m + x₀(c−b) + x₁(a−m)/s with m = (b+c)/2. It is built with `IsometryEquiv.mk'` from an explicit inverse, after checking that the frame is orthonormal.
- The converse direction uses the fact that isometries preserve distances and injectivity.

## Also in the file
`Erdos668.erdos_668.parts.ii` (ErdosProblems/668.lean:72, research solved). n = 4 is a counterexample. The proof is the checkout's test lemma `four_points_implies_parts_ii`, applied to `four_points`.

## Axioms
`'Erdos668.erdos_668.variants.four_points' depends on axioms: [propext, Classical.choice, Quot.sound]`
`'Erdos668.erdos_668.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-18. 6 compile attempts (5 for four_points, 1 more for parts.ii).
