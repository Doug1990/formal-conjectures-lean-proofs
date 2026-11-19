# WrittenOnTheWallII.Test.petersen_cvetkovic

- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line ~392), `@[category test, AMS 5]`
- Statement: `cvetkovic PetersenGraph = 4`. `PetersenVertex`, `petersenGraph` (Kneser K(5,2)) and its instance are restated verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean`, and `cvetkovic` verbatim from `.../Cvetkovic.lean`. The file uses targeted Mathlib imports.

Proof idea: The adjacency matrix is reindexed along an explicit bijection `Fin 5 ⊕ Fin 5 ≃ PetersenVertex`: outer 5-cycle j ↦ {2j,2j+1}, inner pentagram j ↦ {2j+2,2j+4}. The bijection and the block adjacency table are checked by `decide`. In this order the characteristic matrix is `fromBlocks M (-1) (-1) N`, where M and N are the characteristic matrices of C5 and the pentagram. A generic lemma over any `CommRing` with no zero divisors handles the block determinant. Left-multiplying by `S = fromBlocks 0 (-1) (-1) 0` (with S² = 1, so det S = ±1) and applying `det_fromBlocks_one₁₁` gives det = ±det(1 − MN). Here 1 − MN has 1 − X² on the diagonal and X − 1 everywhere else. A 5x5 cofactor expansion gives its determinant as (d−a)⁴(d+4a) = −(X−3)(X−1)⁵(X+2)⁴. Roots are unchanged by the sign, so the spectrum is {3, 1⁵, (−2)⁴}: no zero eigenvalue, 6 positive, 4 negative. The value is 0 + min(6,4) = 4.

Axioms: `'WrittenOnTheWallII.Test.petersen_cvetkovic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compile output: no errors, only `unusedSimpArgs` lint warnings, no sorry. 3 compiles. The first had kernel "deep recursion" errors from instance-path unfolding over ℝ[X]. The second, with maxRecDepth raised, timed out. Fixed by proving the block step for a generic ring.

Date: 2026-10-28
