# WrittenOnTheWallII.Test.Star5_cvetkovic

- Statement: `theorem Star5_cvetkovic : cvetkovic Star5 = 5` (`@[category test, AMS 5]`)
- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line 626). `Star5 := completeBipartiteGraph (Fin 1) (Fin 5)` and its `DecidableRel` instance (lines 72-74) are copied verbatim. `cvetkovic` is copied verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cvetkovic.lean`.

Proof idea: the adjacency matrix on `Fin 1 ⊕ Fin 5` is reindexed along `finSumFinEquiv` to an explicit 6×6 matrix (entrywise `rfl`), using `Matrix.charpoly_reindex`, which leaves the charpoly unchanged. The characteristic matrix is written explicitly, and its determinant for a generic diagonal `x` is expanded along row 0 (`Matrix.det_succ_row_zero`), giving x^4 (x^2 - 5) after `ring`. Since (√5)^2 = 5, the charpoly equals X^4 (X - √5)(X + √5), so the roots multiset is 4•{0} + {√5} + {-√5}. That gives zero count 4, positive count 1 and negative count 1, so cvetkovic = 4 + min 1 1 = 5.

Uses targeted Mathlib imports, because `import Mathlib` does not load within the time limit on this machine.

Axioms: `'WrittenOnTheWallII.Test.Star5_cvetkovic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
