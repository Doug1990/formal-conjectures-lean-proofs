# WrittenOnTheWallII.Test.C6_cvetkovic

- Statement: `theorem C6_cvetkovic : cvetkovic C6 = 3` (`@[category test, AMS 5]`)
- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line 491); `C6 := cycleGraph 6` (line 69); `cvetkovic` copied verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cvetkovic.lean`.

Proof idea: the characteristic matrix of the 6-cycle's adjacency matrix is written explicitly (entrywise `fin_cases` + `simp` with `decide := true` to evaluate the `Fin 6` adjacency). Its determinant, for a generic diagonal entry `x`, is expanded along row 0 repeatedly (`Matrix.det_succ_row_zero`), with zero terms pruned during `simp only`, and `ring` closes it as (x-2)(x+2)(x-1)^2(x+1)^2. So the roots multiset is {2} + {-2} + 2•{1} + 2•{-1} (`roots_mul`, `roots_pow`, `roots_X_sub_C`, nonzero side goals by `X_sub_C_ne_zero`). That gives zero count 0, positive count 3 and negative count 3, so cvetkovic = 0 + min 3 3 = 3.

Uses targeted Mathlib imports, because `import Mathlib` does not load within the time limit on this machine.

Axioms: `'WrittenOnTheWallII.Test.C6_cvetkovic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
