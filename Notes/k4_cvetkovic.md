# WrittenOnTheWallII.Test.K4_cvetkovic

- Statement: `theorem K4_cvetkovic : cvetkovic K4 = 1` (`@[category test, AMS 5]`)
- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line 284); `cvetkovic` copied verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cvetkovic.lean`, `K4` from Test.lean line 62.

Proof idea: the characteristic matrix of the adjacency matrix of K4 is written explicitly as `!![X,-1,-1,-1; ...]` (entrywise `fin_cases` + `simp`). Its determinant is computed by cofactor expansion along row 0 (`Matrix.det_succ_row_zero`, unfolded with `simp only`) and `ring`, giving charpoly = (X - 3)(X + 1)^3. The roots multiset is then `{3} + 3 • {-1}` (`roots_mul`, `roots_pow`, `roots_X_sub_C`), so zero count = 0, positive count = 1, negative count = 3, and cvetkovic = 0 + min 1 3 = 1.

The file uses targeted Mathlib imports instead of `import Mathlib`, because the full import does not load within the 5-minute limit on this machine.

Axioms: `'WrittenOnTheWallII.Test.K4_cvetkovic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
