# WrittenOnTheWallII.Test.house_cvetkovic

- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line ~179), `@[category test, AMS 5]`
- Statement: `cvetkovic HouseGraph = 3`. `HouseGraph` (fromEdgeSet, 6 edges on `Fin 5`) and `cvetkovic` are restated verbatim from the checkout (`cvetkovic` comes from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cvetkovic.lean`). The file uses targeted Mathlib imports.

Proof idea: First the characteristic matrix is written out explicitly (25-case `fin_cases` + `simp`). Cofactor expansion plus `ring` then gives `charpoly = X · (X + 2) · q` with `q = X³ − 2X² − 2X + 2`. The cubic q has three real roots, found by the intermediate value theorem from sign changes: r₁ ∈ (−2,−1), r₂ ∈ (0,1) and r₃ ∈ (1,3). These are distinct, so `{r₁,r₂,r₃} ≤ q.roots`. Since `card q.roots ≤ natDegree q ≤ 3` (`compute_degree`), this gives `q.roots = {r₁,r₂,r₃}`. So the spectrum is {0, −2, r₁, r₂, r₃}: one zero eigenvalue, two positive, two negative. The value is 1 + min(2,2) = 3.

Axioms: `'WrittenOnTheWallII.Test.house_cvetkovic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compile output: no errors, no warnings (first compile).

Date: 2026-10-28
