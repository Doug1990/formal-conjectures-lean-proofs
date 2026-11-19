# wowii32

- Statement: `WrittenOnTheWallII.GraphConjecture32.conjecture32` (a DISPROOF: `¬ ∀ G, distavg(A) + ½·eccavg(M) ≤ path G`)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture32.lean:58` (category research solved)
- Date: 2026-11-18

Proof idea: this is the counterexample from the docstring, the path P5 on Fin 5 (defined locally with decidable adjacency `i+1 = j ∨ j+1 = i`). Degrees are computed by `decide`. This gives minDegree = 1, maxDegree = 2, A = {0,4} and M = {1,2,3}. A walk-length induction gives the lower bound dist(u,v) ≥ |u−v|, so dist(0,4) = dist(4,0) ≥ 4. Eccentricity lower bounds (ecc 1 ≥ 3, ecc 2 ≥ 2, ecc 3 ≥ 3) come from `edist_le_eccent` plus finiteness (`connected_iff_ediam_ne_top`). `path P5 ≤ 5` holds because an induced path is a nodup list. Hence the left side is ≥ 4 + 4/3 > 5 ≥ path, so linarith closes the goal. `isInducedPath`, `path` and `path_le_of_isInducedPath_length_le` are restated verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean (targeted imports only).

Axioms: `'WrittenOnTheWallII.GraphConjecture32.conjecture32' depends on axioms: [propext, Classical.choice, Quot.sound]`

The only compiler warning is the unused binder `h` inside the original statement, which was left unchanged.
