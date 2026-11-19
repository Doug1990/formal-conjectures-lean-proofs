# wowii176

- Statement: `WrittenOnTheWallII.GraphConjecture176.conjecture176` (DISPROOF of Ls + b ≥ n + dist_min(G, M(G²)))
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture176.lean:55` (research solved)

Proof idea: the counterexample is the docstring graph D₇ on Fin 12 (path 0–…–7, triangles {0,8,9} and {7,10,11}), given by an arithmetic adjacency `adjF`. Ls ≤ 4: every path edge crosses a cut, so it lies in every spanning tree (`cut_edge`), and only 8, 9, 10, 11 can be leaves. b ≤ 10: a 2-colouring cannot colour a whole triangle, so an induced bipartite set misses one vertex of each triangle. M(G²) = {1, 6}: the square degrees are computed by `decide` after `dist_eq_computable` and `dist_le_two_iff`. dist(1, 6) ≥ 5 via a 1-Lipschitz potential. So 4 + 10 < 12 + 5. The library definitions (Ls, b, distMin, computable_dist) are restated from FormalConjecturesForMathlib, and the helpers are adapted from results/wowii172.lean.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-19
