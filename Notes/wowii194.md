# wowii194

- Statement: `WrittenOnTheWallII.GraphConjecture194.conjecture194` (DISPROOF of "α(G) ≤ 1 + l_avg(G) ⇒ G has a Hamiltonian path"), source `FormalConjectures/WrittenOnTheWallII/GraphConjecture194.lean:57` (research solved).
- Proof idea: the docstring's 18-vertex counterexample on `Fin 18` with arithmetic adjacency. K = {0..10} is a clique, A = {11..14} is independent and complete to K, and the leaves 15, 16, 17 hang at 11, 12, 14. Then α ≤ 4 via a cover by 4 cliques ({11,15}, {12,16}, {14,17}, K ∪ {13}), with an injection `gc` checked by `decide`. Σ_v α(N(v)) ≥ 54 comes from explicit independent witness sets in each neighbourhood, so the hypothesis 4 ≤ 1 + 54/18 holds. A Hamiltonian path would need all three pendant vertices as endpoints (an interior path vertex has two distinct neighbours), which is impossible.
- Axioms: propext, Classical.choice, Quot.sound
- Date: 2026-11-19
- The definitions from FormalConjecturesForMathlib (indepNeighborsCard, indepNeighbors, averageIndepNeighbors) are restated verbatim.
