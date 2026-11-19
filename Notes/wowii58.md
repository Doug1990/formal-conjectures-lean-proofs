# wowii58

- Statement: `WrittenOnTheWallII.GraphConjecture58.conjecture58` (disproof of ⌈b(G)/l_avg(G)⌉ ≤ f(G), where f is the largest induced forest)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture58.lean:62` (category research solved)
- Date: 2026-11-18

## Proof idea
This proof uses a smaller counterexample than the 79-vertex graph in the checkout docstring. It is a 61-vertex graph on `Fin 61`: K_{3,3} on {0,1,2}|{3,4,5}, plus a clique on Q = {0,3} ∪ {6..60}, i.e. a K_55 glued onto the edge 0–3. Then b ≥ 6, because K_{3,3} itself is bipartite. Also f ≤ 5: a forest has at most 2 vertices in the clique Q (a triangle otherwise), and it cannot contain all of {1,2,4,5} (they form a C4). Next, l(v) ≤ 1 for v ≥ 6 and l(v) ≤ 3 otherwise. This is shown with an explicit clique-cover index function g checked by `omega`. So Σl ≤ 73 and l_avg ≤ 73/61 < 6/5. Also l_avg > 0. Hence b/l_avg > 5, so ⌈b/l_avg⌉ ≥ 6 > 5 ≥ f. The definitions (indepNeighborsCard, averageIndepNeighbors, l_avg, largestInducedForestSize, b) are restated from FormalConjecturesForMathlib, as in wowii91.

## Axioms
`propext, Classical.choice, Quot.sound`
