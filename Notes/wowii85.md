# wowii85

- Statement: `WrittenOnTheWallII.GraphConjecture85.conjecture85` (a DISPROOF of tree(G) ≥ ⌈√(1 + 2·min_v distEven(v))⌉)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture85.lean:49` (research solved)
- Date: 2026-11-18

Proof idea: the counterexample is C₅[K₄] on Fin 20, the same graph as wowii63. Vertex i lies in clique i/4, and adjacency is a linear-arithmetic predicate, so `omega` can decide it. The graph has diameter 2 (an explicit middle vertex works for every pair). Each vertex has exactly 9 non-neighbours, all at distance 2, so distEven ≥ 9 and the radicand is ≥ 19 > 16. That makes the ceiling ≥ 5. Every induced acyclic set has ≤ 4 vertices: at most 2 per clique (no triangle), a clique with 2 forces both neighbouring cliques to be empty, and not all 5 cliques can be hit (an induced 5-cycle). An induced tree is acyclic, so tree(G) ≤ 4 < 5. The `largestInducedTreeSize` and `distEven` definitions are restated from FormalConjecturesForMathlib with targeted imports.

Axioms: `[propext, Classical.choice, Quot.sound]`
