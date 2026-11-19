# wowii63

- Statement: `WrittenOnTheWallII.GraphConjecture63.conjecture63` (disproof of f ≥ ⌈(min_v distEven(v) + b + 1)/3⌉)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture63.lean:48` (research solved; an external formal proof is linked upstream)

Proof idea: the docstring's counterexample C₅[K₄] on `Fin 20` (vertex i lies in clique i/4, and cliques c and c+1 mod 5 are fully joined), with adjacency given by linear ℕ formulas so that `omega` does all the case work. Connectivity and dist = 2 for distinct non-adjacent vertices use an explicit common neighbour `mid`. The 9 non-neighbours (including v itself) are all at even distance, so distEven ≥ 9 (`decide` counts them). b ≥ 4 comes from {0,1,8,9}, coloured by parity. f ≤ 4 holds because in an induced forest each clique holds ≤ 2 vertices (triangle), a clique with 2 vertices forces both neighbouring cliques to be empty (triangle), and not all 5 cliques can be hit (5-cycle, via a bridge argument). Then ⌈(9+4+1)/3⌉ = 5 > 4. The checkout definitions (largestInducedForestSize, largestInducedBipartiteSubgraphSize, b, distEven) are restated verbatim with targeted Mathlib imports.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-18
