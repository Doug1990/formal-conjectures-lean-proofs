# WrittenOnTheWallII.GraphConjecture17.conjecture17

- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture17.lean:44` (category research solved)
- Statement: for a connected finite graph G, α(G) + ⌈diam(G)/3⌉ ≤ b(G), where b(G) is the size of a largest induced bipartite subgraph.
- `b` / `largestInducedBipartiteSubgraphSize` / `induce_isBipartite_iff_exists_coloring` are restated verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean`.

## Proof idea
Take u, v with dist(u,v) = diam = d and a shortest walk p from u to v, so dist(u, p_k) = k for k ≤ d (from take/drop lengths and the triangle inequality). Take a maximum independent set I. Consecutive walk vertices are adjacent, so I never contains two consecutive p_k. A greedy lemma on ℕ (`comb`, by strong induction) gives a set S of indices with p_i ∉ I, pairwise index gaps ≥ 2 and d ≤ 3|S|. Since dist(u,·) changes by at most 1 along an edge, vertices p_i, p_j with |i−j| ≥ 2 are non-adjacent, so T = p(S) is independent, disjoint from I, and |T| = |S|. Then I ∪ T is 2-coloured by "in I or not", so b(G) ≥ |I| + |T| ≥ α(G) + ⌈d/3⌉.

## Axioms
'WrittenOnTheWallII.GraphConjecture17.conjecture17' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-18
