# wowii13

- Statement: `WrittenOnTheWallII.GraphConjecture13.conjecture13` (research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture13.lean:45`
- Claim: for connected G, diam(G) + max_v α(N(v)) − 1 ≤ b(G).

Proof idea: pick v with α(N(v)) = L maximal and an independent I ⊆ N(v) with |I| = L. Take a
diametral geodesic q_0 = u, …, q_d, so dist(u, q_i) = i, and let k = dist(u, v). Then every a ∈ I has
dist(u, a) ∈ [k−1, k+1]. Let S = {v} ∪ I ∪ {q_i : |i − k| ≥ 2}. This has ≥ 1 + L + (d + 1 − 3)
vertices, all distinct. Colour q_i by i mod 2, v by k mod 2 and every vertex of I by (k+1) mod 2.
The colouring is proper on S: v is not adjacent to the remaining q_i (their layers are too far
away), I is independent, and an I-vertex can only touch q_{k±2}, whose parity is k. Two q's are
adjacent only when their indices differ by exactly 1. So b ≥ L + d − 1. (The plain BFS-from-v
argument noted in the 2026-11-18 survey only gives ecc(v) + L.) The definitions b,
largestInducedBipartiteSubgraphSize, induce_isBipartite_iff_exists_coloring and indepNeighborsCard
are restated locally from FormalConjecturesForMathlib.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-18
