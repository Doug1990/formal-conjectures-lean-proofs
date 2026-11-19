# wowii145

- Statement: `WrittenOnTheWallII.GraphConjecture145.conjecture145`
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean:88` (research solved)
- Claim: for connected G with lMin(Gᶜ) > 0, 2·ecc(B) ≤ tree(G)·lMin(Gᶜ), where B = maximum-eccentricity vertices.

## Proof idea
Let D = diam(G) with diametral pair x, y (both in B). A geodesic induces a tree, so tree(G) = T ≥ D + 1. For any vertex u ∉ B, dist(u, q) < D for all q. If L = lMin(Gᶜ) ≥ 2, then 2·dist(u, x) ≤ 2D ≤ T·L. If L = 1, some vertex v has an independent-number-1 non-neighbourhood in G, so every vertex is within distance 2 of v (a non-neighbour c and its G-neighbour w would otherwise give an independent pair in Gᶜ[N(v)]), which gives D ≤ 4. For D ≤ 3, or dist(u,x) ≤ 2, or dist(u,y) ≤ 2, the bound is arithmetic. In the remaining case (D = 4, dist(u,x) = dist(u,y) = 3), lemma `six` builds a 6-vertex induced tree from the two length-3 geodesics u–m1–n1–x and u–m2–n3–y by unique-neighbour insertions. All non-adjacencies follow from 1-Lipschitz distance facts plus omega, in three cases (common middle vertex / m1 ~ m2 / neither). So T ≥ 6 and 2·3 ≤ T. Finally, `eccSet_le` turns the pointwise bound into the bound on eccSet.

The checkout definitions (largestInducedTreeSize, indepNeighborsCard, maxEccentricityVertices, distToSet, eccSet) are restated verbatim with targeted imports. Connectivity is used.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-19
