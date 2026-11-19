# wowii18

- Statement: `WrittenOnTheWallII.GraphConjecture18.conjecture18`
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture18.lean:48` (category research solved, Benny John 2006)
- Claim: for connected G, α(G) + ⌈√dist_max(M)⌉ ≤ b(G), where M is the set of maximum-degree vertices.

## Proof idea
Take u, v ∈ M with dist(u,v) = D and a maximum independent set I. Any independent set T disjoint
from I gives α + |T| ≤ b (colour classes I and T). The geodesic argument of conjecture 17, applied to
u and v, gives α + s ≤ b with D ≤ 3s, which is enough unless D ∈ {2,3,5,6}. The new ingredient is the
key lemma: a maximum-degree vertex u that has some vertex at distance ≥ 2 has two non-adjacent
neighbours x, y. Otherwise N(u) is a clique, and the geodesic neighbour p1 would be adjacent to
N(u)∖{p1}, u and p2, so deg p1 ≥ Δ+1. For D ≥ 2: if u (or v) ∈ I, take T = {x, y}; otherwise
T = {u, v}. For D ≥ 5: if u ∈ I, take T = {x, y, w} with w ∈ {p3, p4}∖I (dist(u,w) ≥ 3, so w is not adjacent to x or y).
If u, v ∉ I, take T = {u, p_k, v} with p_k ∈ {p2, p3}∖I. Then √D ≤ k with D ≤ k² finishes the proof.
Definitions b, largestInducedBipartiteSubgraphSize and distMaxSet are restated verbatim (namespace SimpleGraph).

## Axioms
'WrittenOnTheWallII.GraphConjecture18.conjecture18' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-18. 2 compiles. Only lint warnings remain (an unused DecidableEq in `hex`, and the statement's own Nontrivial).
