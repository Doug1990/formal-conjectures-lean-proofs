# wowii5

- Statement: `WrittenOnTheWallII.GraphConjecture5.conjecture5` (category research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture5.lean:45`
- Claim: for a connected graph G, Ls(G) ≥ max over centres v of |{w : dist(v,w) = rad(G)}|.

Proof idea: fix a centre v and let r = ecc(v) = rad(G) ≥ 1. For every w ≠ v, pick a parent p(w) with
dist(v,p(w)) = dist(v,w) − 1. Let H ≤ G keep all G-edges inside the ball {dist < r} and, for each w on
the sphere {dist = r}, only the edge {w, p(w)}. H is connected (induction on the distance from v).
Take any spanning tree T ≤ H (Mathlib `Connected.exists_isTree_le`). A sphere vertex has at most one
H-neighbour, and at least one T-neighbour because T is connected on ≥ 2 vertices, so it is a leaf of T.
Hence |sphere| ≤ #leaves(T) ≤ Ls(G) (via `toSubgraph` and `spanningCoeEquivCoeOfSpanning`). The outer
sSup is handled by `Real.sSup_le` and `Ls ≥ 0`. Ls is restated verbatim from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SpanningTree.lean (targeted Mathlib imports).
Reusable: `parent_ex` (BFS parent), `key` (OUTER SPHERE OF ANY v WITH ALL dist ≤ r ⇒ |S| ≤ Ls), `Ls_nonneg`.

Axioms: `'WrittenOnTheWallII.GraphConjecture5.conjecture5' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-18
