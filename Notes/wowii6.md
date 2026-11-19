# wowii6

- Statement: `WrittenOnTheWallII.GraphConjecture6.conjecture6` (category research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture6.lean:42`
- Claim: for a connected graph G, `1 + n − μ(G) − α(G) ≤ Ls(G)` (Ls = max number of leaves of a spanning tree, μ = matching number, α = independence number).

## Proof idea

Both one-sided bounds `Ls ≥ n + 1 − 2μ` and `Ls ≥ n + 1 − 2α` hold. Their average gives the claim, since `min(2μ, 2α) ≤ μ + α`.
They share one PAIR GREEDY. Start from S = {s} and repeatedly pick x ∈ N(S) \ S and y ∈ N(x) not dominated by S, then add both to S. This keeps S connected, makes Y = {s, y_1, …, y_k} independent and {x_i y_i} a matching, with |S| = 2k + 1. Stop once S dominates the target set.
A connected dominating S gives a spanning tree in which every vertex outside S is a leaf, so Ls ≥ n − |S|. Each outside vertex keeps only one edge to S, and the tree is taken inside that graph.
For the α-bound, run the greedy in G, so |S| = 2|Y| − 1 ≤ 2α − 1.
For the μ-bound, let r be a vertex farthest from some u (so G − r stays connected along shortest walks) and s a neighbour of r. Run the greedy in G − r from s and add the edge rs to the matching. That gives k + 1 matching edges with |S| = 2k + 1, and r is dominated by s. So n − |S| = n + 1 − 2(k+1) ≥ n + 1 − 2μ.
Ls, matchingNumber and the `α(·)` notation are restated locally from FormalConjecturesForMathlib.

## Axioms

`'WrittenOnTheWallII.GraphConjecture6.conjecture6' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-18. 3 compiles (1: Subgraph `symm` is now `Std.Symm`, a `Reachable.mono` argument needed an explicit `≤` statement, and a `beta_reduce` was missing; 2: clean apart from lints; 3: + axioms).
