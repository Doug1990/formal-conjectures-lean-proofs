# wowii4

- Statement: `WrittenOnTheWallII.GraphConjecture4.conjecture4` (Ls(G) ≥ NG(G) − 1 for connected G).
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture4.lean:44` (category research solved).
- Definitions `Ls`, `non_edge_neighborhood_card` and `NG` are restated verbatim from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{SpanningTree,Degrees}.lean`.
  The type variable is named `V` instead of `α`; the statement is otherwise unchanged.

## Proof idea
If G is complete, the star at any vertex is a spanning tree with n − 1 leaves, and NG = n.
Otherwise, the first three vertices of a shortest path between two non-adjacent vertices give an
induced path u − w − v, so NG ≤ |N(u) ∪ N(v)|. The double star F joins u to all of N(u), and v to w
and to N(v) \ N(u). F is acyclic: each edge is a bridge, shown by a cut that only this edge crosses
(`bridge_cut` via `Walk.exists_boundary_dart`). Mathlib's
`Connected.exists_isTree_le_of_le_of_isAcyclic` extends F to a spanning tree T, so
deg_T u ≥ |N(u)| and deg_T v ≥ |N(v) \ N(u)| + 1. For any tree and distinct u, v, the handshake
identity Σ deg = 2(n − 1) with deg ≥ 1 gives deg u + deg v ≤ #leaves + 2. Hence
#leaves ≥ |N(u) ∪ N(v)| − 1 ≥ NG − 1. Finally `Ls_ge` (#leaves of any spanning tree T ≤ G is ≤ Ls G)
transfers this to Ls.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Date: 2026-11-18. 5 compiles (4 to a clean build, 1 with `#print axioms`).
