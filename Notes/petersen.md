# BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.petersen

- Source: `FormalConjectures/Wikipedia/BergeFulkersonConjecture.lean:111` (category research solved; Petersen's theorem, 1891)
- Statement: every finite cubic bridgeless simple graph has a perfect matching.
- Defs restated locally: `SimpleGraph.IsBridgeless` (from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cycle.lean) and `IsCubic`, both verbatim. The theorem statement itself is unchanged.

## Proof idea
Use Mathlib's Tutte theorem (`SimpleGraph.tutte`), so it suffices that no u ⊆ V is a Tutte violator. For an odd component C of G − u, count the ordered pairs (x, y) with x ∈ C and G.Adj x y. This count is 3|C| (odd), and it splits into the pairs inside C (an even number, by the swap involution ordered by `Fintype.equivFin`) plus the pairs leaving C. So the number of leaving pairs is odd. If it were 1, the unique leaving edge would be a bridge: a walk avoiding it would have to cross the boundary of C (`Walk.exists_boundary_dart`) along another leaving edge. So every odd component has ≥ 3 leaving edges, and all of them end in u (otherwise the neighbour lies in the same component of G − u). These edge sets are disjoint for distinct components and inject (via swap) into the pairs starting in u, of which there are 3|u|. So 3·#odd ≤ 3|u|.

## Axioms
`propext, Classical.choice, Quot.sound`

## Date
2026-11-10 (3 compiles for the statement plus 1 axioms check)
