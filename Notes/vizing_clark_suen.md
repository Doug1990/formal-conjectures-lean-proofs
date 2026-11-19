# vizing_conjecture.variants.clark_suen

- Statement: `VizingConjecture.vizing_conjecture.variants.clark_suen` (category research solved, Clark–Suen 2000)
- Source: `FormalConjectures/Wikipedia/VizingConjecture.lean:65`
- Statement: γ(G)·γ(H) ≤ 2·γ(G □ H) for finite simple graphs G, H.
- The definitions `IsDominating`, `IsNDominatingSet`, `dominationNumber` (and the two helper lemmas
  `exists_isNDominatingSet_dominationNumber`, `dominationNumber_le_of_isDominating`) are copied
  unchanged from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean`,
  because `FormalConjecturesUtil` is not importable here. Targeted Mathlib imports.

## Proof idea
Take a minimum dominating set U of G (|U| = γ(G)) with a choice map f : V(G) → U,
f(g) = g or g ~ f(g), and a minimum dominating set D of G □ H. For u ∈ U let D_u be the part of
D over the cell f⁻¹(u) and P_u its projection to H. Call cell (u, h) vertically dominated if
h ∈ N_H[P_u]. (1) For each u, P_u together with the non-vertically-dominated h dominates H, so
γ(H) ≤ |D_u| + n_u. (2) For each h, the projection to G of D ∩ (V(G) × {h}) plus the u with
(u, h) vertically dominated dominates G (a vertex in a non-vertically-dominated cell can only be
dominated horizontally), so by minimality of U the number of non-vertically-dominated cells in
column h is ≤ |D ∩ (V(G)×{h})|. Summing (1) over u and (2) over h (Finset.sum_comm) gives
γ(G)γ(H) ≤ |D| + |D| = 2γ(G □ H).

## Axioms
`'VizingConjecture.vizing_conjecture.variants.clark_suen' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-03, 3 compiles.
