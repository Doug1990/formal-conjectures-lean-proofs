# Erdos619.erdos_619.variants.add_edges_diam_three

- Source: `FormalConjectures/ErdosProblems/619.lean`, line 87 (category research solved, EGR98)
- Date: 2026-11-10

**Proof idea.** Among the finitely many triangle-free supergraphs of `G` on the finite vertex type, pick a maximal one `H` (`Set.Finite.exists_maximal`). If `u ≠ v` are not adjacent in `H`, adding the edge `uv` keeps `G ≤ ·`, so by maximality the result contains a triangle. Since `H` is triangle-free, the triangle must use the new edge, so `u` and `v` have a common neighbour in `H` (lemma `common_nbr`, a 27-way case split on which triangle sides are new). So every pair is at distance ≤ 2, and `ediam H ≤ 2 ≤ 3` via `ediam_le_of_edist_le` + `edist_le` on explicit walks. Connectedness of `G` is not needed (a maximal triangle-free graph on ≥ 2 vertices is automatically connected).

Axioms: `propext, Classical.choice, Quot.sound`
