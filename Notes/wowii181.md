# wowii181

- Statement: `WrittenOnTheWallII.GraphConjecture181.conjecture181` (DISPROOF of `Ls G + b G ≥ α(G) + deg_avg(B(G²))`)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture181.lean:60` (category research solved)
- Date: 2026-11-19

## Proof idea

The counterexample is the triangular graph T(7) = L(K₇), encoded on Fin 21 with endpoint tables pa, pb : Fin 21 → Fin 7. Adjacency means "distinct, sharing an endpoint". Any two vertices are at distance ≤ 2 (checked by `decide`), so G² = K₂₁. The periphery of G² is nonempty (Mathlib `exists_eccent_eq_ediam_of_finite`), and every vertex has square-degree 20, so the average is 20. Lower bound α ≥ 3 comes from the matching {01, 23, 45}. Upper bounds:
- Independent sets have ≤ 3 elements, by double counting the incidences with the 7 points (each point meets at most one set element). Both colour classes of an induced bipartite subgraph are independent, so b ≤ 6.
- Ls ≤ 16. Fix a spanning tree and its leaf set s. The non-leaves I = sᶜ dominate (a leaf's neighbour is not a leaf, by a cut argument), and I is "cut-connected" (any proper nonempty S ⊆ I has a G-edge to I∖S, via the cut S ∪ {leaves hanging on S}). A greedy growth lemma then gives |points covered by I| ≤ |I| + 1. Domination forces ≥ 6 covered points: two uncovered points x, y would make the vertex xy undominated. Hence |I| ≥ 5 and #leaves ≤ 16.

So Ls + b ≤ 22 < 23 ≤ α + avg.

## Axioms

`'WrittenOnTheWallII.GraphConjecture181.conjecture181' depends on axioms: [propext, Classical.choice, Quot.sound]`
