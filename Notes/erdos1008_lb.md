# erdos1008_lb

- Statement: `Erdos1008.erdos_1008.variants.lower_bound` (category research solved; Erdős calls it trivial)
- Source: `FormalConjectures/ErdosProblems/1008.lean:78` in the checkout
- Statement: there is a c > 0 such that every finite graph G with m edges has a C₄-free subgraph H with at least c·m^(1/2) edges.

## Proof idea

c = 1/2. Take a vertex v of maximum degree Δ and a maximal matching M (a maximum-cardinality family of pairwise disjoint edges of G, via `Finset.exists_max_image`). Every edge of G meets one of the ≤ 2|M| matched vertices, so m ≤ 2|M|·Δ ≤ 2t² with t = max(|M|, Δ). Both the star at v (`fromEdgeSet (G.incidenceSet v)`, Δ edges) and the matching (`fromEdgeSet M`, |M| edges) are C₄-free. A copy of C₄ gives a 4-cycle a b c d with a ≠ c and b ≠ d. In the matching, the edges ab and bc share b, so they are equal, which forces a = c. In the star, ab and cd both contain v, which forces one of a = c, a = d, b = c or b = d. Then (1/2)·√m ≤ t follows from m ≤ (2t)². If V is empty, H = G works. Reusable helpers: `LB.free_of` (C₄-freeness from a 4-cycle criterion), `LB.exists_matching`, `LB.count` (m ≤ 2|M|Δ), and the star/matching subgraph lemmas.

## Axioms

`'Erdos1008.erdos_1008.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date

2026-11-05. Compiled from work/erdos1008_lb.lean (2 compiles). The results copy was written by hand from the verified work file and was not compiled separately.
