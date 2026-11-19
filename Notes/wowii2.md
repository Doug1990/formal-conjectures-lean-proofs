# wowii2

- Statement: `WrittenOnTheWallII.GraphConjecture2.conjecture2` (research solved). For connected G, Ls(G) ≥ 2·(l(G) − 1), where l(G) is the average independence number of the neighbourhoods.
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture2.lean:64` in the checkout.
- Proof file: `results/wowii2.lean`, an identical copy of `work/wowii2.lean`. The definitions Ls, indepNeighborsCard, indepNeighbors and averageIndepNeighbors are restated locally, and the theorem statement is unchanged.

## Proof idea

This follows the "third proof" sketched in the docstring.

1. Take a triangle-free subgraph H ≤ G with the maximum number of edges (`Finset.exists_max_image` over all subgraphs, using `edgeSet.ncard`).
2. Lemma `switch`: for an independent set I ⊆ N_G(v), replace all H-edges at v by the edges v–I. The result is still triangle-free and still ≤ G. By maximality, |I| ≤ deg_H v, so l(v) ≤ deg_H(v).
3. Lemma `heavy`: double counting plus Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) gives an H-edge uv with (deg u + deg v)·n ≥ 2·Σdeg ≥ 2·Σl.
4. Lemma `dstar_acyclic`: the double star on uv in H is acyclic, because H is triangle-free; every edge is shown to be a bridge with a cut argument. It extends to a spanning tree T of G (`exists_isTree_le_of_le_of_isAcyclic`).
5. The tree handshake gives deg_T u + deg_T v ≤ #leaves + 2 (`leaf_bound`), and `Ls_ge` (both from wowii4) finishes. If H has no edges, then l ≡ 0 and Ls ≥ 0.

## Result

- Axioms: `'WrittenOnTheWallII.GraphConjecture2.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-18
