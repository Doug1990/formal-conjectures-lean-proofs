# Erdos1022.erdos_1022.variants.lovasz

- Source: `FormalConjectures/ErdosProblems/1022.lean:80` (category research solved, Lovász 1968)
- Statement: `IsGreatest {c : ℝ | SparseImpliesPropertyB 2 c} 1`
- Date: 2026-11-05. Kernel-checked from `work/erdos1022_lovasz.lean` (3 compiles). The results copy is a verbatim hand copy of that file.

## Proof idea
Upper bound: for c > 1 the triangle {01, 12, 02} satisfies the sparsity condition (each X spans at most |X| triangle edges, via an injection of edges into X) but has no 2-colouring. Lower bound (Lovász): let e(X) be the number of edges inside X, and assume e(X) < |X| for every nonempty X. Use strong induction on Σ|A|. If some edge A has |A| ≥ 3, replace it by A∖{v} for a suitable v ∈ A. If both v and w fail, there are "tight" sets X ∌ v and Y ∌ w with A∖v ⊆ X, A∖w ⊆ Y and e = |·|−1. Since X∩Y ≠ ∅ and A ⊆ X∪Y but A ⊄ X and A ⊄ Y, supermodularity gives e(X∪Y) ≥ |X∪Y|, a contradiction. A colouring of the shrunken family also colours the original one. If all edges are pairs, double counting (Σ deg = 2|F| < 2|V|) gives a vertex of degree 1. Remove its edge, colour the rest by induction, then recolour that vertex.

## Axioms
`'Erdos1022.erdos_1022.variants.lovasz' depends on axioms: [propext, Classical.choice, Quot.sound]`
