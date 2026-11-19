# erdos1008_folkman

- Statement: `Erdos1008.erdos_1008.variants.folkman` (category research solved, Folkman's counterexample)
- Source: `FormalConjectures/ErdosProblems/1008.lean:68` in the checkout
- Statement: K_{n,n²} has n³ edges, and every subgraph H of K_{n,n²} with more than n² + C(n,2) edges contains a copy of C₄.

## Proof idea

Part 1 comes from Mathlib's `encard_edgeSet_completeBipartiteGraph` via `Set.ncard_def`. For part 2, suppose H is C₄-free and let D_r be the H-neighbourhood of the right vertex r. All of D_r lies on the left side, and every edge of H has exactly one right endpoint, so |E(H)| ≤ Σ_r |D_r|. Two distinct right vertices r and r' cannot share two distinct left neighbours x and y, because x–r–y–r'–x would be a C₄ (built explicitly as a `Copy` from `![x, inr r, y, inr r']` with `fin_cases`). So the sets offDiag(D_r) are pairwise disjoint subsets of offDiag(left side), which gives Σ_r d_r(d_r−1) ≤ n(n−1) = 2·C(n,2). Since 2d ≤ 2 + d(d−1) for every d, summing over the n² right vertices gives 2|E(H)| ≤ 2n² + 2·C(n,2). This contradicts the hypothesis. Reusable helpers: `FK.of_cycle` (a 4-cycle a b c d with a ≠ c and b ≠ d gives `cycleGraph 4 ⊑ H`), `FK.choose2` (2·C(n,2) = n·n − n), `FK.arith`.

## Axioms

`'Erdos1008.erdos_1008.variants.folkman' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date

2026-11-05. Compiled from work/erdos1008_folkman.lean (2 compiles). The results copy was written by hand from the verified work file and was not compiled separately.
