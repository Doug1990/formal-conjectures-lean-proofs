# SimpleGraph.theorem2

- Source: FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:287 (category research solved, Erdős–Fajtlowicz–Staton)
- Statement unchanged. `degreeSequence` / `degreeSequenceMultiplicity` are restated locally, verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean.
- Verified file: work/dfs_theorem2.lean. This copy was written out by hand from the verified file and has not been compiled separately.

Proof idea: this is a direct construction and does not go through lemma4. lemma4's statement says nothing about the H-degrees of the new vertices, so theorem2 cannot be derived from it alone. Let n = |G| and e : α ≃ Fin n. Vertex a should end with degree D(a) = n+1+e(a); these values are distinct and larger than deg_G(a). Add a half graph on L ⊔ R with |L| = |R| = N, where l_i ~ r_j iff i+j ≥ N−1. L is the sigma type Σ a, Fin c(a) with c(a) = D(a) − deg_G(a) ≥ 2, so each l has exactly one owner a ∈ G and is joined to it. Degrees: a ↦ n+1+e(a), l_i ↦ i+2, r_j ↦ j+1. Each value therefore occurs at most once per class (≤ 3 in total), and n+1 occurs exactly 3 times (once in each class; this uses N ≥ 2n > n). Triangle-free: every l has a single G-neighbour, L and R are independent, and G has no R-neighbours. The graph is transported to `ULift (Fin M)` for the universe of β. Multiplicity is an isomorphism invariant, and clique-freeness passes back along the embedding (`CliqueFree.comap` + `Embedding.isContained`).

Axioms: `'SimpleGraph.theorem2' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-02. Compile output has only the "unused variable `i`" lint, which comes from the binder in the given statement.
