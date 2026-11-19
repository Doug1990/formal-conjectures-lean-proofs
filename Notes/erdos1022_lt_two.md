# Erdos1022.erdos_1022.variants.lt_two

- Source: `FormalConjectures/ErdosProblems/1022.lean:71` (category research solved)
- Statement: `∀ (t : ℕ) (c : ℝ), SparseImpliesPropertyB t c → c < 2`
- Defs restated locally (`Finset.HasPropertyB`, `Finset.hypergraphInduce`, `SparseImpliesPropertyB`) with targeted Mathlib imports; the `@[category]` attribute is dropped.

**Proof idea.** If c ≥ 2, take k = t+1 and build a k+1-uniform, "2-degenerate", non-2-colourable family (a Wood-type construction). Base W = {0,…,2k}. For every pair (P,P') of k-subsets of W there is an apex vertex ap(P,P') with the edges P∪{ap}, P'∪{ap}. L1 is the set of these apexes. For every pair (P ⊆ W, Q ⊆ L1) of k-subsets there is a second-level apex with the edges P∪{ap}, Q∪{ap}. Apexes are `Nat.pair (Σ2^i over P) (Σ2^i over Q) + 1`. This is injective and larger than every element of P and Q. Sparsity: every edge inside X has its apex in X minus min X, and each apex has ≤ 2 edges, so the count is ≤ 2(|X|−1) < 2|X| ≤ c|X|. Non-colourability: some colour c has k+1 vertices R in W. All apexes (P0,P) with P0,P ⊆ R get the other colour, and there are ≥ k+1 of them. Pick k of them as Q. Then the apex of (P0,Q) can have neither colour.

The same file also proves the main `Erdos1022.erdos_1022` (`1022.lean:59`, research solved). If c_t → ∞, then eventually c_t ≥ 2, which contradicts `lt_two`.

Axioms (both theorems): `propext, Classical.choice, Quot.sound`

Verified as work/erdos1022_lt2.lean on 2026-11-05 (3 compiles). This file is a hand copy and was not compiled separately.
