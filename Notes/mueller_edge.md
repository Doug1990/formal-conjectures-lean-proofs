# ReconstructionConjecture.edge_reconstruction_conjecture.variants.mueller

- Source: `FormalConjectures/Wikipedia/ReconstructionConjecture.lean:179` (category research solved, Müller 1977)
- Statement: if `n! < 2^(m−1)` with m = |E(G)| and `G`, `H` (same vertex type) are edge-hypomorphic, then `G ≃g H`.

## Proof idea
This reuses the framework from `lovasz_edge` (Kelly's lemma for edges, `N_eq`). Suppose G ≇ H. Then no
permutation maps E(G) into E(H), so N_H(E(G)) = 0, while N_G(E(G)) ≥ 1. Inclusion–exclusion with a
fixed base set A ⊆ E(G) (`incl_excl'`) gives Σ_{B ⊆ E(G)∖A} (−1)^{|B|} N_K(A ∪ B) = M_K(A), where
M_K(A) = #{σ : σ(A) ⊆ E(K), σ(E(G)∖A) ∩ E(K) = ∅}. All terms with A ∪ B ≠ E(G) agree for G and H,
so M_G(A) − M_H(A) = (−1)^{|E(G)∖A|} N_G(E(G)). Hence M_G(A) ≥ 1 whenever |E(G)∖A| is even (`M_pos`).
Choosing one σ for each such A gives an injection (σ determines A = {f : σf ∈ E(G)}) from the
2^(m−1) "even" subsets into Sym(V), so 2^(m−1) ≤ n!. The case m = 0 contradicts n! ≥ 1. The lower
bound 2^(m−1) is the injection B ↦ B or insert e₀ B from subsets of E(G)∖{e₀}.

Axioms: `propext, Classical.choice, Quot.sound`

Verified: 2026-11-03 (work/mueller_edge.lean, 1 compile). `EdgeHypomorphic` is restated locally.
