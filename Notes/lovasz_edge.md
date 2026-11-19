# ReconstructionConjecture.edge_reconstruction_conjecture.variants.lovasz

- Source: `FormalConjectures/Wikipedia/ReconstructionConjecture.lean:165` (category research solved, Lovász 1972)
- Statement: if `C(n,2) < 2·|E(G)|` and `G`, `H` (on the same vertex type) are edge-hypomorphic, then `G ≃g H`.

## Proof idea
For a set of edges `F`, let `N_K(F)` be the number of permutations σ of `V` with σ(F) ⊆ E(K).
Kelly's lemma for edges (`kelly`): Σ_{e∈E(K)} N_{K−e}(F) = (|E(K)| − |F|)·N_K(F). `N` does not
change under graph isomorphism (`N_iso`), so edge-hypomorphic graphs have N_G(F) = N_H(F) whenever
|F| < m = |E(G)| (`N_eq`). Inclusion–exclusion over F ⊆ E(G) (`incl_excl`) gives
Σ_F (−1)^{|F|} N_K(F) = #{σ : σ(E(G)) ∩ E(K) = ∅}. When 2m > C(n,2) this count is 0 for
K = G and K = H, so the terms with F = E(G) agree too: N_H(E(G)) = N_G(E(G)) ≥ 1. A permutation
with σ(E(G)) ⊆ E(H) is an isomorphism, since both edge sets have m elements.

Axioms: `propext, Classical.choice, Quot.sound`

Verified: 2026-11-03 (work/lovasz_edge.lean, 5 compiles). `EdgeHypomorphic` is restated locally because the file imports targeted Mathlib modules, not FormalConjecturesUtil.
