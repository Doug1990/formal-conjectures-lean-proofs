# sidorenko_cycle

- Statement: `SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle` (category research solved, Sidorenko 1993)
- Source: `FormalConjectures/Wikipedia/SidorenkoConjecture.lean:794` in the checkout
- Date: 2026-11-03

## Proof idea
Let A be the real adjacency matrix of G, N = |W|, D = Σ_{ij} A_ij = 2e(G). Closed walks of length n = 2k
inject into homomorphisms C_n → G (vertex i ↦ getVert i, wrap-around edge from getVert n = getVert 0;
injective by `Walk.ext_getVert_le_length`), so tr(Aⁿ) ≤ hom(C_n, G) via `adjMatrix_pow_apply_eq_card_walk`.
Spectral theorem (`IsHermitian.spectral_theorem`): A = U·diag(λ)·Uᵀ with U orthogonal, so tr(A^{2k}) = Σ λ_l^{2k},
and with c_l = Σ_i U_il we get D = Σ λ_l c_l², N = Σ c_l². Hence D/N ≤ max|λ|, so
(D/N)^{2k} ≤ max λ^{2k} ≤ tr(A^{2k}) ≤ hom(C_{2k}, G). Dividing by N^{2k} gives t(K₂,G)^{2k} ≤ t(C_{2k},G), with
e(C_{2k}) = 2k from the degree sum. `homCount` / `homDensity` are restated locally (same definitions as
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/HomDensity.lean).

## Axioms
`'SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles: 3 (1: two errors, a simp order issue with `mul_diagonal` and a dependent `rw` on a walk-length subtype; 2: clean; 3: + axioms). The results copy was written by hand from the verified work file and not compiled separately.
