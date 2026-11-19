# Erdos329.erdos_329.variants.turan_1941

- Source: `FormalConjectures/ErdosProblems/329.lean`, line 85 (category research solved, Erdős–Turán 1941).
- Statement: every Sidon set `A ⊆ ℕ` has `limsup |A ∩ [1,N]| / √N ≤ 1`.

Proof idea: for a finite Sidon set `S ⊆ [1,N]` with `k = |S|` and any `M > 0`, the additive
energy of `S` with `[0,M)` is at most `kM + M²` (diagonal `a₁ = a₂` gives `kM` quadruples; off the
diagonal the map to `(b₁,b₂)` is injective, because the Sidon property fixes `(a₁,a₂)` from
`a₁ − a₂ = b₂ − b₁`). Mathlib's Cauchy–Schwarz `Finset.le_card_add_mul_addEnergy` with
`|S + [0,M)| ≤ N + M` gives `k²M ≤ (N+M)(k+M)`, so `k ≤ N/M + 1 + √N + √M`. With
`M = ⌈6/ε⌉·(⌊√N⌋+1)` this is `≤ (1+ε)√N` for large `N`. Then `limsup_le_of_le` (cobounded since
the sequence is nonnegative) and `le_of_forall_pos_le_add` finish. `IsSidon` and the two density
definitions are restated verbatim (the checkout's `FormalConjecturesUtil` is not built here).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29. Compiles: 3.
