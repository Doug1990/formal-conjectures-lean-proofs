# Erdos30.erdos_30.variants.erdos_turan

- Source: `FormalConjectures/ErdosProblems/30.lean`, line 79 (category research solved, Erdős–Turán 1941).
- Statement: `∃ C, ∀ᶠ N, h N ≤ √N + C·N^{1/4}`, where `h N` is the maximum size of a Sidon subset of `{1,…,N}`.

Proof idea: same core as `results/erdos329_turan.lean`. For a Sidon set `S ⊆ [1,N]`, `|S| = k`,
`M > 0`, the additive energy with `[0,M)` is ≤ `kM + M²`, so Mathlib's Cauchy–Schwarz
`Finset.le_card_add_mul_addEnergy` gives `k²M ≤ (N+M)(k+M)`, hence
`k ≤ N/M + 1 + √(N+M) ≤ N/M + 1 + √N + M/(2√N)`. With `q = N^{1/4}` and `M = ⌈q³⌉`
each of `N/M`, `1`, `M/(2√N)` is ≤ `q`, giving `C = 3` for all `N ≥ 1`. `h N` is realised by
`Finset.exists_mem_eq_sup` on the (nonempty, contains ∅) family of Sidon subsets. `IsSidon`, its
`Decidable` instance and `maxSidonSubsetCard` are restated verbatim from FormalConjecturesForMathlib.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29. Compiles: 1.
