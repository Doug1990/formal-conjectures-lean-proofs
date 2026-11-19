# Erdos264.erdos_264.variants.ko_tao_neg

- Source: `FormalConjectures/ErdosProblems/264.lean:81` (category research solved, Kovač–Tao 2024)
- Statement: a strictly increasing positive sequence with Σ 1/a_n < ∞ and
  liminf a_n² Σ_{k>n} 1/a_k² > 0 is not an irrationality sequence.
- Lean file: `results/erdos264_kotao.lean` (verified copy of `work/erdos264_kotao.lean`)

## Proof idea
Pick K ≥ 4/C and a shift N past the threshold of the liminf hypothesis with N ≥ K+1, so
a_n ≥ K+1 for n ≥ N. For n ≥ N choose b_n ∈ {1, …, K+1}, giving terms 1/(a_n + j + 1) with
j ≤ K. A generalised greedy lemma (the one from `erdos264_i`, but the gap condition now
compares a step at index n with the whole tail spread Σ_{m>n}(f m 0 − f m K)) shows that
every value between the all-low and all-high tail sums is attained. The gap condition holds
because each step at n is ≤ 1/a_n², and each tail term spread is ≥ (K/4)/a_m², so the tail
spread is ≥ (K/4)·C/a_n² ≥ 1/a_n². Take b_n = 1 for n < N and a rational q strictly inside
the attainable interval (shifted by the finite head sum); the series then sums to q.
The subtype tsum over `Set.Ioi n` is reindexed via an explicit equivalence ℕ ≃ Ioi n.

## Axioms
`'Erdos264.erdos_264.variants.ko_tao_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-01. Compiles: 2.
