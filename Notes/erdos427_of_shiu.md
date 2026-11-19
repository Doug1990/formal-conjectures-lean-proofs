# Erdos427.erdos_427.variants.of_shiu

- Source: `FormalConjectures/ErdosProblems/427.lean:86` (category research solved, Pilatte's observation)
- Statement: `ShiuTheorem → erdos427`. Both defs are restated verbatim from the source, with targeted imports. This is a conditional result: Shiu's theorem stays a hypothesis.
- Verified file: `work/erdos427_of_shiu.lean` (identical copy).

**Proof idea.** Fix n and d ≠ 0. Shiu's theorem with k = q = d and a = 1 gives an m > n such that p_m, …, p_{m+d−1} are all ≡ 1 mod d. Let S = Σ_{n ≤ i < m} p_i. Then Σ_{n ≤ i < m+j} p_i ≡ S + j (mod d) for j ≤ d, by induction with `Finset.sum_Ico_succ_top`. Take j = d − (S mod d) ∈ [1, d], so the sum is divisible by d, and use k = m + j − n ≠ 0.

Axioms: `'Erdos427.erdos_427.variants.of_shiu' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-11
