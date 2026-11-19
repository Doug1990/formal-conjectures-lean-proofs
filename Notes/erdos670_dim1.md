# Erdos670.erdos_670.variants.dim_one

- Source: `FormalConjectures/ErdosProblems/670.lean:66` (category research solved, Erdős [Er97f])
- Verified file: `results/erdos670_dim1.lean` (copy of `work/erdos670_dim1.lean`, compiled clean)
- `HasSeparatedDistances` restated locally, identical to the source definition; targeted Mathlib imports.

## Proof idea
Map the points of A ⊆ ℝ¹ isometrically to ℝ (p ↦ p 0) and list them in increasing order
x_0 < … < x_{n−1} (`Finset.orderEmbOfFin`). Fix a window m = ⌈2/ε⌉ and look at the m(n−m)
differences x_{i+k} − x_i with 1 ≤ k ≤ m and i < n − m. They come from distinct pairs, so they
are nonnegative and pairwise at least 1 apart, and their sum is ≥ M(M−1)/2 with M = m(n−m)
(`sum_sep`, induction on the maximum). For each fixed k the sum over i telescopes to at most k·D,
where D = x_{n−1} − x_0 ≤ diam A (`tele`, `tele_le`). So M(M−1)/2 ≤ D·m(m+1)/2. Since
(m+1)(1−ε) ≤ m−1 when εm ≥ 2, this gives D ≥ (1−ε)n² once n − m ≥ 2m² + m³ + 1 (`arith`).
Reusable: sum_sep, tele, tele_le, core (window counting for an abstract sequence), de (dist on
EuclideanSpace ℝ (Fin 1)).

## Axioms
'Erdos670.erdos_670.variants.dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]

## Date
2026-11-02
