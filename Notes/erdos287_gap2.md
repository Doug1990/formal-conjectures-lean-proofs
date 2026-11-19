# Erdos287.erdos_287.variants.gap_at_least_two

- Source: `FormalConjectures/ErdosProblems/287.lean:57` (category research solved; the classical fact that 1 is never a sum of reciprocals of k ≥ 2 consecutive integers, Theisinger/Kürschák, cited as Erdős [Er32]).
- File: `results/erdos287_gap2.lean` (targeted imports, `max_gap` restated verbatim, statement unchanged).

**Proof idea.** Suppose max_gap < 2. Since s is strictly increasing, every gap is exactly 1, so s i = a + i with a = s 0 ≥ 2. The sum moves to ℚ via `Rat.cast_injective`. Among the consecutive integers a, …, a+k−1, choose one, x₀, with the largest 2-adic valuation v. It is the only one with that valuation: between two distinct multiples of 2^v lies a multiple of 2^(v+1) (lemma `between`). Since k ≥ 2 some term is even, so v ≥ 1. Each other term 1/x has valuation > −v, so their sum does too (lemma `val_sum`, using `padicValRat.min_le_padicValRat_add`). By `padicValRat.add_eq_of_lt` the whole sum has valuation −v ≠ 0, but `padicValRat 2 1 = 0`, a contradiction. Reusable: `between`, `val_sum`, `core` (Σ_{j<k} 1/(a+j) ≠ 1 for a ≥ 1, k ≥ 2).

**Axioms:** `'Erdos287.erdos_287.variants.gap_at_least_two' depends on axioms: [propext, Classical.choice, Quot.sound]`

**Date:** 2026-10-31. Compiles: 3 (1: a no-op `simp only` and a missing `omega`; 2: only an unused `beta_reduce` lint; 3: clean + axioms).
