# Erdos349.alpha_gt_two_not_isGoodPair

- Source: FormalConjectures/ErdosProblems/349.lean:97 (category research solved)
- Statement: for t > 0 and α > 2, the sequence ⌊tα^n⌋ is not additively complete.

Proof idea: a_n = ⌊tα^n⌋ is nonnegative and monotone. Lemma `gap`: an integer k with
a_0+⋯+a_{n-1} < k < a_n is not a sum of distinct terms (every used term is < a_n, hence of
index < n, so the sum is at most the partial sum). Using the geometric sum
(Σ_{m<n} α^m)(α−1) = α^n − 1, one gets t·Σα^m ≤ tα^n − X as soon as X(α−1) < α^n·t(α−2),
which holds for large n (α^n unbounded). With X = |N|+2, k = a_n − 1 is ≥ N and lies in the
gap, contradicting completeness. `subsetSums` / `IsAddComplete` restated locally with the same
bodies (FormalConjecturesUtil is not built here); targeted Mathlib imports.

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-10-30
