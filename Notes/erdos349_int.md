# Erdos349 integer-pair chain

- Source: FormalConjectures/ErdosProblems/349.lean
  - exists_finsetSum_two_pow (:119, textbook)
  - one_two_isGoodPair (:128, research solved)
  - dyadic_two_isGoodPair (:138, research solved)
  - alpha_le_one_not_isGoodPair (:108, research solved)
  - int_coeff_ge_two_not_isGoodPair (:149, research solved)
  - integer_isGoodPair_iff (:161, research solved; main target of this file)
  - also contains alpha_gt_two_not_isGoodPair (:97), see erdos349_gt_two.md

Proof idea: binary expansion via `Nat.bitIndices` gives completeness of the powers of two,
so (1,2) is good; (1/2^k, 2) is good because its range contains every 2^m (index m+k).
For α ≤ 1 all terms lie in [0, ⌊t⌋], so subset sums are bounded by Σ_{Icc 0 ⌊t⌋} i. For integer
t ≥ 2 and integer α every term is t·α^n, so all subset sums are multiples of t, but |N|·t+1 is not.
For α > 2 a gap lemma plus the geometric sum. The iff assembles: α = 1 fails, α ≥ 3 fails,
t ≥ 2 fails, so (t,α) = (1,2), which is good. `subsetSums` / `IsAddComplete` restated locally
with the same bodies; targeted Mathlib imports. The statement `IsAddComplete.mono` was not
needed (dyadic case done by `filter_upwards`).

Axioms (all six theorems): [propext, Classical.choice, Quot.sound]

Date: 2026-10-30
