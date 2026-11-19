# Erdős 494: k_eq_card and card_eq_2k

- Statements: `Erdos494.erdos_494.variants.k_eq_card` (∀ k > 2, ¬Erdos494Unique k k) and
  `Erdos494.erdos_494.variants.card_eq_2k` (∀ k > 2, ¬Erdos494Unique k (2k)).
- Source: `FormalConjectures/ErdosProblems/494.lean`, lines 114 and 125 (category research solved).
- Defs `sumMultiset` and `Erdos494Unique` are restated verbatim (targeted imports, no FormalConjecturesUtil).

Proof idea. For |A| = k the multiset of k-sums is the singleton {ΣA} (`powersetCard_self`), so any
two different k-sets with the same total give a counterexample: A = {1,4} ∪ [5, k+3),
B = {2,3} ∪ [5, k+3) (as natural numbers cast into ℂ). For |A| = 2k (Tao): if ΣA = 0, then the
k-sums of −A are −Σs = Σ(A∖s), and s ↦ A∖s is a bijection of the k-subsets of A, so −A and A
have the same k-sum multiset (`KC.neg_multiset`, via `image_val_of_injOn`). Take
A = {1, …, 2k−1} ∪ {−S} with S = 1+…+(2k−1); then −(2k−1) ∈ −A but not in A, since S > 2k−1.

Axioms: `[propext, Classical.choice, Quot.sound]` (both theorems).

Date: 2026-11-11. 2 compiles (1: missing imports for `Nat.cast_sum` and `Finset.Ico`; 2: clean + axioms).
