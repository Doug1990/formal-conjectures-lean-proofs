# Erdos494.erdos_494.variants.k_eq_2_card_pow_two

- Source: `FormalConjectures/ErdosProblems/494.lean:69` (category research solved, Selfridge–Straus counterexamples for k = 2, |A| = 2^l)
- Definitions `sumMultiset` and `Erdos494Unique` are restated verbatim (targeted imports, no FormalConjecturesUtil).

Proof idea: the doubling construction. Start with A₀ = {0}, B₀ = {1} (no 2-subsets, so both 2-sum multisets are empty). Given A, B ⊆ [0, d) with the same 2-sums, set A' = A ∪ (B + d), B' = B ∪ (A + d). For disjoint X, Y the 2-sum multiset is S(X ∪ Y) = S(X) + S(Y) + X(X, Y) with the cross sums X(X, Y) (proved by Finset induction from `powersetCard_succ_insert`); translation gives S(B + d) = S(B) + 2d and X(A, B + d) = X(A, B) + d, and X is symmetric. So S(A') = S(B'). Elements below d show A' ≠ B' from A ≠ B, and the cards double. The ℕ-sets are then cast into ℂ (2-sums commute with the cast).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-12. Compiles: 4 (2 with errors, 1 clean, 1 clean + axioms).
