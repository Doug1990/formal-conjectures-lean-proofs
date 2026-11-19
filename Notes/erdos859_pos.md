# Erdos859.erdos_859.variants.positive_density

- Source: `FormalConjectures/ErdosProblems/859.lean:74` (category textbook)
- Statement: `∀ t : ℕ, (DivisorSumSet t).HasPosDensity`, where `DivisorSumSet t = {n | ∃ s ⊆ n.divisors, t = ∑ s}`, and `HasPosDensity` means a natural density α > 0 exists.
- Date: 2026-10-29

## Proof idea
For n ≥ 1, whether n is in the set depends only on which d ≤ t divide n, because the summands of t are at most t. Every 1 ≤ d ≤ t divides L = t!, so n + 1 ∈ S ↔ n + 1 + L ∈ S. The shifted predicate k ↦ k+1 ∈ S is therefore L-periodic. A general lemma (count_bound / shift_bound) shows |count(b) − b·c/L| ≤ L + 2, with c the number of hits in one period (via `Nat.count_add`, `Nat.count_succ'`). From this, count(b)/b → c/L. Also c > 0 because L = t! itself is in S (take s = {t}, or s = ∅ for t = 0). The FormalConjecturesForMathlib definitions `partialDensity` / `HasDensity` / `HasPosDensity` are restated locally, unchanged, because FormalConjecturesUtil is not built.

## Axioms
`'Erdos859.erdos_859.variants.positive_density' depends on axioms: [propext, Classical.choice, Quot.sound]`
