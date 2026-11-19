# Erdos1122.erdos_1122.variants.monotone

- Source: `FormalConjectures/ErdosProblems/1122.lean:66` (category research solved, Erdős 1946)
- Statement: an additive f : ℕ → ℝ (f(ab) = f(a) + f(b) for coprime a, b > 0) with f(n) ≤ f(n+1) for all n ≥ 1 is c·log n on n > 0.
- Verified file: `work/erdos1122_mono.lean` (identical copy here), targeted import `Mathlib.Analysis.SpecialFunctions.Log.Basic`.

## Proof idea
f(1) = 0, so f ≥ 0 and f is monotone on n ≥ 1. Since m^k is coprime to m−1 and m+1 and
m^k(m−1) ≤ m^{k+1} ≤ m^k(m+1), induction gives k·f(m−1) ≤ f(m^k) ≤ k·f(m+1). Comparing m^k ≤ n^j with
j = ⌈k·log m/log n⌉ and letting k → ∞ gives f(m−1)·log n ≤ f(n+1)·log m for all m, n ≥ 2. With
C = sup_m f(m−1)/log m this yields C·log(x−1) ≤ f(x) ≤ C·log(x+1), so h = f − C·log satisfies
|h(x)| ≤ C/(x−1) for x ≥ 3. h is additive, so h(n) = h(n(kn+1)) − h(kn+1) gives |h(n)| ≤ 2C/k for every
k ≥ 2, hence h(n) = 0. Complete additivity at prime powers is never needed.

Reusable helpers (namespace `Erdos1122.M`): `f_one`, `mono`, `nonneg`, `pow_bounds`, `limit_arg`
(∀k≥1, kA ≤ (kL+1)B ⇒ A ≤ LB), `ratio`, `log_gap`.

## Axioms
`'Erdos1122.erdos_1122.variants.monotone' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-09. 3 compiles.
