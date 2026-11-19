# erdos684_lower

- Statement: `Erdos684.erdos_684.lower_bound` (research solved, APSSV26 Thm 2.1, weak form with coefficient 1/8)
- Source: `FormalConjectures/ErdosProblems/684.lean:62` in the checkout
- Date: 2026-11-17

## Proof idea
Take K large and n = M − 1 with M = lcmUpto(K) · primorial(K). Every prime p ≤ K then has p^(log_p K + 1) ∣ n+1, and this power exceeds K. A Kummer-type lemma (`KL.not_dvd_choose`, by induction on e through Lucas's theorem `Choose.choose_modEq_choose_mod_mul_choose_div_nat`) says that p^e ∣ n+1 and k < p^e imply p ∤ C(n,k). So for every k ≤ K, every prime p ≤ k has valuation 0 in C(n,k), and smallPrimePart n k = 1. Mathlib's Chebyshev bounds (ψ(K) = log lcmUpto K ≤ (log 4 + 4)K and θ(K) = log primorial K ≤ K log 4) give log n ≤ (2 log 4 + 4)K ≤ 8K, using log 2 ≤ 1. So k ≤ log n / 8 forces k ≤ K. Finally n > K, which makes the set of such n unbounded.

## Axioms
`'Erdos684.erdos_684.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
