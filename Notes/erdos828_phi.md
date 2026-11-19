# Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3

- Source: `FormalConjectures/ErdosProblems/828.lean:53` (category textbook)
- Statement: `φ n ∣ n ↔ n ≤ 1 ∨ ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b`
- Date: 2026-10-29

## Proof idea
Backward direction: φ(2^a·3^b) = 2^(a−1)·φ(3^b) by multiplicativity and the prime-power formula, which visibly divides 2^a·3^b; n = 0, 1 by `simp`. Forward direction for n ≥ 2: Mathlib's `Nat.totient_mul_prod_primeFactors` (φ(n)·∏p = n·∏(p−1)) turns φ(n) ∣ n into ∏(p−1) ∣ ∏p over the prime factors. Each odd prime factor makes p−1 even, so 2 ∣ ∏p and 2 is a prime factor. The product of distinct primes is not divisible by 4, so there is at most one odd prime factor p. Then (p−1) ∣ 2p, so (p−1) ∣ 2 and p = 3. Hence the support of the factorization is in {2, 3}, and `Finsupp.prod_of_support_subset` gives n = 2^v₂·3^v₃ with v₂ > 0.

## Axioms
`'Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3' depends on axioms: [propext, Classical.choice, Quot.sound]`

Imports are targeted (Mathlib.Data.Nat.Totient, Factorization.Basic, BigOperators.Finsupp.Basic, BigOperators.Associated, Tactic.Ring). The `@[category ...]` attribute is dropped because FormalConjecturesUtil is not built.
