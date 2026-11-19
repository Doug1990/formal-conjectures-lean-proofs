# AgohGiuga.isWeakGiuga_iff_prime_dvd and AgohGiuga.isWeakGiuga_iff_sum_primeFactors

Source: FormalConjectures/Wikipedia/AgohGiuga.lean:101 and :112 (both category research solved).

Proof idea: Fix a prime p ∣ n. Since p−1 = φ(p) ∣ φ(n) and φ(n) ≥ 1, Fermat gives i^φ(n) ≡ 1 (mod p) if p ∤ i and ≡ 0 if p ∣ i. So 1 + Σ_{0<i<n} i^φ(n) ≡ 1 + #{0<i<n : p ∤ i} = 1 + (n−1) − (n/p − 1) (mod p), i.e. p divides (1 + Σ) + (n/p − 1) (lemma `key`). This gives the forward direction. For the converse, the condition p ∣ n/p − 1 for all p forces n squarefree (if p² ∣ n then p ∣ n/p, so p ∣ 1), and for squarefree n, n = ∏ primeFactors divides anything that every prime factor divides (`Finset.prod_primes_dvd`). The second statement: n·(Σ 1/p − 1/n) = T − 1 with T = Σ_{p∣n} n/p, so the expression is a natural number iff n ∣ T − 1; modulo a prime p ∣ n all terms n/q with q ≠ p vanish, so p ∣ T − 1 ⟺ p ∣ n/p − 1, and the same squarefree argument closes the loop via the first theorem.

`Nat.Composite` (from FormalConjecturesForMathlib) is restated locally as an abbrev with the same body; targeted Mathlib imports.

Axioms (both theorems): [propext, Classical.choice, Quot.sound]

Date: 2026-10-30
