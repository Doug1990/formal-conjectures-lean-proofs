# Erdos394.erdos_394.variants.lower_bound

- Source: `FormalConjectures/ErdosProblems/394.lean:110` (category research solved)
- Statement: `(fun x ↦ x ^ 2 / Real.log x) ≪ (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ))`, where `≪` is the
  checkout's notation `IsBigO atTop (g : ℕ → ℝ) (f : ℕ → ℝ)`. The notation and the def `t` are restated
  locally, and only targeted Mathlib imports are used.

## Proof idea
For a prime p, p ∣ m(m+1) forces m ≥ p − 1, so t₂(p) ≥ p − 1. The proof takes y = ⌊n/100⌋ and counts the
primes in (y, n]. Chebyshev's lower bound π(n) ≥ n/(6 log n) comes from the central binomial coefficient
(copied from erdos888). For the upper bound on the primes ≤ y: at most √n + 1 of them are ≤ √n. The ones in
(√n, y] number B with (√n+1)^B ≤ primorial y ≤ 4^y, so B·log n ≤ 2y·log 4 ≈ 0.028 n. Then (√n + 1)·log n ≤ n/20
for n ≥ 160⁴: with r = n^{1/4}, log n = 4 log r ≤ 4r. Together these give #P·log n ≥ n/12 for the primes P in
(y, n]. Each prime in P contributes t₂(p) ≥ y ≥ n/200. So the sum is ≥ n²/(2400 log n), which gives
`IsBigO.of_bound 2400`.

## Axioms
`'Erdos394.erdos_394.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-14 (4 compiles)
