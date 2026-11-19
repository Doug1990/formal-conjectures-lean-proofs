# erdos888_primes

- Statement: `Erdos888.erdos_888.variants.primes` (category research solved), from `FormalConjectures/ErdosProblems/888.lean:78` in the checkout.
- The `≫` notation was unfolded to its definition (`FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean:24`): `IsBigO atTop (fun n ↦ n / log n) (fun n ↦ findGreatest (p n) n)`. `RequiredCondition` and `p` are restated verbatim, with Mathlib imports only.

**Proof idea.** A = the primes in [1, n]. Take primes a ≤ b ≤ c ≤ d with abcd a square. Then a ∣ bcd, so a ∈ {b, c, d}, and the ordering forces a = b. In the same way d ∣ abc gives d = c, so ad = bc. Hence `p n (π(n))` holds. π(n) ≤ n, so `Nat.le_findGreatest` gives π(n) ≤ findGreatest. The Chebyshev lower bound 4^m ≤ (2m+1)(2m)^{π(2m+1)} comes from the central binomial coefficient (MP.cheb from erdos205_many). Take m = ⌊(n−1)/2⌋ and logs, and use log 2 > 0.693. This gives n ≤ 6·π(n)·log n for n ≥ 4, so the constant is 6.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-14
