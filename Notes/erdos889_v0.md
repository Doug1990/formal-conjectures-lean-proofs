# erdos889_v0

- Statement: `Erdos889.erdos_889.variants.v0_gt_1` (∀ n ∉ {0,1,2,3,4,7,8,16}, 1 < v₀ n)
- Source: `FormalConjectures/ErdosProblems/889.lean:61` (category research solved, ErSe67)
- Definitions `v`, `v₀` restated verbatim with targeted Mathlib imports.

Proof idea: only k ∈ {0,1,2} are needed. If n has two distinct prime factors, use k = 0. If n+1 has two, use k = 1, since its primes cannot divide n. Otherwise n and n+1 are both prime powers, so one of them is a power of 2. Odd primes dividing n+2 cannot divide n or n+1, so it suffices to find two distinct odd primes dividing n+2. Case n = 2^e: the exceptions force e ≥ 5. If e were odd, 3 | 2^e+1 = n+1 would make it a power of 3, which is impossible. So e is even, and n+2 = 2(2^m+1) with m = e−1 odd and m ≥ 5. Case n+1 = 2^b: b ≥ 4. If b were even, 3 | n would give 3^a + 1 = 2^b (impossible mod 8), so b is odd and n+2 = 2^b+1. In both cases 3 | 2^m+1 with m odd and m ≥ 4. If 2^m+1 were a prime power, then 3^a = 2^m+1. That forces m ≤ 3: mod 8, a is even, and (3^{a/2}+1) | 2^m must be 2 or 4. So 2^m+1 has two distinct (odd) prime factors.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-14
