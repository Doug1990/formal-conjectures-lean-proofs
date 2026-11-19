# erdos205_many

- Statement: `Erdos205.erdos_205.variants.many_prime_factors`
- Source: `FormalConjectures/ErdosProblems/205.lean:96` (category research solved, Tao–Alexeev quantification of Barreto–Leeham)
- Date: 2026-11-14

## Proof idea
Let r = 2^j with j ≥ 3. A Chebyshev-type bound comes from the central binomial coefficient: 4^m ≤ (2m+1)·(2m)^{π(2m)}. With m = r², this gives more than r primes up to 2r²+1, so the odd primes q_0 < … < q_{r−1} (nth primes 1..r) are all ≤ 2r² = 2^{2j+1}. CRT gives n ≡ 2^i mod q_i^r for i < r and n ≡ 2^r mod 2^{r+1}, with 2^r < n < 2^{(2j+1)r² + r + 2}. For every k with 2^k ≤ n, n − 2^k ≠ 0 is divisible by q_k^r (if k < r) or by 2^r (if k ≥ r), so Ω(n − 2^k) ≥ r. Then log n ≤ (2j+2)r² and log log n ≥ j/4, which gives log n / log log n ≤ 16r². So (1/4)·√(log n / log log n) ≤ r ≤ Ω(n − 2^k). Since j can be arbitrarily large, the set is unbounded.

## Axioms
`'Erdos205.erdos_205.variants.many_prime_factors' depends on axioms: [propext, Classical.choice, Quot.sound]`
