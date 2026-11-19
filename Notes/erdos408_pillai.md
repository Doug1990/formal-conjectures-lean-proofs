# Erdos408.erdos_408.variants.pillai

- Source: `FormalConjectures/ErdosProblems/408.lean:148` (category research solved, Pillai 1929)
- Statement: for n ≥ 2, ⌊(log n − log 2)/log 3⌋₊ + 1 ≤ f n ≤ ⌊log n / log 2⌋₊ + 1, where f n = least k ≥ 1 with φ^[k] n = 1.
- Verified file: `work/erdos408_pillai.lean` (this is a hand copy); `f` is restated locally, targeted imports.

**Proof idea.** Upper bound: φ(2m) ≤ m (strong induction, using φ(2·2j) = 2φ(2j) and φ(2m) = φ(m) for odd m), and φ(n) is even for n > 2. Strong induction gives k ≥ 1 with φ^[k] n = 1, 2^(k−1) ≤ n, and 2^k ≤ n when n is even. Lower bound: a completely additive weight D with D(2) = 1 and D(p) = D(p−1) for odd primes. It is defined by well-founded recursion over `primeFactors.attach`. Using φ(n) = ∏ p^(k−1)(p−1), we get D(n) ≤ D(φ n) + [2 ∣ n]. So φ^[k] n = 1 forces D(n) ≤ k, and D(n) + 1 ≤ k for odd n ≥ 3. Strong induction over minFac gives n ≤ 3^D(n), and 3n ≤ 2·3^D(n) for even n. Together these give n ≤ 2·3^(f n − 1), and taking logs finishes both floors.

Axioms: `'Erdos408.erdos_408.variants.pillai' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-11
