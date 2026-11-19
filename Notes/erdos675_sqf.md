# erdos675_sqf

- Statement: `Erdos675.erdos_675.variants.squarefree` (the squarefree numbers have the translation property), `FormalConjectures/ErdosProblems/675.lean:135`, category research solved.
- The definitions `IsTranslation` and `HasTranslationProperty` are restated verbatim, with targeted Mathlib imports instead of `FormalConjecturesUtil`.

Proof idea: fix n and set M = (n!)². The shift is t = M(s+1) with 0 ≤ s < X. For a ≤ n, a square x² ∣ a with x ≥ 2 has x ≤ n, so x² ∣ M ∣ t. This means non-squarefree stays non-squarefree, and primes p ≤ n cannot create a square factor in a + t. Only primes p > n with p² ≤ n + MX remain (so p ≤ R = √(n+MX)). These p are coprime to M, so for each pair (a, p) at most X/p² + 1 values of s are bad. Summing, and using Σ_{m>n} 1/m² ≤ 2/(2n+1) (a telescoping bound), gives #bad ≤ n(2X/(2n+1) + R). This is < X because X = Y²(n+M)+1 with Y = n(2n+1) forces Y·R < X. So some s is good. It is an elementary counting sieve, derived without the literature.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-16
