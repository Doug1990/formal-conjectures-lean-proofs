# AgohGiuga.agoh_giuga.variants.isStrongGiuga_implies_isCarmichael and AgohGiuga.isStrongGiuga_iff

Source: FormalConjectures/Wikipedia/AgohGiuga.lean:214 and :206 (both category research solved).

Proof idea: For a prime p ∣ n with n = p·c, the map i ↦ i^(n−1) mod p is p-periodic and vanishes at 0, so 1 + Σ_{0<i<n} i^(n−1) ≡ 1 + c·Σ_{x∈ZMod p} x^(n−1) ≡ 1 − c·[p−1 ∣ n−1] (mod p), using `FiniteField.sum_pow_units` (lemma `strong_mod`). Hence a strong Giuga number satisfies p−1 ∣ n−1 and p ∣ n/p − 1 for every prime factor p. The second condition forces n squarefree; with the first, Fermat's little theorem at every prime factor gives n ∣ b^(n−1) − 1 for b coprime to n, so n is Carmichael. For the iff, the condition ∃ m, Σ1/p − 1/n = m is shown equivalent to "p ∣ n/p − 1 for all p ∣ n" (multiply by n, reduce mod each p). For the converse, Carmichael ⇒ p−1 ∣ n−1 (Korselt, one direction) by CRT: pick b ≡ g (mod p), with g a generator of (ZMod p)ˣ, and b ≡ 1 (mod n/p); then g^(n−1) = 1, so p−1 = ord(g) ∣ n−1. Then `strong_mod` gives 1 − c ≡ 0 mod p for each p, and squarefreeness finishes.

`Nat.Composite` and `IsCarmichael` (from FormalConjecturesForMathlib) are restated locally with the same bodies; targeted Mathlib imports.

Axioms (both theorems): [propext, Classical.choice, Quot.sound]

Date: 2026-10-30
