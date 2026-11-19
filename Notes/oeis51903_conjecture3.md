# OeisA51903.conjecture3

- Source: FormalConjectures/OEIS/51903.lean:99 (category research solved)
- Statement: ∃ n, Odd n ∧ 1 < a n ∧ 2^n ≡ 2^(a n) [MOD n], where a n = max exponent in the factorisation of n.

Proof idea: witness n = 7·631·881·3511²·201961 = 9687963167864344937 (from the source docstring). The five factors are proved prime with `norm_num`. `Nat.primeFactorsList_unique` gives a permutation, and `List.Perm.eq_of_sortedLE` with sortedness pins down primeFactorsList n exactly, so a n = 2 by `decide`. For 2^n ≡ 4 (mod n), a fuel-based square-and-multiply function `pm` (pm (k+1) e = pm k (e/2)^2 · b^(e%2) mod m) is proved equal to b^e % m for e < 2^k. The instance with k = 64 is then evaluated by `decide +kernel`, which uses GMP-accelerated kernel Nat arithmetic and no native code.

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-06 (2 compiles)
