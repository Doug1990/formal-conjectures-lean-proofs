# Erdos1052.even_of_isUnitaryPerfect

- Source: `FormalConjectures/ErdosProblems/1052.lean:52` (category research solved). Statement: every unitary perfect number is even.
- Proof idea: let S(n) be the sum of all unitary divisors (d ∣ n with gcd(d, n/d) = 1), so S(n) = (sum of the proper ones) + n = 2n for a unitary perfect n. S is multiplicative on coprime arguments (`S_mul`). The bijection U(a) × U(b) → U(ab), (x, y) ↦ xy, has inverse f ↦ (gcd f a, gcd f b). For a prime power, S(p^a) = 1 + p^a (`S_pp`). Suppose n is odd. Then n ≠ 1 (the sum for n = 1 is 0), so n = p^a·m with p = minFac n and m coprime to p^a. If m = 1, then 1 + p^a = 2p^a, which is impossible. Otherwise split m = r^b·k the same way. Both 1 + p^a and 1 + r^b are even (odd prime powers), so 4 ∣ S(n) = 2n, and n is even, a contradiction.
- Axioms: `'Erdos1052.even_of_isUnitaryPerfect' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-08. 2 compiles (the first had only unused-simp-argument lint warnings; the second was clean + axioms).
