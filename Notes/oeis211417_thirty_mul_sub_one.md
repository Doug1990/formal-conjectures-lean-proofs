# OeisA211417.thirty_mul_sub_one_dvd_a

- Source: `FormalConjectures/OEIS/211417.lean:84` (category research solved)
- Statement: `(30 * (n : ℤ) - 1) ∣ (a n : ℤ)` with a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)

Proof idea: for n ≥ 1, show (30n−1)·(15n)!(10n)!(6n)! ∣ (30n)! n! by comparing p-adic valuations
(`Nat.factorization_prime_le_iff_dvd` + Legendre's formula `padicValNat_factorial`). Each Legendre
term depends only on J = ⌊30n/q⌋ (q = p^i), since ⌊cn/q⌋ = ⌊J/(30/c)⌋. The Landau function
J + ⌊J/30⌋ − ⌊J/2⌋ − ⌊J/3⌋ − ⌊J/5⌋ is ≥ 0, and it is ≥ 1 when J is coprime to 30 (omega). If
q ∣ 30n−1, then 30n = qJ + 1, so J is coprime to 30. The levels i = 1..v_p(30n−1) each contribute
an extra 1, which covers v_p(30n−1). Then a(n) = N/D gives the divisibility, and n = 0 is trivial
(−1 divides everything).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-05. Verified file: work/oeis211417_30n.lean (results copy written with identical text).
Reusable: T.div_eq, T.key, T.key1 (Landau step-function bounds), T.sum_bound (Legendre sum comparison).
