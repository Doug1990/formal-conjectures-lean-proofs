# OeisA211417.seven_mul_a_dvd_two_mul_add_one

- Source: FormalConjectures/OEIS/211417.lean:94 (category research solved)
- Statement: (2n+1) ∣ 7·a(n), where a(n) = (30n)! n! / ((15n)! (10n)! (6n)!).

Proof idea: Legendre's formula, one layer q = p^i at a time. With J = ⌊30n/q⌋, each layer contributes the Landau function Δ(J) = J + ⌊J/30⌋ − ⌊J/2⌋ − ⌊J/3⌋ − ⌊J/5⌋ ≥ 0. If q ∣ 2n+1 and q ≥ 15, then J = 30t+14 and Δ = 1. For q < 15, interval_cases shows that the only bad odd layers are q ∈ {3, 5, 7}. For p = 3 and p = 5, an injection swaps the bad layer i = 1 for the top layer L (q ≤ 30n < 6q, so Δ = 1), and L > v holds because p^(v+1) ≤ 5(2n+1) ≤ 30n. For p = 7, the factor 7 absorbs the bad layer. Integrality (D ∣ N) follows from Δ ≥ 0, and that turns 7·(N/D) into (7N)/D.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-05. Verified file: work/oeis211417_7.lean. This results file is an identical copy and was not compiled separately.
