# OeisA211417.a_dvd_three_mul_add_one

- Source: `FormalConjectures/OEIS/211417.lean:105` (category research solved)
- Statement: `(3 * (n : ℤ) + 1) ∣ (a n : ℤ)`, where a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)
- Verified file: `work/oeis211417_3n1.lean`. `results/oeis211417_three_mul_add_one.lean` is the same text.

Proof idea: compare Legendre valuations prime by prime. Every layer q = p^i contributes
Δ(J) = J + ⌊J/30⌋ − ⌊J/2⌋ − ⌊J/3⌋ − ⌊J/5⌋ ≥ 0 with J = ⌊30n/q⌋. If q ∣ 3n+1 and q ≥ 10, then
J = 10k − 1, so J ≡ 9 mod 10 and Δ = 1. For q < 10 a case check shows Δ = 1 except at q ∈ {2, 5, 8}.
Those missing layers are replaced by the top layers: q = p^L with q ≤ 30n < 6q always gives Δ = 1.
For p = 5 the layer L is above v_5(3n+1); for p = 2 both L and L−1 are. An injection of
{1..v} into the "good" layers (`Finset.card_le_card_of_injOn`) then gives v_p(3n+1) ≤ Σ Δ.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-05
