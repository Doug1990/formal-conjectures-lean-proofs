# OeisA211417.a_dvd_five_mul_add_one

- Source: `FormalConjectures/OEIS/211417.lean:116` (category research solved)
- Statement: `(5 * (n : ℤ) + 1) ∣ (a n : ℤ)`, where a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)
- Verified file: `work/oeis211417_5n1.lean`. `results/oeis211417_five_mul_add_one.lean` is the same text.

Proof idea: the same Legendre-layer method as `a_dvd_three_mul_add_one`. For q ∣ 5n+1 and q ≥ 6,
J = ⌊30n/q⌋ = 6k − 1 ≡ 5 mod 6, so Δ(J) = 1. The only layers that fail are q ∈ {2, 3, 4}.
They are replaced by the top layers. For p = 3 that is the layer L = log₃(30n), which lies above
v₃(5n+1). For p = 2 it is L and L−1, both above v₂(5n+1) because 4(5n+1) ≤ 30n. On those top
layers q ≤ 30n < 6q, so J ∈ [1, 5] and Δ = 1. The counting step uses an injection of {1..v} into
the good layers.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-05
