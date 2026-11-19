# RamanujanTau.multipliable

- Source: `FormalConjectures/Wikipedia/RamanujanTau.lean:46` (category API)
- Statement: `Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ)` (Pi topology on power series).

Proof idea: write each factor as `1 + f n` with `f n = (1 - X^n)^24 - 1`. Since `(1 - X^n) - 1 = -X^n` divides
`(1 - X^n)^24 - 1^24` (`sub_dvd_pow_sub_pow`), `X^n ∣ f n`, so `order (f n) ≥ n → ⊤`. Mathlib's
`multipliable_one_add_of_tendsto_order_atTop_nhds_top` (index type ℕ+, a locally finite order with bottom) then gives
multipliability.

Axioms: `'RamanujanTau.multipliable' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-02. 2 compiles (1st: the ring `R` had to be given explicitly as `(R := ℤ)`).
