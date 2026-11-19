# TanArctanSum: x_eq_tan_sum_arctan and kernel_dvd_of_eq_intCast

- Statements: `Arxiv.«2607.05739».x_eq_tan_sum_arctan` (category textbook, line 80) and
  `Arxiv.«2607.05739».kernel_dvd_of_eq_intCast` (category research solved, line 105)
- Source: `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean`
- Proof file: `results/tan_arctan.lean`. Definitions restated locally; imports are targeted Mathlib modules instead of FormalConjecturesUtil.

**Proof idea.** For `x_eq_tan_sum_arctan`: write θ_n = Σ_{k≤n} arctan k and r_n = ∏_{k≤n} √(1+k²) > 0.
Induction with Z_{n+1} = Z_n·(1+i(n+1)), the angle-addition formulas and cos(arctan t) = 1/√(1+t²),
sin(arctan t) = t/√(1+t²) gives A_n = r_n cos θ_n and B_n = r_n sin θ_n. Then B_n/A_n = sin θ_n / cos θ_n = tan θ_n.
This also holds when A_n = 0, because Lean's division by zero gives 0 on both sides.
For `kernel_dvd_of_eq_intCast`: x_n = m with A_n ≠ 0 gives B_n = m·A_n, so ω_n = |A_n|²·(1+m²). A prime
with odd exponent in ω_n therefore has a positive exponent in 1+m². The kernel is a product of distinct primes
dividing 1+m² (`Finset.prod_primes_dvd`), so K_n ∣ 1+m². Then K_n ≤ 1+m², and √(K_n−1) ≤ √(m²) = |m|.

Axioms (both): `[propext, Classical.choice, Quot.sound]`

The only compiler messages are unused-variable warnings for the hypothesis `hn`, which is part of the original statements.

Date: 2026-10-30
