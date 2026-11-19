# BeckFiala.beck_fiala_theorem

- Source: `FormalConjectures/Wikipedia/BeckFialaConjecture.lean:72` (category research solved, Beck–Fiala 1981)
- Date: 2026-11-03
- Compiles: 2 (1st: `Fl` needed `noncomputable`, one `simp` needed `simpa` for `(0 : Fin n → ℝ) j`; 2nd: clean + axioms)

## Proof idea
This is the classical floating-colouring argument. A coordinate of a point x in [-1,1]^n is
*floating* if |x_j| < 1, and a set is *active* if it contains more than t floating
coordinates. Double counting with the degree bound gives #active·(t+1) ≤ t·#floating, so
while some coordinate floats, there are fewer active sets than floating coordinates. A dimension
count (`LinearMap.ker_ne_bot_of_finrank_lt`) then gives a nonzero vector v that is supported on
the floating coordinates and has zero sum on every active set. Moving along v until the first
coordinate reaches ±1 fixes at least one more coordinate. Strong induction on the number of
floating coordinates proves this: for every x in the cube there is a ±1 vector χ that agrees with x
on the fixed coordinates and has |Σ_{S_i}(χ − x)| < 2t for every i. Active sets keep their sum
during the move. For inactive sets, the error is < 2 per floating coordinate, and there are at most t of
them. Starting from x = 0, the sum Σ_{S_i} χ is an integer of absolute value < 2t, so it is at most 2t − 1.
The proof uses targeted Mathlib imports, and the file is self-contained.

Reusable helpers: `BF.kernel`, `BF.move`, `BF.count`, `BF.bound`, `BF.main`.

## Axioms
`'BeckFiala.beck_fiala_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`
