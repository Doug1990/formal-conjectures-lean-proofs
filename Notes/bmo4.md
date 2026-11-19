# BeaverMathOlympiad.beaver_math_olympiad_problem_4

Source: FormalConjectures/Other/BeaverMathOlympiad.lean:174 (category research solved).

Proof idea: write 5·a(n) = 3·2^n + e(n). The recurrence becomes autonomous in e
(e ↦ e/3 + 5 if e ≡ 0 mod 3, e ↦ (e − 25)/3 if e ≡ 1 mod 3), and a(n) mod 3 is determined by
e(n) mod 3. Starting from e(0) = 7, e cycles with period 4 through 7, −6, 3, 6, so a(n) mod 3 is
always 2, 0, 0, 0 and never 1. The Lean proof shows the four-case invariant by induction on n
(treating 2^n as an opaque atom t, then `split_ifs <;> omega`), and the theorem follows by omega.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-09 (2 compiles)
