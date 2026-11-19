import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace BeaverMathOlympiad

/-- Invariant: 5·a n = 3·2^n + e(n mod 4) with e = (7, −6, 3, 6). -/
theorem bmo4_inv (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) (n : ℕ) :
    (n % 4 = 0 → 5 * a n = 3 * 2 ^ n + 7) ∧
    (n % 4 = 1 → 5 * a n + 6 = 3 * 2 ^ n) ∧
    (n % 4 = 2 → 5 * a n = 3 * 2 ^ n + 3) ∧
    (n % 4 = 3 → 5 * a n = 3 * 2 ^ n + 6) := by
  induction n with
  | zero => simp [a_ini]
  | succ n ih =>
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    rw [a_rec n, h2]
    generalize 2 ^ n = t at *
    obtain ⟨h0, h1, h2', h3⟩ := ih
    split_ifs with hc <;> omega

theorem beaver_math_olympiad_problem_4
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) :
    ¬ (∃ n, a n % 3 = 1) := by
  rintro ⟨n, hn⟩
  obtain ⟨h0, h1, h2, h3⟩ := bmo4_inv a a_ini a_rec n
  generalize 2 ^ n = t at *
  omega

end BeaverMathOlympiad

#print axioms BeaverMathOlympiad.beaver_math_olympiad_problem_4
