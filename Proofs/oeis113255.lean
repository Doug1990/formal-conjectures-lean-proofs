import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.Even

namespace OeisA113255

def a : ℕ → ℤ
| 0 => -1
| 1 => 4
| 2 => 227
| 3 => 5329
| n + 4 => -4 * a (n + 3) + 324 * a (n + 1) + 6561 * a n

def u : ℕ → ℤ
| 0 => 2
| 1 => 73
| n + 2 => -4 * u (n + 1) - 81 * u n

theorem a6 (n : ℕ) :
    a (n + 6) = -65 * a (n + 4) + 5265 * a (n + 2) + 531441 * a n := by
  have r0 : a (n + 4) = -4 * a (n + 3) + 324 * a (n + 1) + 6561 * a n := rfl
  have r1 : a (n + 5) = -4 * a (n + 4) + 324 * a (n + 2) + 6561 * a (n + 1) := rfl
  have r2 : a (n + 6) = -4 * a (n + 5) + 324 * a (n + 3) + 6561 * a (n + 2) := rfl
  linear_combination r2 - 4 * r1 + 81 * r0

theorem w_rec (n : ℕ) :
    u (n + 3) ^ 2 = -65 * u (n + 2) ^ 2 + 5265 * u (n + 1) ^ 2 + 531441 * u n ^ 2 := by
  have h2 : u (n + 2) = -4 * u (n + 1) - 81 * u n := rfl
  have h3 : u (n + 3) = -4 * u (n + 2) - 81 * u (n + 1) := rfl
  rw [h3, h2]
  ring

theorem main (n : ℕ) :
    a (2 * n + 1) = u n ^ 2 ∧ a (2 * n + 3) = u (n + 1) ^ 2 ∧ a (2 * n + 5) = u (n + 2) ^ 2 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show a (2 * n + 7) = u (n + 3) ^ 2
    have h : a (2 * n + 7) = -65 * a (2 * n + 5) + 5265 * a (2 * n + 3) + 531441 * a (2 * n + 1) :=
      a6 (2 * n + 1)
    rw [h, h0, h1, h2, w_rec]

theorem conjecture : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨u n, by rw [(main n).1, sq]⟩

end OeisA113255

#print axioms OeisA113255.conjecture
