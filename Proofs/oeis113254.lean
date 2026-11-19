import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.Even

namespace OeisA113254

open Nat Int

def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

def u : ℕ → ℤ
| 0 => 2
| 1 => 56
| n + 2 => -4 * u (n + 1) - 64 * u n

theorem a6 (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  have r0 : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl
  have r1 : a (n + 5) = -4 * a (n + 4) + 256 * a (n + 2) + 4096 * a (n + 1) := rfl
  have r2 : a (n + 6) = -4 * a (n + 5) + 256 * a (n + 3) + 4096 * a (n + 2) := rfl
  linear_combination r2 - 4 * r1 + 64 * r0

theorem w_rec (n : ℕ) :
    u (n + 3) ^ 2 = -48 * u (n + 2) ^ 2 + 3072 * u (n + 1) ^ 2 + 262144 * u n ^ 2 := by
  have h2 : u (n + 2) = -4 * u (n + 1) - 64 * u n := rfl
  have h3 : u (n + 3) = -4 * u (n + 2) - 64 * u (n + 1) := rfl
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
    have h : a (2 * n + 7) = -48 * a (2 * n + 5) + 3072 * a (2 * n + 3) + 262144 * a (2 * n + 1) :=
      a6 (2 * n + 1)
    rw [h, h0, h1, h2, w_rec]

theorem a_odd_is_square : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨u n, by rw [(main n).1, sq]⟩

end OeisA113254

#print axioms OeisA113254.a_odd_is_square
