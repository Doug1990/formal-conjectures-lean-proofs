import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Even

namespace OeisA113250

def a : ℕ → ℤ
| 0 => -1
| 1 => 4
| 2 => 32
| 3 => 64
| n + 4 => -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n

def f : ℕ → ℤ
| 0 => -1
| 1 => 1
| 2 => 2
| 3 => 1
| 4 => -1
| _ => 4

def e (n : ℕ) : ℤ := f (n % 6)

theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n := rfl

theorem e_rec (n : ℕ) : e (n + 4) = -e (n + 3) + e (n + 1) + e n := by
  unfold e
  have h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h
  · rw [show (n + 4) % 6 = 4 by omega, show (n + 3) % 6 = 3 by omega,
      show (n + 1) % 6 = 1 by omega, h]; rfl
  · rw [show (n + 4) % 6 = 5 by omega, show (n + 3) % 6 = 4 by omega,
      show (n + 1) % 6 = 2 by omega, h]; rfl
  · rw [show (n + 4) % 6 = 0 by omega, show (n + 3) % 6 = 5 by omega,
      show (n + 1) % 6 = 3 by omega, h]; rfl
  · rw [show (n + 4) % 6 = 1 by omega, show (n + 3) % 6 = 0 by omega,
      show (n + 1) % 6 = 4 by omega, h]; rfl
  · rw [show (n + 4) % 6 = 2 by omega, show (n + 3) % 6 = 1 by omega,
      show (n + 1) % 6 = 5 by omega, h]; rfl
  · rw [show (n + 4) % 6 = 3 by omega, show (n + 3) % 6 = 2 by omega,
      show (n + 1) % 6 = 0 by omega, h]; rfl

theorem closed (n : ℕ) :
    a n = 2 ^ (2 * n) * e n ∧ a (n + 1) = 2 ^ (2 * (n + 1)) * e (n + 1) ∧
    a (n + 2) = 2 ^ (2 * (n + 2)) * e (n + 2) ∧ a (n + 3) = 2 ^ (2 * (n + 3)) * e (n + 3) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨h1, h2, h3, ?_⟩
    show a (n + 4) = 2 ^ (2 * (n + 4)) * e (n + 4)
    rw [a_rec, h0, h1, h3, e_rec]
    ring

theorem conjecture : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [(closed (2 * n + 1)).1]
  unfold e
  have h : (2 * n + 1) % 6 = 1 ∨ (2 * n + 1) % 6 = 3 ∨ (2 * n + 1) % 6 = 5 := by omega
  rcases h with h | h | h
  · refine ⟨2 ^ (2 * n + 1), ?_⟩
    rw [h, show f 1 = 1 from rfl]
    ring
  · refine ⟨2 ^ (2 * n + 1), ?_⟩
    rw [h, show f 3 = 1 from rfl]
    ring
  · refine ⟨2 ^ (2 * n + 2), ?_⟩
    rw [h, show f 5 = 4 from rfl]
    ring

end OeisA113250

#print axioms OeisA113250.conjecture
