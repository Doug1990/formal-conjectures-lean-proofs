import Mathlib.Data.Nat.Fib.Basic

namespace OeisA103311

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n

namespace Fb

theorem ra (n : ℕ) : a (n + 4) = 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n := rfl

/-- Fibonacci numbers in ℤ. -/
def F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

theorem hF (n : ℕ) : F (n + 2) = F n + F (n + 1) := by
  unfold F
  rw [Nat.fib_add_two, Nat.cast_add]

/-- One block of five: a(5k+j) is (up to sign) F(5k), F(5k+1), F(5k+1), 0, -F(5k+3). -/
theorem block (n : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (h0 : a n = s * F n) (h1 : a (n + 1) = s * F (n + 1)) (h2 : a (n + 2) = s * F (n + 1))
    (h3 : a (n + 3) = 0) (h4 : a (n + 4) = -s * F (n + 3)) :
    a (n + 5) = -s * F (n + 5) ∧ a (n + 6) = -s * F (n + 6) ∧ a (n + 7) = -s * F (n + 6) ∧
      a (n + 8) = 0 ∧ a (n + 9) = s * F (n + 8) := by
  have r5 := ra (n + 1)
  have r6 := ra (n + 2)
  have r7 := ra (n + 3)
  have r8 := ra (n + 4)
  have r9 := ra (n + 5)
  have f2 := hF n
  have f3 := hF (n + 1)
  have f4 := hF (n + 2)
  have f5 := hF (n + 3)
  have f6 := hF (n + 4)
  have f7 := hF (n + 5)
  have f8 := hF (n + 6)
  simp only [Nat.add_assoc, Nat.reduceAdd] at r5 r6 r7 r8 r9 f2 f3 f4 f5 f6 f7 f8 h1 h2 h3 h4 ⊢
  rcases hs with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem main (k : ℕ) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    a (5 * k) = s * F (5 * k) ∧ a (5 * k + 1) = s * F (5 * k + 1) ∧
    a (5 * k + 2) = s * F (5 * k + 1) ∧ a (5 * k + 3) = 0 ∧
    a (5 * k + 4) = -s * F (5 * k + 3) := by
  induction k with
  | zero => exact ⟨1, Or.inl rfl, by decide, by decide, by decide, by decide, by decide⟩
  | succ k ih =>
    obtain ⟨s, hs, h0, h1, h2, h3, h4⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4⟩ := block (5 * k) s hs h0 h1 h2 h3 h4
    refine ⟨-s, ?_, ?_⟩
    · rcases hs with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (by decide)
    rw [show 5 * (k + 1) = 5 * k + 5 by omega]
    simp only [Nat.add_assoc, Nat.reduceAdd, neg_neg]
    exact ⟨g0, g1, g2, g3, g4⟩

theorem abs_eq (s : ℤ) (hs : s = 1 ∨ s = -1) (m : ℕ) : Int.natAbs (s * F m) = Nat.fib m := by
  rcases hs with rfl | rfl <;> simp [F]

end Fb

open Fb in
theorem a_abs_eq_fib (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  obtain ⟨s, hs, h0, h1, h2, h3, h4⟩ := main (n / 5)
  have hn : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  generalize hq : n / 5 = q at h0 h1 h2 h3 h4 hn
  rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4)
    with h | h | h | h | h
  · refine ⟨5 * q, ?_⟩
    rw [show n = 5 * q by omega, h0]
    exact abs_eq s hs _
  · refine ⟨5 * q + 1, ?_⟩
    rw [show n = 5 * q + 1 by omega, h1]
    exact abs_eq s hs _
  · refine ⟨5 * q + 1, ?_⟩
    rw [show n = 5 * q + 2 by omega, h2]
    exact abs_eq s hs _
  · refine ⟨0, ?_⟩
    rw [show n = 5 * q + 3 by omega, h3]
    rfl
  · refine ⟨5 * q + 3, ?_⟩
    rw [show n = 5 * q + 4 by omega, h4]
    exact abs_eq (-s) (by rcases hs with rfl | rfl <;> simp) _

end OeisA103311

#print axioms OeisA103311.a_abs_eq_fib
