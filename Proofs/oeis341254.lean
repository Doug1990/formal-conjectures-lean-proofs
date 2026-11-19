import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OeisA341254

open Real

noncomputable def rConst : ℝ := (2 + sqrt 5) / 2

noncomputable def rSq : ℝ := rConst * rConst

noncomputable def a (n : ℕ) : ℕ :=
  let r := rConst
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

namespace P

lemma s_facts : (0 : ℝ) ≤ √5 ∧ √5 * √5 = 5 ∧ √5 < 9 / 4 ∧ 2 < √5 := by
  have h0 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  have h1 : √5 * √5 = (5 : ℝ) := Real.mul_self_sqrt (by norm_num)
  refine ⟨h0, h1, ?_, ?_⟩ <;> nlinarith

lemma r_sq : rConst * rConst = 2 * rConst + 1 / 4 := by
  obtain ⟨_, h1, _, _⟩ := s_facts
  unfold rConst
  linear_combination (1 / 4 : ℝ) * h1

lemma irr (n : ℕ) (hn : n ≠ 0) : Irrational (rConst * n) := by
  have h5 : Irrational √((5 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt (by decide)
  have h := ((h5.natCast_add 2).div_natCast (two_ne_zero)).mul_natCast hn
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have e5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  rw [e2, e5] at h
  exact h

end P

theorem a_bounds (n : ℕ) (hn : 1 ≤ n) : (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3 := by
  obtain ⟨_, _, hs2, hs3⟩ := P.s_facts
  have hr : rConst = (2 + √5) / 2 := rfl
  have hr2 := P.r_sq
  set r := rConst with hrdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := ⌊r * n⌋ with hm
  have hm1 : (m : ℝ) ≤ r * n := Int.floor_le _
  have hm2 : r * n < m + 1 := Int.lt_floor_add_one _
  have hm3 : (m : ℝ) ≠ r * n := fun h => (P.irr n (by omega)).ne_int m h.symm
  have hx0 : 0 < r * n - m := by
    rcases lt_or_eq_of_le hm1 with h | h
    · linarith
    · exact absurd h hm3
  have hmpos : (0 : ℝ) ≤ m := by
    have : (0 : ℝ) < r * n := by
      have : (0 : ℝ) < r := by rw [hr]; linarith
      positivity
    have : (0 : ℤ) ≤ m := Int.floor_nonneg.mpr this.le
    exact_mod_cast this
  set A : ℤ := ⌊r * (m : ℝ)⌋ with hA
  have hA1 : (A : ℝ) ≤ r * m := Int.floor_le _
  have hA2 : r * m < A + 1 := Int.lt_floor_add_one _
  have hA0 : (0 : ℤ) ≤ A := Int.floor_nonneg.mpr (by
    have : (0 : ℝ) < r := by rw [hr]; linarith
    positivity)
  have ha : (a n : ℝ) = A := by
    show (((⌊r * ((⌊r * (n : ℝ)⌋ : ℤ) : ℝ)⌋).toNat : ℕ) : ℝ) = A
    rw [← hm, ← hA]
    have : ((A.toNat : ℕ) : ℤ) = A := Int.toNat_of_nonneg hA0
    exact_mod_cast this
  rw [ha]
  have hrSq : rSq = r * r := rfl
  rw [hrSq]
  set x := r * n - m with hx
  have hrm : r * m = 2 * m + n / 4 - (r - 2) * x := by
    rw [hx]; linear_combination (n : ℝ) * hr2
  have hD : (n : ℝ) * (r * r) - A = 2 * x + n / 4 - (A - 2 * m) := by
    rw [hx]; linear_combination (n : ℝ) * hr2
  have heps0 : 0 < r - 2 := by rw [hr]; linarith
  have heps1 : r - 2 < 1 / 8 := by rw [hr]; linarith
  have hx1 : x < 1 := by rw [hx]; linarith
  have hex0 : 0 < (r - 2) * x := mul_pos heps0 hx0
  have hex1 : (r - 2) * x < 1 / 8 := by nlinarith
  set t : ℤ := A - 2 * m with ht
  have htr : (t : ℝ) = A - 2 * m := by rw [ht]; push_cast; ring
  have hlow : (4 * t : ℝ) < n := by rw [htr]; linarith
  have hup : (n : ℝ) < 4 * t + 5 := by rw [htr]; linarith
  have hlow' : 4 * t + 1 ≤ (n : ℤ) := by
    have : (4 * t : ℤ) < n := by exact_mod_cast hlow
    omega
  have hup' : (n : ℤ) ≤ 4 * t + 4 := by
    have : (n : ℤ) < 4 * t + 5 := by exact_mod_cast hup
    omega
  have hlow'' : (4 * t + 1 : ℝ) ≤ n := by exact_mod_cast hlow'
  have hup'' : (n : ℝ) ≤ 4 * t + 4 := by exact_mod_cast hup'
  rw [hD, ← htr]
  constructor <;> linarith

#print axioms a_bounds

end OeisA341254
