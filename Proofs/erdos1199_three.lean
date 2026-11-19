import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Pointwise

namespace Erdos1199

/-- For `0 ≤ x`, `4x < y`, the floors of `(3/2) log₂ (y+y)` and `(3/2) log₂ (x+y)` differ
by 1 or 2. -/
lemma key (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (h4 : 4 * x < y) :
    1 ≤ ⌊(3 / 2 : ℝ) * Real.logb 2 (y + y)⌋ - ⌊(3 / 2 : ℝ) * Real.logb 2 (x + y)⌋ ∧
    ⌊(3 / 2 : ℝ) * Real.logb 2 (y + y)⌋ - ⌊(3 / 2 : ℝ) * Real.logb 2 (x + y)⌋ ≤ 2 := by
  have hL2 : Real.logb 2 (y + y) = 1 + Real.logb 2 y := by
    rw [← two_mul, Real.logb_mul (by norm_num) hy.ne', Real.logb_self_eq_one (by norm_num)]
  have hge : Real.logb 2 y ≤ Real.logb 2 (x + y) :=
    Real.logb_le_logb_of_le (by norm_num) hy (by linarith)
  have hlt : 3 * Real.logb 2 (x + y) < 3 * Real.logb 2 y + 1 := by
    have e1 : Real.logb 2 ((x + y) ^ 3) = 3 * Real.logb 2 (x + y) := by
      rw [Real.logb_pow]; push_cast; ring
    have e2 : Real.logb 2 (2 * y ^ 3) = 3 * Real.logb 2 y + 1 := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
        Real.logb_pow]
      push_cast; ring
    have h1 : x + y < 5 / 4 * y := by linarith
    have h2 : (x + y) ^ 3 < (5 / 4 * y) ^ 3 :=
      pow_lt_pow_left₀ h1 (by linarith) (by norm_num)
    have hy3 : 0 < y ^ 3 := by positivity
    have h3 : (x + y) ^ 3 < 2 * y ^ 3 := by nlinarith
    have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h3
    linarith
  set t1 := (3 / 2 : ℝ) * Real.logb 2 (x + y) with ht1
  set t2 := (3 / 2 : ℝ) * Real.logb 2 (y + y) with ht2
  have a1 := Int.floor_le t1
  have a2 := Int.lt_floor_add_one t1
  have b1 := Int.floor_le t2
  have b2 := Int.lt_floor_add_one t2
  have c1 : (⌊t1⌋ : ℝ) < ⌊t2⌋ := by linarith
  have c2 : (⌊t2⌋ : ℝ) < ⌊t1⌋ + 3 := by linarith
  have i1 : ⌊t1⌋ < ⌊t2⌋ := by exact_mod_cast c1
  have i2 : ⌊t2⌋ < ⌊t1⌋ + 3 := by exact_mod_cast c2
  omega

/--
Hindman [Hi79] has shown that this is false for 3-colourings.
-/
theorem erdos_1199.variants.three :
    ∃ (color : ℕ → Fin 3), ∀ (A : Set ℕ),
    A.Infinite → ∃ n ∈ (A+A), ∃ m ∈ (A+A), color n ≠ color m := by
  refine ⟨fun n => ((⌊(3 / 2 : ℝ) * Real.logb 2 (n : ℝ)⌋ : ℤ) : ZMod 3), ?_⟩
  intro A hA
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb, hab⟩ := hA.exists_gt (4 * a)
  refine ⟨a + b, Set.add_mem_add ha hb, b + b, Set.add_mem_add hb hb, ?_⟩
  intro h
  have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have h4 : 4 * (a : ℝ) < b := by exact_mod_cast hab
  obtain ⟨k1, k2⟩ := key (a : ℝ) (b : ℝ) (by positivity) hb0 h4
  push_cast at h'
  obtain ⟨c, hc⟩ := h'
  omega

end Erdos1199

#print axioms Erdos1199.erdos_1199.variants.three
