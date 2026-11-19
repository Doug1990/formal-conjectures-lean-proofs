import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Bugeaud61

noncomputable def routeAExponent (α ρ : ℝ) : ℝ :=
  Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹

lemma key_iff {L x y : ℝ} (hL : 0 < L) (hx : 0 < x) (hy : 0 < y) :
    L / x + L / y < 1 ↔ 1 < (x / L - 1) * (y / L - 1) := by
  have e1 : L / x + L / y = (L * y + x * L) / (x * y) := by
    field_simp
  have e2 : (x / L - 1) * (y / L - 1) - 1 = (x * y - (L * y + x * L)) / L ^ 2 := by
    field_simp
    ring
  have e3 : 1 < (x / L - 1) * (y / L - 1) ↔ 0 < (x / L - 1) * (y / L - 1) - 1 := sub_pos.symm
  rw [e1, div_lt_one (mul_pos hx hy), e3, e2, div_pos_iff_of_pos_right (by positivity)]
  constructor <;> intro h <;> linarith

theorem problem_10_61.variants.covering_criterion_range {a b : ℤ} {α : ℝ}
    (hroot : α ^ 2 = a * α + b) (hα : 1 < α) (hconj : |(a : ℝ) - α| < 1) (hb : b ≠ 0) :
    routeAExponent α |(a : ℝ) - α| < 1 ↔
      1 < (Real.logb 2 α - 1) * (Real.logb 2 α - Real.logb 2 |(b : ℝ)| - 1) := by
  have hα0 : 0 < α := by linarith
  have hb0 : 0 < |(b : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hb)
  have hprod : ((a : ℝ) - α) * α = -b := by linear_combination (-1 : ℝ) * hroot
  have hρ : |(a : ℝ) - α| = |(b : ℝ)| / α := by
    rw [eq_div_iff hα0.ne', show |(b : ℝ)| = |((a : ℝ) - α) * α| by rw [hprod, abs_neg],
      abs_mul, abs_of_pos hα0]
  have hρpos : 0 < |(a : ℝ) - α| := by rw [hρ]; exact div_pos hb0 hα0
  have hlog : Real.log |(a : ℝ) - α|⁻¹ = Real.log α - Real.log |(b : ℝ)| := by
    rw [hρ, inv_div, Real.log_div hα0.ne' hb0.ne']
  have hy : 0 < Real.log α - Real.log |(b : ℝ)| := by
    rw [← hlog]
    exact Real.log_pos ((one_lt_inv₀ hρpos).2 hconj)
  have hx : 0 < Real.log α := Real.log_pos hα
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : Real.logb 2 α - Real.logb 2 |(b : ℝ)| =
      (Real.log α - Real.log |(b : ℝ)|) / Real.log 2 := by
    unfold Real.logb
    ring
  rw [routeAExponent, hlog, hsub]
  unfold Real.logb
  exact key_iff hL hx hy

end Bugeaud61

#print axioms Bugeaud61.problem_10_61.variants.covering_criterion_range
