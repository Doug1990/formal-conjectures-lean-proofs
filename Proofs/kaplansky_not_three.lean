import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

open Finset QuadraticMap

namespace QuadraticForm

variable (F : Type*) [Field F]

/-- Restated from FormalConjecturesForMathlib/LinearAlgebra/QuadraticForm/UInvariant.lean. -/
def anisotropicDims : Set ℕ :=
  {n | ∃ Q : QuadraticForm F (Fin n → F), Q.Anisotropic ∧ Q.Nondegenerate}

end QuadraticForm

namespace KaplanskyUInvariant

open QuadraticForm

def IsUInvariant (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)), IsGreatest (anisotropicDims F) n

theorem aniso_nondeg {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [NeZero (2 : F)]
    {Q : QuadraticForm F M} (hQ : Q.Anisotropic) : Q.Nondegenerate := by
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  exact QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
    ((Submodule.eq_bot_iff _).mpr fun m hm ↦ hQ m (QuadraticMap.mem_radical_iff'.mp hm).1)

/-- If `⟨1, a, b⟩` is anisotropic, so is `⟨1, a, b, ab⟩`. -/
theorem key {F : Type*} [Field F] (a b : F)
    (H : ∀ x y z : F, x ^ 2 + a * y ^ 2 + b * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (x y z t : F) (h : x ^ 2 + a * y ^ 2 + b * z ^ 2 + a * b * t ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0 := by
  by_cases hc : z ^ 2 + a * t ^ 2 = 0
  · obtain ⟨hz, ht, -⟩ := H z t 0 (by linear_combination hc)
    subst hz; subst ht
    obtain ⟨hx, hy, -⟩ := H x y 0 (by linear_combination h)
    exact ⟨hx, hy, rfl, rfl⟩
  · exfalso
    exact hc (H (x * z - a * y * t) (x * t + y * z) (z ^ 2 + a * t ^ 2)
      (by linear_combination (z ^ 2 + a * t ^ 2) * h)).2.2

theorem four_aniso {F : Type*} [Field F] (a b : F)
    (H : ∀ x y z : F, x ^ 2 + a * y ^ 2 + b * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0) :
    (weightedSumSquares F ![1, a, b, a * b] : QuadraticForm F (Fin 4 → F)).Anisotropic := by
  intro v hv
  have e : weightedSumSquares F ![1, a, b, a * b] v
      = 1 * (v 0 * v 0) + a * (v 1 * v 1) + b * (v 2 * v 2) + a * b * (v 3 * v 3) := by
    rw [weightedSumSquares_apply, Fin.sum_univ_four]; rfl
  rw [e] at hv
  obtain ⟨h0, h1, h2, h3⟩ := key a b H (v 0) (v 1) (v 2) (v 3) (by linear_combination hv)
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3]

theorem three_of_w {F : Type*} [Field F] (w : Fin 3 → F)
    (hw : (weightedSumSquares F w : QuadraticForm F (Fin 3 → F)).Anisotropic) :
    ∀ x y z : F, w 0 * x ^ 2 + w 1 * y ^ 2 + w 2 * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  have e : weightedSumSquares F w ![x, y, z] = w 0 * (x * x) + w 1 * (y * y) + w 2 * (z * z) := by
    rw [weightedSumSquares_apply, Fin.sum_univ_three]; rfl
  have := hw ![x, y, z] (by rw [e]; linear_combination h)
  exact ⟨by simpa using congrFun this 0, by simpa using congrFun this 1,
    by simpa using congrFun this 2⟩

theorem normalize {F : Type*} [Field F] (w : Fin 3 → F)
    (H3 : ∀ x y z : F, w 0 * x ^ 2 + w 1 * y ^ 2 + w 2 * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0) :
    ∃ a b : F, ∀ x y z : F, x ^ 2 + a * y ^ 2 + b * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  have hw0 : w 0 ≠ 0 := by
    intro h0
    exact one_ne_zero (H3 1 0 0 (by rw [h0]; ring)).1
  have e1 : w 0 * (w 1 / w 0) = w 1 := by field_simp
  have e2 : w 0 * (w 2 / w 0) = w 2 := by field_simp
  refine ⟨w 1 / w 0, w 2 / w 0, fun x y z h => H3 x y z ?_⟩
  linear_combination w 0 * h - y ^ 2 * e1 - z ^ 2 * e2

theorem aniso_three {F : Type*} [Field F] [NeZero (2 : F)] (h3 : 3 ∈ anisotropicDims F) :
    ∃ a b : F, ∀ x y z : F, x ^ 2 + a * y ^ 2 + b * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  obtain ⟨Q, hQ, -⟩ := h3
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hw : (weightedSumSquares F w).Anisotropic := fun v hv => by
    have h0 : e.symm v = 0 := hQ _ (by rw [e.symm.map_app]; exact hv)
    exact e.symm.toLinearEquiv.map_eq_zero_iff.mp h0
  have hm : Module.finrank F (Fin 3 → F) = 3 := by simp
  clear e
  revert w hw
  rw [hm]
  intro w hw
  exact normalize w (three_of_w w hw)

theorem u_invariant_values.variants.not_three : ¬ IsUInvariant 3 := by
  rintro ⟨F, _, _, h3, hmax⟩
  obtain ⟨a, b, H⟩ := aniso_three h3
  have h4 := four_aniso a b H
  have : 4 ≤ 3 := hmax ⟨_, h4, aniso_nondeg h4⟩
  omega

end KaplanskyUInvariant

#print axioms KaplanskyUInvariant.u_invariant_values.variants.not_three
