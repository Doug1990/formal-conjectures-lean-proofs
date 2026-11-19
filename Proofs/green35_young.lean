import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Green35

open MeasureTheory
open scoped Convolution ENNReal

/-- A nonnegative integrable function on $[0,1]$ with total integral $1$. -/
def IsUnitIntervalDensity (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ (∀ x, 0 ≤ f x) ∧ Function.support f ⊆ .Icc (0 : ℝ) 1 ∧ ∫ x, f x = 1

/-- The infimum of $\|f \ast f\|_p$ over unit-interval densities. -/
noncomputable def c (p : ℝ≥0∞) : ℝ≥0∞ :=
  sInf { r | ∃ f, IsUnitIntervalDensity f ∧ r = eLpNorm (f ⋆ f) p }

lemma key (g : ℝ → ℝ) (hg : AEStronglyMeasurable g volume) :
    eLpNorm g 2 volume ^ 2 ≤ eLpNorm g ∞ volume * ∫⁻ x, ‖g x‖ₑ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := volume) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  calc eLpNorm g 2 volume ^ 2 = eLpNorm g 2 volume ^ (2:ℝ) := (ENNReal.rpow_two _).symm
    _ = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := h
    _ = ∫⁻ x, ‖g x‖ₑ * ‖g x‖ₑ := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.rpow_two, sq]
    _ ≤ ∫⁻ x, eLpNorm g ∞ volume * ‖g x‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [enorm_ae_le_eLpNormEssSup g volume] with x hx
        rw [eLpNorm_exponent_top]
        gcongr
    _ = eLpNorm g ∞ volume * ∫⁻ x, ‖g x‖ₑ := lintegral_const_mul'' _ hg.enorm

lemma conv_nonneg (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ℝ) : 0 ≤ (f ⋆ f) x := by
  rw [convolution_def]
  refine integral_nonneg fun t => ?_
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg (hf t) (hf _)

lemma one_eq (f : ℝ → ℝ) (hf : IsUnitIntervalDensity f) :
    ∫⁻ x, ‖(f ⋆ f) x‖ₑ = 1 := by
  obtain ⟨hi, hnn, -, h1⟩ := hf
  have hI : Integrable (f ⋆ f) volume := hi.integrable_convolution _ hi
  have hint : ∫ x, (f ⋆ f) x = 1 := by
    rw [integral_convolution _ hi hi, h1]
    simp
  have e : ∀ x, ‖(f ⋆ f) x‖ₑ = ENNReal.ofReal ((f ⋆ f) x) := fun x =>
    Real.enorm_eq_ofReal (conv_nonneg f hnn x)
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => conv_nonneg f hnn x), hint, ENNReal.ofReal_one]

lemma c_le (p : ℝ≥0∞) (f : ℝ → ℝ) (hf : IsUnitIntervalDensity f) :
    c p ≤ eLpNorm (f ⋆ f) p volume := by
  unfold c
  exact sInf_le ⟨f, hf, rfl⟩

lemma per_f (f : ℝ → ℝ) (hf : IsUnitIntervalDensity f) :
    c 2 ^ 2 ≤ eLpNorm (f ⋆ f) ∞ volume := by
  have hc := c_le 2 f hf
  have hI : Integrable (f ⋆ f) volume := hf.1.integrable_convolution _ hf.1
  have h2 : c 2 ^ 2 ≤ eLpNorm (f ⋆ f) 2 volume ^ 2 := pow_le_pow_left' hc 2
  have h3 := key (f ⋆ f) hI.1
  rw [one_eq f hf, mul_one] at h3
  exact h2.trans h3

theorem c_inf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  unfold c
  refine le_sInf ?_
  rintro r ⟨f, hf, hr⟩
  rw [hr]
  have := per_f f hf
  unfold c at this
  exact this

end Green35

#print axioms Green35.c_inf_lower_young
