import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real Complex MeasureTheory
open scoped FourierTransform

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Green42

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

noncomputable def fHat (f : V → ℝ) (t : V) : ℝ :=
  (𝓕 (fun x ↦ (f x : ℂ)) t).re

def CohnElkiesAdmissible (f : V → ℝ) : Prop :=
  Continuous f ∧ ∃ C > 0, ∃ δ > 0,
    (∀ x : V, |f x| ≤ C / (1 + ‖x‖) ^ ((Module.finrank ℝ V : ℝ) + δ)) ∧
    (∀ t : V, |fHat f t| ≤ C / (1 + ‖t‖) ^ ((Module.finrank ℝ V : ℝ) + δ))

def SatisfiesCohnElkiesScheme (f : V → ℝ) : Prop :=
  CohnElkiesAdmissible f ∧
  (∀ x y : V, ‖x‖ = ‖y‖ → f x = f y) ∧
  (∀ x : V, 2 ≤ ‖x‖ → f x ≤ 0) ∧
  (∀ t : V, 0 ≤ fHat f t) ∧
  (0 < fHat f 0) ∧
  (0 < f 0)

def CohnElkiesOptimal (d : ℕ) (bound : ℝ) : Prop :=
  ∃ f : ℝ^d → ℝ,
    SatisfiesCohnElkiesScheme f ∧
    f 0 / fHat f 0 = bound

/-! ### The triangle function on ℝ -/

noncomputable def tri (x : ℝ) : ℝ := max 0 (1 - |x| / 2)

lemma tri_cont : Continuous tri := by
  unfold tri; fun_prop

lemma tri_pos (x : ℝ) (hx : 0 ≤ x) (h2 : x ≤ 2) : tri x = 1 - x / 2 := by
  unfold tri; rw [abs_of_nonneg hx]; exact max_eq_right (by linarith)

lemma tri_neg (x : ℝ) (hx : x ≤ 0) (h2 : -2 ≤ x) : tri x = 1 + x / 2 := by
  unfold tri; rw [abs_of_nonpos hx, max_eq_right (by linarith)]; ring

lemma tri_zero_of (x : ℝ) (h : 2 ≤ |x|) : tri x = 0 := by
  unfold tri; exact max_eq_left (by linarith)

lemma tri_zero_Icc (x : ℝ) (hx : x ∉ Set.Icc (-2:ℝ) 2) : tri x = 0 := by
  rcases le_or_gt 2 |x| with h | h
  · exact tri_zero_of x h
  · exfalso; apply hx; rw [abs_lt] at h; constructor <;> linarith

lemma tri_zero_Ioc (x : ℝ) (hx : x ∉ Set.Ioc (-2:ℝ) 2) : tri x = 0 := by
  rcases le_or_gt 2 |x| with h | h
  · exact tri_zero_of x h
  · exfalso; apply hx; rw [abs_lt] at h; constructor <;> linarith

lemma int_pos (ω : ℝ) (hω : ω ≠ 0) :
    ∫ x in (0:ℝ)..2, tri x * Real.cos (ω * x) = (1 - Real.cos (ω * 2)) / (2 * ω ^ 2) := by
  have e : ∫ x in (0:ℝ)..2, tri x * Real.cos (ω * x) =
      ∫ x in (0:ℝ)..2, (1 - x / 2) * Real.cos (ω * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [tri_pos x hx.1 hx.2]
  rw [e]
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 2, HasDerivAt
      (fun x => (1 - x / 2) * Real.sin (ω * x) / ω - Real.cos (ω * x) / (2 * ω ^ 2))
      ((1 - x / 2) * Real.cos (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => ω * x) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    have hs := h1.sin
    have hc := h1.cos
    have hl : HasDerivAt (fun x : ℝ => 1 - x / 2) (-(1 / 2)) x := by
      simpa using ((hasDerivAt_id x).div_const 2).const_sub 1
    have := ((hl.mul hs).div_const ω).sub (hc.div_const (2 * ω ^ 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

lemma int_neg (ω : ℝ) (hω : ω ≠ 0) :
    ∫ x in (-2:ℝ)..0, tri x * Real.cos (ω * x) = (1 - Real.cos (ω * 2)) / (2 * ω ^ 2) := by
  have e : ∫ x in (-2:ℝ)..0, tri x * Real.cos (ω * x) =
      ∫ x in (-2:ℝ)..0, (1 + x / 2) * Real.cos (ω * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [tri_neg x hx.2 hx.1]
  rw [e]
  have hd : ∀ x ∈ Set.uIcc (-2:ℝ) 0, HasDerivAt
      (fun x => (1 + x / 2) * Real.sin (ω * x) / ω + Real.cos (ω * x) / (2 * ω ^ 2))
      ((1 + x / 2) * Real.cos (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => ω * x) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    have hs := h1.sin
    have hc := h1.cos
    have hl : HasDerivAt (fun x : ℝ => 1 + x / 2) (1 / 2) x := by
      simpa using ((hasDerivAt_id x).div_const 2).const_add 1
    have := ((hl.mul hs).div_const ω).add (hc.div_const (2 * ω ^ 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show ω * (-2) = -(ω * 2) by ring, Real.sin_neg, Real.cos_neg]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

lemma int_tri (ω : ℝ) (hω : ω ≠ 0) :
    ∫ x in (-2:ℝ)..2, tri x * Real.cos (ω * x) = 2 * (Real.sin ω / ω) ^ 2 := by
  have hc : Continuous (fun x => tri x * Real.cos (ω * x)) := by
    have := tri_cont; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), int_pos ω hω, int_neg ω hω,
    show ω * 2 = 2 * ω by ring, Real.cos_two_mul, Real.cos_sq']
  field_simp
  ring

lemma int_tri_zero : ∫ x in (-2:ℝ)..2, tri x * Real.cos (0 * x) = 2 := by
  simp only [zero_mul, Real.cos_zero, mul_one]
  have hc := tri_cont
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (-2:ℝ)..0, tri x = ∫ x in (-2:ℝ)..0, (1 + x / 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact tri_neg x hx.2 hx.1
  have e2 : ∫ x in (0:ℝ)..2, tri x = ∫ x in (0:ℝ)..2, (1 - x / 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact tri_pos x hx.1 hx.2
  rw [e1, e2]
  have d1 : ∀ x ∈ Set.uIcc (-2:ℝ) 0, HasDerivAt (fun x : ℝ => x + x * x / 4) (1 + x / 2) x := by
    intro x _
    have := (hasDerivAt_id' x).add (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 4)
    exact this.congr_deriv (by ring)
  have d2 : ∀ x ∈ Set.uIcc (0:ℝ) 2, HasDerivAt (fun x : ℝ => x - x * x / 4) (1 - x / 2) x := by
    intro x _
    have := (hasDerivAt_id' x).sub (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 4)
    exact this.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt d1
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt d2
      (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-- the cosine integral `K s = ∫ tri x cos(2π s x)` -/
noncomputable def K (s : ℝ) : ℝ := ∫ x in (-2:ℝ)..2, tri x * Real.cos ((2 * π * s) * x)

lemma K_zero : K 0 = 2 := by
  unfold K; simpa using int_tri_zero

lemma K_ne (s : ℝ) (hs : s ≠ 0) : K s = 2 * (Real.sin (2 * π * s) / (2 * π * s)) ^ 2 :=
  int_tri _ (by positivity)

lemma K_nonneg (s : ℝ) : 0 ≤ K s := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [K_zero]; norm_num
  · rw [K_ne s hs]; positivity

lemma K_bound (s : ℝ) : K s * (1 + |s|) ^ 2 ≤ 9 := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [K_zero]; norm_num
  rw [K_ne s hs]
  set ω := 2 * π * s with hω
  have hω0 : ω ≠ 0 := by positivity
  have hω2 : 0 < ω ^ 2 := by positivity
  have hq0 : 0 ≤ (Real.sin ω / ω) ^ 2 := by positivity
  have hq1 : (Real.sin ω / ω) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one hω2]; exact Real.sin_sq_le_sq
  have hqω : (Real.sin ω / ω) ^ 2 * ω ^ 2 ≤ 1 := by
    rw [div_pow, div_mul_cancel₀ _ hω2.ne']; exact Real.sin_sq_le_one ω
  rcases le_or_gt |s| 1 with h1 | h1
  · have : (1 + |s|) ^ 2 ≤ 4 := by
      have : (1 + |s|) ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    calc 2 * (Real.sin ω / ω) ^ 2 * (1 + |s|) ^ 2 ≤ 2 * 1 * 4 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num)) this
            (by positivity) (by norm_num)
      _ ≤ 9 := by norm_num
  · have hpi : 1 ≤ π := by linarith [Real.two_le_pi]
    have h2 : (1 + |s|) ^ 2 ≤ ω ^ 2 := by
      have a : (1 + |s|) ^ 2 ≤ (2 * |s|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have b : (2 * |s|) ^ 2 ≤ (2 * π * |s|) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg s)
      have c : (2 * π * |s|) ^ 2 = ω ^ 2 := by
        rw [hω, mul_pow, sq_abs]; ring
      linarith
    calc 2 * (Real.sin ω / ω) ^ 2 * (1 + |s|) ^ 2
        ≤ 2 * ((Real.sin ω / ω) ^ 2 * ω ^ 2) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h2 hq0) (by norm_num)
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hqω (by norm_num)
      _ ≤ 9 := by norm_num

lemma fourier_tri (s : ℝ) : (𝓕 (fun x : ℝ => (tri x : ℂ)) s).re = K s := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * s) * Complex.I) • (tri v : ℂ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have := tri_cont; fun_prop
    · apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2))
      intro x hx
      simp [tri_zero_Icc x hx]
  have := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at this
  rw [← this]
  have pt : ∀ v : ℝ, (Complex.exp (↑(-2 * π * v * s) * Complex.I) • (tri v : ℂ)).re
      = tri v * Real.cos ((2 * π * s) * v) := by
    intro v
    rw [smul_eq_mul, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm,
      show -2 * π * v * s = -((2 * π * s) * v) by ring, Real.cos_neg]
  simp_rw [pt]
  unfold K
  rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp [tri_zero_Ioc x hx]

/-! ### Transfer to `ℝ^1` -/

noncomputable def A : ℝ ≃ₗᵢ[ℝ] ℝ^1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

noncomputable def F (x : ℝ^1) : ℝ := max 0 (1 - ‖x‖ / 2)

lemma F_A (x : ℝ) : F (A x) = tri x := by
  simp only [F, tri, A.norm_map, Real.norm_eq_abs]

lemma fHat_F (t : ℝ^1) : fHat F t = K (A.symm t) := by
  unfold fHat
  rw [← fourier_tri]
  congr 1
  calc 𝓕 (fun x ↦ (F x : ℂ)) t = 𝓕 (fun x ↦ (F x : ℂ)) (A (A.symm t)) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = 𝓕 ((fun x ↦ (F x : ℂ)) ∘ A) (A.symm t) :=
        (Real.fourier_comp_linearIsometry A _ _).symm
    _ = 𝓕 (fun x : ℝ => (tri x : ℂ)) (A.symm t) := by
        rw [show ((fun x ↦ (F x : ℂ)) ∘ A) = (fun x : ℝ => (tri x : ℂ)) from
          funext fun x => by simp only [Function.comp_apply, F_A]]

lemma norm_symm (t : ℝ^1) : |A.symm t| = ‖t‖ := by
  rw [← Real.norm_eq_abs, LinearIsometryEquiv.norm_map]

lemma F_cont : Continuous F := by
  unfold F; fun_prop

lemma F0 : F 0 = 1 := by
  unfold F; rw [norm_zero, zero_div, sub_zero]; exact max_eq_right zero_le_one

lemma K0' : fHat F 0 = 2 := by rw [fHat_F, map_zero, K_zero]

lemma F_bound (x : ℝ^1) : |F x| * (1 + ‖x‖) ^ 2 ≤ 9 := by
    rcases le_or_gt 2 ‖x‖ with h | h
    · have : F x = 0 := by unfold F; exact max_eq_left (by linarith)
      rw [this]; norm_num
    · have h0 : 0 ≤ F x := le_max_left _ _
      have h1 : F x ≤ 1 := by
        unfold F; apply max_le (by norm_num); linarith [norm_nonneg x]
      rw [abs_of_nonneg h0]
      have : (1 + ‖x‖) ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc F x * (1 + ‖x‖) ^ 2 ≤ 1 * 3 ^ 2 :=
            mul_le_mul h1 this (by positivity) (by norm_num)
        _ ≤ 9 := by norm_num

lemma Fhat_bound (t : ℝ^1) : |fHat F t| * (1 + ‖t‖) ^ 2 ≤ 9 := by
  rw [fHat_F, abs_of_nonneg (K_nonneg _), ← norm_symm]
  exact K_bound _

lemma rpow_e (y : ℝ) :
    y ^ ((Module.finrank ℝ (ℝ^1) : ℝ) + 1) = y ^ 2 := by
  rw [finrank_euclideanSpace_fin, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num, Real.rpow_two]

theorem green_42.variants.dimension_one :
    CohnElkiesOptimal 1 (1 / 2) := by
  refine ⟨F, ⟨⟨F_cont, 9, by norm_num, 1, one_pos, fun x => ?_, fun t => ?_⟩,
    fun x y h => ?_, fun x h => ?_, fun t => ?_, ?_, ?_⟩, ?_⟩
  · rw [rpow_e, le_div_iff₀ (by positivity)]; exact F_bound x
  · rw [rpow_e, le_div_iff₀ (by positivity)]; exact Fhat_bound t
  · simp only [F, h]
  · unfold F; exact max_le (le_refl _) (by linarith)
  · rw [fHat_F]; exact K_nonneg _
  · rw [K0']; norm_num
  · rw [F0]; norm_num
  · rw [F0, K0']

end Green42

#print axioms Green42.green_42.variants.dimension_one
