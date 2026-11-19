import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Algebra.BigOperators.Field

open Filter Matrix

open scoped Topology

namespace Arxiv.«2607.05349»

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X]

noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X] (t : ℝ) :
    Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] : Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] (t : ℝ) :
    X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Tendsto (weighting X) (𝓝[>] 0) (𝓝 w)

def IsGauging (M : Matrix X X ℝ) (g : X → ℝ) (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

def HasFiniteConcentration (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging M g c

omit [Nonempty X] in
lemma det_analytic (t : ℝ) : AnalyticAt ℝ (fun t => (similarityMatrix X t).det) t := by
  have e : (fun t => (similarityMatrix X t).det) =
      fun t => ∑ σ : Equiv.Perm X, (Equiv.Perm.sign σ : ℝ) *
        ∏ i, Real.exp (-t * dist (σ i) i) := by
    funext t
    rw [Matrix.det_apply']
    rfl
  rw [e]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ (fun i _ => ?_)))
  exact ((analyticAt_id.neg).mul analyticAt_const).rexp'

omit [Nonempty X] in
lemma det_tendsto_atTop :
    Tendsto (fun t => (similarityMatrix X t).det) atTop (𝓝 1) := by
  have hZ : Tendsto (fun t => similarityMatrix X t) atTop (𝓝 (1 : Matrix X X ℝ)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [similarityMatrix, Matrix.of_apply, dist_self, mul_zero, Real.exp_zero,
        Matrix.one_apply_eq]
      exact tendsto_const_nhds
    · have hd : 0 < dist i j := dist_pos.2 hij
      simp only [similarityMatrix, Matrix.of_apply, Matrix.one_apply_ne hij]
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_mul_const hd)
  have hc := ((continuous_id (X := Matrix X X ℝ)).matrix_det).tendsto (1 : Matrix X X ℝ)
  have h2 := hc.comp hZ
  simp only [Function.comp_def, id_eq, Matrix.det_one] at h2
  exact h2

omit [Nonempty X] in
lemma det_ne_zero_near :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (similarityMatrix X t).det ≠ 0 := by
  rcases (det_analytic (X := X) 0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have han : AnalyticOnNhd ℝ (fun t => (similarityMatrix X t).det) Set.univ :=
      fun t _ => det_analytic (X := X) t
    have hall : Set.EqOn (fun t => (similarityMatrix X t).det) 0 Set.univ :=
      han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ 0) h
    obtain ⟨T, hT⟩ := ((det_tendsto_atTop (X := X)).eventually_ne one_ne_zero).exists
    exact hT (hall (Set.mem_univ T))
  · exact h.filter_mono (nhdsWithin_mono _ (fun x (hx : 0 < x) => hx.ne'))

lemma slope_tendsto (d : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (-t * d) - 1) / t) (𝓝[>] 0) (𝓝 (-d)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-t * d)) (-d) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).neg.mul_const d).exp
    simpa using this
  refine hd.tendsto_slope_zero_right.congr (fun t => ?_)
  simp only [zero_add, neg_zero, zero_mul, Real.exp_zero, smul_eq_mul]
  ring

theorem hasFiniteConcentration_of_hasMicroscopicWeighting
    (h : HasMicroscopicWeighting X) : HasFiniteConcentration (distanceMatrix X) := by
  obtain ⟨w, hw⟩ := h
  have hwj : ∀ j, Tendsto (fun t => weighting X t j) (𝓝[>] 0) (𝓝 (w j)) :=
    fun j => tendsto_pi_nhds.1 hw j
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ∀ i,
      ∑ j, Real.exp (-t * dist i j) * weighting X t j = 1 := by
    filter_upwards [det_ne_zero_near (X := X), self_mem_nhdsWithin] with t ht ht0
    refine ⟨ht0, fun i => ?_⟩
    have hmul : similarityMatrix X t *ᵥ weighting X t = 1 := by
      rw [weighting, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ht), Matrix.one_mulVec]
    have := congrFun hmul i
    simpa [Matrix.mulVec, dotProduct, similarityMatrix] using this
  set S : ℝ → ℝ := fun t => ∑ j, weighting X t j with hS
  have hq : ∀ i, Tendsto (fun t => (1 - S t) / t) (𝓝[>] 0)
      (𝓝 (∑ j, (-dist i j) * w j)) := by
    intro i
    have hlim : Tendsto (fun t => ∑ j, (Real.exp (-t * dist i j) - 1) / t * weighting X t j)
        (𝓝[>] 0) (𝓝 (∑ j, (-dist i j) * w j)) :=
      tendsto_finsetSum _ (fun j _ => (slope_tendsto (dist i j)).mul (hwj j))
    refine hlim.congr' ?_
    filter_upwards [hev] with t ⟨ht0, ht⟩
    show _ = (1 - ∑ j, weighting X t j) / t
    have key : ∑ j, (Real.exp (-t * dist i j) - 1) / t * weighting X t j =
        (∑ j, Real.exp (-t * dist i j) * weighting X t j - ∑ j, weighting X t j) / t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [key, ht i]
  obtain ⟨i0⟩ := ‹Nonempty X›
  have hS1 : Tendsto S (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have := (tendsto_const_nhds (x := (1:ℝ))).sub (h0.mul (hq i0))
    rw [zero_mul, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ⟨ht0, _⟩
    field_simp
    ring
  have hSw : Tendsto S (𝓝[>] 0) (𝓝 (∑ j, w j)) :=
    tendsto_finsetSum _ (fun j _ => hwj j)
  have hsum : ∑ j, w j = 1 := tendsto_nhds_unique hSw hS1
  refine ⟨w, -∑ j, (-dist i0 j) * w j, hsum, ?_⟩
  funext i
  have := tendsto_nhds_unique (hq i) (hq i0)
  simp only [Matrix.mulVec, dotProduct, distanceMatrix, Matrix.of_apply, Function.const_apply]
  rw [← this]
  simp [Finset.sum_neg_distrib]

noncomputable def Bm (X : Type*) [Fintype X] [MetricSpace X] (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun i j => (1 - Real.exp (-t * dist i j)) / t

omit [DecidableEq X] [Nonempty X] in
lemma Bm_tendsto : Tendsto (Bm X) (𝓝[>] 0) (𝓝 (distanceMatrix X)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Tendsto _ _ (𝓝 (dist i j))
  have := (slope_tendsto (dist i j)).neg
  rw [neg_neg] at this
  refine this.congr (fun t => ?_)
  simp only [Bm, Matrix.of_apply]
  ring

omit [Nonempty X] [MetricSpace X] in
lemma inv_tendsto {F : Filter ℝ} {B : ℝ → Matrix X X ℝ} {D : Matrix X X ℝ}
    (hB : Tendsto B F (𝓝 D)) (hD : D.det ≠ 0) :
    Tendsto (fun t => (B t)⁻¹) F (𝓝 D⁻¹) := by
  have hdet : Tendsto (fun t => (B t).det) F (𝓝 D.det) :=
    ((continuous_id.matrix_det).tendsto D).comp hB
  have hadj : Tendsto (fun t => (B t).adjugate) F (𝓝 D.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto D).comp hB
  have := (hdet.inv₀ hD).smul hadj
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact this

omit [DecidableEq X] [Nonempty X] in
/-- If `B t *ᵥ u = 1` and `σ - t ≠ 0` then `v = (σ - t)⁻¹ • u` solves `Z t *ᵥ v = 1`. -/
lemma Z_mulVec (t : ℝ) (ht : t ≠ 0) (u : X → ℝ) (hu : Bm X t *ᵥ u = 1)
    (hs : ∑ j, u j - t ≠ 0) :
    similarityMatrix X t *ᵥ ((∑ j, u j - t)⁻¹ • u) = 1 := by
  funext i
  have hi := congrFun hu i
  simp only [Matrix.mulVec, dotProduct, Bm, Matrix.of_apply, Pi.one_apply] at hi
  simp only [Matrix.mulVec, dotProduct, similarityMatrix, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, Pi.one_apply]
  have key : ∑ j, Real.exp (-t * dist i j) * u j =
      ∑ j, u j - t * ∑ j, (1 - Real.exp (-t * dist i j)) / t * u j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    field_simp
    ring
  rw [hi, mul_one] at key
  have : ∑ j, Real.exp (-t * dist i j) * ((∑ j, u j - t)⁻¹ * u j) =
      (∑ j, u j - t)⁻¹ * ∑ j, Real.exp (-t * dist i j) * u j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this, key, inv_mul_cancel₀ hs]

theorem hasMicroscopicWeighting_iff_of_isUnit (h : IsUnit (distanceMatrix X).det) :
    HasMicroscopicWeighting X ↔ HasFiniteConcentration (distanceMatrix X) := by
  refine ⟨hasFiniteConcentration_of_hasMicroscopicWeighting, ?_⟩
  rintro ⟨g, c, hgs, hg⟩
  set D := distanceMatrix X with hDdef
  have hD : D.det ≠ 0 := h.ne_zero
  set u0 : X → ℝ := D⁻¹ *ᵥ 1 with hu0
  set s0 : ℝ := ∑ j, u0 j with hs0
  have hgu : g = c • u0 := by
    have : D⁻¹ *ᵥ (D *ᵥ g) = g := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
    rw [← this, hg, hu0, ← Matrix.mulVec_smul]
    congr 1
    funext j
    simp
  have hs0ne : s0 ≠ 0 := by
    intro h0
    rw [hgu] at hgs
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hgs
    rw [← hs0, h0, mul_zero] at hgs
    exact zero_ne_one hgs
  have hBinv : Tendsto (fun t => (Bm X t)⁻¹) (𝓝[>] 0) (𝓝 D⁻¹) :=
    inv_tendsto Bm_tendsto hD
  have hu : Tendsto (fun t => (Bm X t)⁻¹ *ᵥ (1 : X → ℝ)) (𝓝[>] 0) (𝓝 u0) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto D⁻¹).comp hBinv
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hσ : Tendsto (fun t => ∑ j, ((Bm X t)⁻¹ *ᵥ (1 : X → ℝ)) j - t) (𝓝[>] 0)
      (𝓝 s0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset X)
      (fun j _ => tendsto_pi_nhds.1 hu j)).sub h0
    rw [sub_zero] at this
    exact this
  have hv := (hσ.inv₀ hs0ne).smul hu
  refine ⟨s0⁻¹ • u0, hv.congr' ?_⟩
  have hdetB : ∀ᶠ t in 𝓝[>] (0 : ℝ), (Bm X t).det ≠ 0 :=
    (((continuous_id.matrix_det).tendsto D).comp Bm_tendsto).eventually_ne hD
  filter_upwards [hdetB, det_ne_zero_near (X := X), hσ.eventually_ne hs0ne,
    self_mem_nhdsWithin] with t hB hZ hs (ht : 0 < t)
  have hBu : Bm X t *ᵥ ((Bm X t)⁻¹ *ᵥ (1 : X → ℝ)) = 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hB),
      Matrix.one_mulVec]
  have hZv := Z_mulVec t ht.ne' _ hBu hs
  rw [weighting]
  conv_rhs => rw [← hZv, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hZ), Matrix.one_mulVec]

#print axioms hasMicroscopicWeighting_iff_of_isUnit

end Arxiv.«2607.05349»
