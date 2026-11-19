import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

open Set MeasureTheory Filter Topology

namespace Erdos120

def Erdos120For (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  MeasurableSet E ∧ 0 < volume E ∧ ∀ a b : ℝ, a ≠ 0 → ¬ .image (fun x => a * x + b) A ⊆ E

theorem erdos_120.variants.finite_set {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  rintro ⟨E, hE, hpos, hno⟩
  -- a Lebesgue density point
  have hne : volume.restrict E ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne'
  have : (ae (volume.restrict E)).NeBot := ae_neBot.2 hne
  obtain ⟨x, hx⟩ := (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) E).exists
  -- a bound on A
  obtain ⟨M0, hM0⟩ := (h.image abs).bddAbove
  set M : ℝ := |M0| + 1 with hMdef
  have hM : 0 < M := by positivity
  have hAM : ∀ a ∈ A, |a| ≤ M := fun a ha =>
    (hM0 ⟨a, ha, rfl⟩).trans ((le_abs_self M0).trans (by linarith))
  set T := h.toFinset with hT
  set n : ℕ := T.card with hn
  set δ : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδdef, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hδn : (n : ℝ) * δ * 2 < 1 := by
    have h4 : δ * (4 * ((n : ℝ) + 1)) = 1 := by
      rw [hδdef]; field_simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  -- real ratio
  have ht := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hx
  simp only [ENNReal.toReal_one] at ht
  have hev := (ht.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  obtain ⟨r, hr1, hr0⟩ := hev.exists
  simp only [Function.comp_apply] at hr1
  have hr0' : (0 : ℝ) < r := hr0
  set B := Metric.closedBall x r with hB
  have hvB : volume B = ENNReal.ofReal (2 * r) := Real.volume_closedBall x r
  have hBfin : volume B ≠ ⊤ := by rw [hvB]; exact ENNReal.ofReal_ne_top
  have hEBfin : volume (E ∩ B) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono inter_subset_right)
  have hBEfin : volume (B \ E) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono sdiff_subset)
  rw [ENNReal.toReal_div, hvB, ENNReal.toReal_ofReal (by linarith),
    lt_div_iff₀ (by linarith)] at hr1
  have hsum : volume (B ∩ E) + volume (B \ E) = volume B := measure_inter_add_sdiff B hE
  rw [inter_comm] at hsum
  have hsumR : (volume (E ∩ B)).toReal + (volume (B \ E)).toReal = 2 * r := by
    rw [← ENNReal.toReal_add hEBfin hBEfin, hsum, hvB, ENNReal.toReal_ofReal (by linarith)]
  have hm2 : (volume (B \ E)).toReal < δ * (2 * r) := by nlinarith
  -- the scaling
  set s : ℝ := r / (2 * M) with hs
  have hs0 : 0 < s := by positivity
  have hsM : s * M = r / 2 := by rw [hs]; field_simp
  have key : ∃ b ∈ Metric.closedBall x (r / 2), ∀ a ∈ A, b + s * a ∈ E := by
    by_contra hcon
    push Not at hcon
    have hsub : Metric.closedBall x (r / 2) ⊆
        ⋃ a ∈ T, (fun b => b + s * a) ⁻¹' (B \ E) := by
      intro b hb
      obtain ⟨a, ha, hbE⟩ := hcon b hb
      simp only [mem_iUnion, mem_preimage]
      refine ⟨a, by rw [hT, Finite.mem_toFinset]; exact ha, ?_, hbE⟩
      rw [hB, Metric.mem_closedBall, Real.dist_eq]
      rw [Metric.mem_closedBall, Real.dist_eq] at hb
      have h1 : |s * a| ≤ r / 2 := by
        rw [abs_mul, abs_of_pos hs0, ← hsM]
        exact mul_le_mul_of_nonneg_left (hAM a ha) hs0.le
      calc |b + s * a - x| = |(b - x) + s * a| := by ring_nf
        _ ≤ |b - x| + |s * a| := abs_add_le _ _
        _ ≤ r := by linarith
    have hle := (measure_mono (μ := (volume : Measure ℝ)) hsub).trans
      (measure_biUnion_finset_le (μ := (volume : Measure ℝ)) T _)
    simp only [measure_preimage_add_right volume, Finset.sum_const, nsmul_eq_mul] at hle
    rw [Real.volume_closedBall] at hle
    have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hBEfin) hle
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle'
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (n : ℝ) * (volume (B \ E)).toReal ≤ n * (δ * (2 * r)) :=
      mul_le_mul_of_nonneg_left hm2.le hn0
    nlinarith
  obtain ⟨b, -, hb⟩ := key
  apply hno s b hs0.ne'
  rintro _ ⟨y, hy, rfl⟩
  show s * y + b ∈ E
  rw [add_comm]
  exact hb y hy

end Erdos120

#print axioms Erdos120.erdos_120.variants.finite_set
