import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Erdős 1121 (Goodman–Goodman). `ℝ²` is restated locally
(FormalConjecturesForMathlib/Geometry/2d.lean). -/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open MeasureTheory

namespace Erdos1121

namespace GG

/-- An interval `(a, b]` covered by closed intervals `[x k - ρ k, x k + ρ k]`, `k ∈ T`,
has length at most `∑ 2 ρ k`. -/
lemma gap {ι : Type*} (T : Finset ι) (x ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) {a b : ℝ}
    (h : ∀ t, a < t → t ≤ b → ∃ k ∈ T, x k - ρ k ≤ t ∧ t ≤ x k + ρ k) :
    b - a ≤ ∑ k ∈ T, 2 * ρ k := by
  have hsub : Set.Ioc a b ⊆ ⋃ k ∈ T, Set.Icc (x k - ρ k) (x k + ρ k) := by
    intro t ht
    obtain ⟨k, hk, h1, h2⟩ := h t ht.1 ht.2
    exact Set.mem_biUnion hk ⟨h1, h2⟩
  have h1 := (measure_mono (μ := volume) hsub).trans (measure_biUnion_finset_le T _)
  simp only [Real.volume_Ioc, Real.volume_Icc] at h1
  have e : ∀ k, x k + ρ k - (x k - ρ k) = 2 * ρ k := fun k => by ring
  simp only [e] at h1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by linarith [hρ k])] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun k _ => by linarith [hρ k])).1 h1

lemma pair (n : ℕ) (ρ e : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    2 * ∑ j, ∑ l, (if e j < e l then ρ j * ρ l else 0) + ∑ j, ρ j * ρ j ≤ (∑ j, ρ j) ^ 2 := by
  have key : ∀ j l, (if e j < e l then ρ j * ρ l else 0) + (if e l < e j then ρ l * ρ j else 0)
      + (if j = l then ρ j * ρ l else 0) ≤ ρ j * ρ l := by
    intro j l
    have := mul_pos (hρ j) (hρ l)
    by_cases h1 : e j < e l
    · have h2 : ¬ e l < e j := not_lt.2 h1.le
      have h3 : j ≠ l := by rintro rfl; exact lt_irrefl _ h1
      simp [h1, h2, h3]
    · by_cases h2 : e l < e j
      · have h3 : j ≠ l := by rintro rfl; exact lt_irrefl _ h2
        simp [h1, h2, h3, mul_comm]
      · by_cases h3 : j = l
        · simp [h3]
        · simp [h1, h2, h3]; linarith
  have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => key j l
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hs
  have hc : ∑ j, ∑ l, (if e l < e j then ρ l * ρ j else 0)
      = ∑ j, ∑ l, (if e j < e l then ρ j * ρ l else 0) := Finset.sum_comm
  rw [sq, Finset.sum_mul_sum]
  linarith

/-- One-dimensional Goodman–Goodman: intervals `[x i - ρ i, x i + ρ i]` with connected union
(no uncovered point separates the centres). -/
lemma oned {n : ℕ} (x ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i)
    (H : ∀ t, (∀ i, ρ i < |t - x i|) → (∀ i, x i < t) ∨ (∀ i, t < x i)) (i : Fin n) :
    (∑ j, ρ j) * (x i + ρ i) ≤ ∑ j, ρ j * x j + (∑ j, ρ j) ^ 2 := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun j => x j + ρ j) ⟨i, Finset.mem_univ _⟩
  have hg : ∀ j, (x k + ρ k) - (x j + ρ j) ≤
      ∑ l ∈ Finset.univ.filter (fun l => x j + ρ j < x l + ρ l), 2 * ρ l := by
    intro j
    apply gap _ x ρ (fun l => (hρ l).le)
    intro t ht1 ht2
    by_contra hno
    push Not at hno
    have hall : ∀ l, ρ l < |t - x l| := by
      intro l
      have hl0 := hρ l
      by_cases hl : x j + ρ j < x l + ρ l
      · by_cases h3 : x l - ρ l ≤ t
        · have := hno l (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩) h3
          rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg (by linarith)]; linarith
      · push Not at hl
        rw [abs_of_pos (by linarith)]; linarith
    rcases H t hall with h | h
    · have h1 := hall k
      rw [abs_of_pos (by linarith [h k])] at h1
      linarith
    · have := h j
      linarith [hρ j]
  have hsum : ∑ j, ρ j * ((x k + ρ k) - x j) ≤ ∑ j, ρ j * ρ j +
      ∑ j, ρ j * ∑ l ∈ Finset.univ.filter (fun l => x j + ρ j < x l + ρ l), 2 * ρ l := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_left (hg j) (hρ j).le
    have e : ρ j * ((x k + ρ k) - x j) = ρ j * ρ j + ρ j * ((x k + ρ k) - (x j + ρ j)) := by ring
    linarith
  have hw : ∀ j, ρ j * ∑ l ∈ Finset.univ.filter (fun l => x j + ρ j < x l + ρ l), 2 * ρ l
      = 2 * ∑ l, (if x j + ρ j < x l + ρ l then ρ j * ρ l else 0) := by
    intro j
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  simp only [hw] at hsum
  rw [← Finset.mul_sum] at hsum
  have hp := pair n ρ (fun j => x j + ρ j) hρ
  beta_reduce at hp
  have hik := hk i (Finset.mem_univ _)
  have hS : 0 ≤ ∑ j, ρ j := Finset.sum_nonneg fun j _ => (hρ j).le
  have e1 : ∑ j, ρ j * ((x k + ρ k) - x j) = (∑ j, ρ j) * (x k + ρ k) - ∑ j, ρ j * x j := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have := mul_le_mul_of_nonneg_left hik hS
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma point {n : ℕ} (c : Fin n → E) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : E) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i)))
    (z : E) (hz : (∑ j, r j) • z = ∑ j, r j • c j) (i : Fin n) (p : E)
    (hp : dist p (c i) ≤ r i) : dist p z ≤ ∑ j, r j := by
  have hS : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) ⟨i, Finset.mem_univ _⟩
  rw [dist_eq_norm]
  by_cases hv : p - z = 0
  · rw [hv, norm_zero]; exact hS.le
  have hvn : 0 < ‖p - z‖ := norm_pos_iff.2 hv
  have hH : ∀ t, (∀ j, ‖p - z‖ * r j < |t - inner ℝ (p - z) (c j)|) →
      (∀ j, inner ℝ (p - z) (c j) < t) ∨ (∀ j, t < inner ℝ (p - z) (c j)) := by
    intro t ht
    apply hsep (p - z) t hv
    intro j q hq hqt
    have h1 := ht j
    have h2 : |inner ℝ (p - z) q - inner ℝ (p - z) (c j)| ≤ ‖p - z‖ * r j := by
      rw [← inner_sub_right]
      exact (abs_real_inner_le_norm (p - z) (q - c j)).trans
        (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hq)
          hvn.le)
    rw [hqt] at h2
    linarith
  have H := oned (fun j => inner ℝ (p - z) (c j)) (fun j => ‖p - z‖ * r j)
    (fun j => mul_pos hvn (hr j)) hH i
  beta_reduce at H
  have hzi : (∑ j, r j) * inner ℝ (p - z) z = ∑ j, r j * inner ℝ (p - z) (c j) := by
    rw [← real_inner_smul_right, hz, inner_sum]
    simp only [real_inner_smul_right]
  have e1 : ∑ j, ‖p - z‖ * r j = ‖p - z‖ * ∑ j, r j := by rw [Finset.mul_sum]
  have e2 : ∑ j, ‖p - z‖ * r j * inner ℝ (p - z) (c j)
      = ‖p - z‖ * ∑ j, r j * inner ℝ (p - z) (c j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e1, e2, ← hzi] at H
  have key : ‖p - z‖ * (∑ j, r j) * (inner ℝ (p - z) (c i) + ‖p - z‖ * r i) ≤
      ‖p - z‖ * (∑ j, r j) * (inner ℝ (p - z) z + ‖p - z‖ * ∑ j, r j) :=
    le_of_le_of_eq H (by ring)
  have k2 := le_of_mul_le_mul_left key (mul_pos hvn hS)
  have h3 : inner ℝ (p - z) (p - c i) ≤ ‖p - z‖ * r i :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hp) hvn.le)
  have h4 : ‖p - z‖ ^ 2 = inner ℝ (p - z) (p - z) := (real_inner_self_eq_norm_sq _).symm
  rw [inner_sub_right] at h3 h4
  have h5 : ‖p - z‖ * ‖p - z‖ ≤ ‖p - z‖ * ∑ j, r j := by nlinarith
  exact le_of_mul_le_mul_left h5 hvn

theorem cover {n : ℕ} (c : Fin n → E) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : E) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))) :
    ∃ z : E, (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) := by
  refine ⟨(∑ j, r j)⁻¹ • ∑ j, r j • c j, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
  rw [Metric.mem_closedBall] at hi ⊢
  have hS : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) ⟨i, Finset.mem_univ _⟩
  exact point c r hr hsep _ (by rw [smul_smul, mul_inv_cancel₀ hS.ne', one_smul]) i p hi

end GG

theorem erdos_1121 {n : ℕ} (c : Fin n → ℝ²) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : ℝ²) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))) :
    ∃ z : ℝ², (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) :=
  GG.cover c r hr hsep

theorem erdos_1121.variants.higher_dimension {d n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin d))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) :=
  GG.cover c r hr hsep

end Erdos1121

#print axioms Erdos1121.erdos_1121
#print axioms Erdos1121.erdos_1121.variants.higher_dimension
