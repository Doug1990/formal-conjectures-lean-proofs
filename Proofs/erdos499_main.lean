import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

namespace Erdos499

namespace MM

open Finset Matrix

variable {n : ℕ}

lemma entry {M : Matrix (Fin n) (Fin n) ℝ} (w : Equiv.Perm (Fin n) → ℝ)
    (hsum : ∑ σ, w σ • σ.permMatrix ℝ = M) (i j : Fin n) :
    M i j = ∑ σ, w σ * (if σ i = j then 1 else 0) := by
  rw [← hsum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma keyf {M : Matrix (Fin n) (Fin n) ℝ} (w : Equiv.Perm (Fin n) → ℝ)
    (hsum : ∑ σ, w σ • σ.permMatrix ℝ = M) (f : Fin n → Fin n → ℝ) :
    ∑ σ, w σ * ∑ i, f i (σ i) = ∑ i, ∑ j, M i j * f i j := by
  have h1 : ∀ i, ∑ j, M i j * f i j = ∑ σ, w σ * f i (σ i) := by
    intro i
    calc ∑ j, M i j * f i j = ∑ j, (∑ σ, w σ * (if σ i = j then 1 else 0)) * f i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← entry w hsum i j]
      _ = ∑ σ, ∑ j, w σ * ((if σ i = j then 1 else 0) * f i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ _ => ?_
          ring
      _ = ∑ σ, w σ * f i (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← Finset.mul_sum]
          simp
  simp_rw [h1, Finset.mul_sum]
  exact Finset.sum_comm

lemma ge_w {M : Matrix (Fin n) (Fin n) ℝ} (w : Equiv.Perm (Fin n) → ℝ) (hw0 : ∀ σ, 0 ≤ w σ)
    (hsum : ∑ σ, w σ • σ.permMatrix ℝ = M) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    w σ ≤ M i (σ i) := by
  rw [entry w hsum i (σ i)]
  have := Finset.single_le_sum (f := fun τ => w τ * (if τ i = σ i then (1 : ℝ) else 0))
    (fun τ _ => by
      by_cases h : τ i = σ i
      · simp [h, hw0 τ]
      · simp [h]) (Finset.mem_univ σ)
  simpa using this

/-- Entropy bound: a probability vector on `n` points has `Σ p log p ≥ -log n`. -/
lemma entropy (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (h1 : ∑ j, p j = 1) (hn : 0 < n) :
    -Real.log n ≤ ∑ j, p j * Real.log (p j) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ j, p j - 1 / (n : ℝ) ≤ p j * Real.log n + p j * Real.log (p j) := by
    intro j
    rcases (hp j).lt_or_eq with h | h
    · have hl := Real.one_sub_inv_le_log_of_pos (mul_pos hn' h)
      rw [Real.log_mul hn'.ne' h.ne'] at hl
      have e : p j * (1 - ((n : ℝ) * p j)⁻¹) = p j - 1 / n := by
        field_simp
      have := mul_le_mul_of_nonneg_left hl h.le
      rw [e] at this
      linarith
    · rw [← h]
      simp only [zero_mul, add_zero, zero_sub, Left.neg_nonpos_iff]
      positivity
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, h1] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have e2 : (n : ℝ) * (1 / n) = 1 := by field_simp
  rw [e2] at hs
  linarith

end MM

lemma erdos_499 :
    (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by
  intro n M hM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp⟩
  obtain ⟨w, hw0, hw1, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hk := MM.keyf w hsum (fun i j => Real.log (M i j))
  have hrow : ∀ i, -Real.log n ≤ ∑ j, M i j * Real.log (M i j) := fun i =>
    MM.entropy (fun j => M i j) (fun j => nonneg_of_mem_doublyStochastic hM)
      (sum_row_of_mem_doublyStochastic hM i) hn
  set c : ℝ := -(n * Real.log n) with hc
  have hsumge : c ≤ ∑ i, ∑ j, M i j * Real.log (M i j) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hrow i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [hc]; linarith
  have hex : ∃ σ, 0 < w σ ∧ c ≤ ∑ i, Real.log (M i (σ i)) := by
    by_contra hcon
    push Not at hcon
    have hpos : ∃ σ, 0 < w σ := by
      by_contra h0
      push Not at h0
      have : ∑ σ, w σ ≤ 0 := Finset.sum_nonpos fun σ _ => h0 σ
      linarith
    obtain ⟨τ, hτ⟩ := hpos
    have hlt : ∑ σ, w σ * ∑ i, Real.log (M i (σ i)) < ∑ σ, w σ * c := by
      refine Finset.sum_lt_sum (fun σ _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩
      · rcases (hw0 σ).lt_or_eq with h | h
        · exact mul_le_mul_of_nonneg_left (hcon σ h).le h.le
        · rw [← h]; simp
      · exact mul_lt_mul_of_pos_left (hcon τ hτ) hτ
    rw [← Finset.sum_mul, hw1, one_mul] at hlt
    linarith
  obtain ⟨σ, hσ, hS⟩ := hex
  refine ⟨σ, ?_⟩
  have hpos : ∀ i, 0 < M i (σ i) := fun i => lt_of_lt_of_le hσ (MM.ge_w w hw0 hsum σ i)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_le_log_iff (zpow_pos hn' _) (Finset.prod_pos fun i _ => hpos i),
    Real.log_zpow, Real.log_prod fun i _ => (hpos i).ne']
  push_cast
  rw [hc] at hS
  linarith

end Erdos499

#print axioms Erdos499.erdos_499
