import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Order.Chebyshev

open Nat

namespace Erdos499

namespace OL

open Finset Matrix

variable {n : ℕ}

lemma entry {M : Matrix (Fin n) (Fin n) ℝ} (w : Equiv.Perm (Fin n) → ℝ)
    (hsum : ∑ σ, w σ • σ.permMatrix ℝ = M) (i j : Fin n) :
    M i j = ∑ σ, w σ * (if σ i = j then 1 else 0) := by
  rw [← hsum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma key {M : Matrix (Fin n) (Fin n) ℝ} (w : Equiv.Perm (Fin n) → ℝ)
    (hsum : ∑ σ, w σ • σ.permMatrix ℝ = M) :
    ∑ σ, w σ * ∑ i, M i (σ i) = ∑ i, ∑ j, M i j ^ 2 := by
  have h1 : ∀ i, ∑ j, M i j ^ 2 = ∑ σ, w σ * M i (σ i) := by
    intro i
    calc ∑ j, M i j ^ 2 = ∑ j, (∑ σ, w σ * (if σ i = j then 1 else 0)) * M i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← entry w hsum i j, sq]
      _ = ∑ σ, ∑ j, w σ * ((if σ i = j then 1 else 0) * M i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ _ => ?_
          ring
      _ = ∑ σ, w σ * M i (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← Finset.mul_sum]
          simp
  simp_rw [h1, Finset.mul_sum]
  exact Finset.sum_comm

lemma sq_ge {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n)) (hn : 0 < n) :
    1 ≤ ∑ i, ∑ j, M i j ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow : ∀ i, 1 / (n : ℝ) ≤ ∑ j, M i j ^ 2 := by
    intro i
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun j => M i j)
    rw [sum_row_of_mem_doublyStochastic hM i] at h
    simp only [Finset.card_univ, Fintype.card_fin, one_pow] at h
    rw [div_le_iff₀ hn']
    linarith
  calc (1 : ℝ) = ∑ _i : Fin n, 1 / (n : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hrow i

end OL

theorem erdos_499.variants.one_le :
    ∀ n > 0, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      (∀ i, M i (σ i) ≠ 0) ∧ 1 ≤ ∑ i, M i (σ i) := by
  intro n hn M hM
  obtain ⟨w, hw0, hw1, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hk := OL.key w hsum
  have hsq := OL.sq_ge hM hn
  have hex : ∃ σ, 0 < w σ ∧ 1 ≤ ∑ i, M i (σ i) := by
    by_contra hcon
    push Not at hcon
    have hpos : ∃ σ, 0 < w σ := by
      by_contra h0
      push Not at h0
      have : ∑ σ, w σ ≤ 0 := Finset.sum_nonpos fun σ _ => h0 σ
      linarith
    obtain ⟨τ, hτ⟩ := hpos
    have hlt : ∑ σ, w σ * ∑ i, M i (σ i) < ∑ σ, w σ * 1 := by
      refine Finset.sum_lt_sum (fun σ _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩
      · rcases (hw0 σ).lt_or_eq with h | h
        · exact mul_le_mul_of_nonneg_left (hcon σ h).le h.le
        · rw [← h]; simp
      · exact mul_lt_mul_of_pos_left (hcon τ hτ) hτ
    simp only [mul_one, hw1] at hlt
    linarith
  obtain ⟨σ, hσ, hS⟩ := hex
  refine ⟨σ, fun i => ?_, hS⟩
  have hge : w σ ≤ M i (σ i) := by
    rw [OL.entry w hsum i (σ i)]
    have := Finset.single_le_sum (f := fun τ => w τ * (if τ i = σ i then (1 : ℝ) else 0))
      (fun τ _ => by
        by_cases h : τ i = σ i
        · simp [h, hw0 τ]
        · simp [h]) (Finset.mem_univ σ)
    simpa using this
  exact (lt_of_lt_of_le hσ hge).ne'

end Erdos499

#print axioms Erdos499.erdos_499.variants.one_le
