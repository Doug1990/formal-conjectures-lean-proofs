import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

open Finset

namespace Erdos661

/-- first coordinate parameter -/
noncomputable def a (n k : ℕ) : ℝ := (k : ℝ) / (2 * ((n : ℝ) + 1))

noncomputable def b (n k : ℕ) : ℝ := Real.sqrt (1 / 2 - a n k ^ 2)

lemma a_nonneg (n k : ℕ) : 0 ≤ a n k := by
  unfold a; positivity

lemma a_lt (n k : ℕ) (hk : k < n) : a n k < 1 / 2 := by
  unfold a
  have h1 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  rw [div_lt_iff₀ h1]
  have : (k : ℝ) < n := by exact_mod_cast hk
  linarith

lemma a_inj (n k l : ℕ) (h : a n k = a n l) : k = l := by
  unfold a at h
  have h1 : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  rw [div_left_inj' h1] at h
  exact_mod_cast h

lemma ab_sq (n k : ℕ) (hk : k < n) : a n k ^ 2 + b n k ^ 2 = 1 / 2 := by
  have h0 := a_nonneg n k
  have h1 := a_lt n k hk
  have : a n k ^ 2 < 1 / 2 := by nlinarith
  unfold b
  rw [Real.sq_sqrt (by linarith)]
  ring

lemma b_pos (n k : ℕ) (hk : k < n) : 0 < b n k := by
  have h0 := a_nonneg n k
  have h1 := a_lt n k hk
  unfold b
  apply Real.sqrt_pos.2
  nlinarith

noncomputable def P (n k : ℕ) : EuclideanSpace ℝ (Fin 4) := !₂[a n k, b n k, 0, 0]

noncomputable def Q (n k : ℕ) : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, a n k, b n k]

lemma dist_PQ (n k l : ℕ) (hk : k < n) (hl : l < n) : dist (P n k) (Q n l) = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_four, Real.dist_eq, sq_abs, P, Q]
  have h1 := ab_sq n k hk
  have h2 := ab_sq n l hl
  have : (a n k - 0) ^ 2 + (b n k - 0) ^ 2 + (0 - a n l) ^ 2 + (0 - b n l) ^ 2 = 1 := by
    nlinarith
  simpa using this

lemma P_inj (n : ℕ) : Function.Injective (P n) := by
  intro k l h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 0) h
  simp only [P] at this
  exact a_inj n k l (by simpa using this)

lemma Q_inj (n : ℕ) : Function.Injective (Q n) := by
  intro k l h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 2) h
  simp only [Q] at this
  exact a_inj n k l (by simpa using this)

lemma P_ne_Q (n k l : ℕ) (hl : l < n) : P n k ≠ Q n l := by
  intro h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 3) h
  simp only [P, Q] at this
  have hb := b_pos n l hl
  have h' : (0 : ℝ) = b n l := by simpa using this
  linarith

theorem erdos_661.variants.lenz (n : ℕ) :
    ∃ A B : Finset (EuclideanSpace ℝ (Fin 4)), #A = n ∧ #B = n ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, dist x y = 1 := by
  refine ⟨(range n).image (P n), (range n).image (Q n), ?_, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ (P_inj n), card_range]
  · rw [card_image_of_injective _ (Q_inj n), card_range]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨k, -, rfl⟩ := mem_image.1 hx
    obtain ⟨l, hl, hkl⟩ := mem_image.1 hx'
    exact P_ne_Q n k l (mem_range.1 hl) hkl.symm
  · intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hy
    exact dist_PQ n k l (mem_range.1 hk) (mem_range.1 hl)

end Erdos661

#print axioms Erdos661.erdos_661.variants.lenz
