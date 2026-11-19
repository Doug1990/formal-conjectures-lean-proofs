import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Local restatement of `subsetSums` / `IsAddComplete` from
FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean (same bodies). -/

section
variable {M : Type*} [AddCommMonoid M]

def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

def IsAddComplete [Preorder M] (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A
end

namespace Erdos349

open Set Filter Real Nat Function

def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n ↦ ⌊t * α ^ n⌋))

/-- A gap: an integer strictly between the partial sum `a 0 + ⋯ + a (n-1)` and `a n` is not a
sum of distinct terms of a nonnegative monotone sequence. -/
lemma gap (a : ℕ → ℤ) (h0 : ∀ n, 0 ≤ a n) (hmono : Monotone a) (n : ℕ) (k : ℤ)
    (hk1 : ∑ m ∈ Finset.range n, a m < k) (hk2 : k < a n) :
    k ∉ subsetSums (range a) := by
  rintro ⟨C, hC, hsum⟩
  have hCnn : ∀ j ∈ C, 0 ≤ j := fun j hj => by
    obtain ⟨l, rfl⟩ := hC (Finset.mem_coe.2 hj); exact h0 l
  have hsub : C ⊆ (Finset.range n).image a := by
    intro c hc
    obtain ⟨i, rfl⟩ := hC (Finset.mem_coe.2 hc)
    have hle : a i ≤ ∑ j ∈ C, j :=
      Finset.single_le_sum (f := fun j => j) hCnn hc
    have hi : i < n := by
      by_contra hcon
      have := hmono (not_lt.1 hcon)
      omega
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have h1 : ∑ j ∈ C, j ≤ ∑ i ∈ Finset.range n, a i :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hj; exact h0 l)).trans
      (Finset.sum_image_le_of_nonneg fun u hu => by
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hu; exact h0 l)
  omega

theorem alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) :
    ¬ IsGoodPair t α := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have h0 : ∀ n : ℕ, 0 ≤ ⌊t * α ^ n⌋ := fun n =>
    Int.floor_nonneg.2 (mul_nonneg ht.le (pow_nonneg hα0 n))
  have hmono : Monotone (fun n : ℕ ↦ ⌊t * α ^ n⌋) := by
    intro m n hmn
    exact Int.floor_mono
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hmn) ht.le)
  intro hgood
  unfold IsGoodPair IsAddComplete at hgood
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hgood
  set X : ℝ := |(N : ℝ)| + 2 with hX
  have hD : 0 < t * (α - 2) := mul_pos ht (by linarith)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (X * (α - 1) / (t * (α - 2)))
    (by linarith : (1 : ℝ) < α)
  have key : X * (α - 1) < α ^ n * (t * (α - 2)) := (div_lt_iff₀ hD).1 hn
  set P : ℝ := α ^ n with hP
  set G : ℝ := ∑ m ∈ Finset.range n, α ^ m with hG
  have hgeom : G * (α - 1) = P - 1 := geom_sum_mul α n
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun m _ => pow_nonneg hα0 m
  have hmain : t * G ≤ t * P - X := by
    refine le_of_mul_le_mul_right ?_ hα1
    have e1 : t * G * (α - 1) = t * P - t := by rw [mul_assoc, hgeom]; ring
    have e2 : (t * P - X) * (α - 1) = t * P + (P * (t * (α - 2)) - X * (α - 1)) := by ring
    rw [e1, e2]
    linarith
  have hX2 : (2 : ℝ) ≤ X := by have := abs_nonneg (N : ℝ); linarith
  have hfl : t * P - 1 < (⌊t * α ^ n⌋ : ℝ) := Int.sub_one_lt_floor _
  have hsumR : ((∑ m ∈ Finset.range n, ⌊t * α ^ m⌋ : ℤ) : ℝ) ≤ t * G := by
    push_cast
    rw [hG, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ => Int.floor_le _
  have hk1R : ((∑ m ∈ Finset.range n, ⌊t * α ^ m⌋ : ℤ) : ℝ)
      < ((⌊t * α ^ n⌋ - 1 : ℤ) : ℝ) := by
    have := hsumR
    push_cast at this ⊢; linarith
  have hk1 : ∑ m ∈ Finset.range n, ⌊t * α ^ m⌋ < ⌊t * α ^ n⌋ - 1 := by exact_mod_cast hk1R
  have hNR : (N : ℝ) ≤ ((⌊t * α ^ n⌋ - 1 : ℤ) : ℝ) := by
    have := le_abs_self (N : ℝ)
    have := mul_nonneg ht.le hG0
    push_cast; linarith
  have hNk : N ≤ ⌊t * α ^ n⌋ - 1 := by exact_mod_cast hNR
  exact gap (fun n : ℕ ↦ ⌊t * α ^ n⌋) h0 hmono n _ hk1 (by omega) (hN _ hNk)

end Erdos349

#print axioms Erdos349.alpha_gt_two_not_isGoodPair
