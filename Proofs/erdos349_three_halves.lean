import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
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

/-- Every term of `⌊(3/2)·2^n⌋` is `1` or a multiple of `3`. -/
lemma term (n : ℕ) : ⌊(3 / 2 : ℝ) * 2 ^ n⌋ = 1 ∨ (3 : ℤ) ∣ ⌊(3 / 2 : ℝ) * 2 ^ n⌋ := by
  cases n with
  | zero =>
    left
    rw [Int.floor_eq_iff]
    norm_num
  | succ m =>
    right
    have h : (3 / 2 : ℝ) * 2 ^ (m + 1) = ((3 * 2 ^ m : ℤ) : ℝ) := by
      push_cast; ring
    rw [h, Int.floor_intCast]
    exact Dvd.intro _ rfl

/-- A finite set of integers, each `1` or a multiple of `3`, has sum `≡ 0` or `1` mod 3. -/
lemma sum_mod (B : Finset ℤ) (hB : ∀ x ∈ B, x = 1 ∨ (3 : ℤ) ∣ x) :
    (∑ i ∈ B, i) % 3 = 0 ∨ (∑ i ∈ B, i) % 3 = 1 := by
  rw [← Finset.sum_filter_add_sum_filter_not B (fun x => x = 1)]
  have h3 : (3 : ℤ) ∣ ∑ i ∈ B.filter (fun x => ¬ x = 1), i := by
    refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rcases hB i hi.1 with h | h
    · exact absurd h hi.2
    · exact h
  have hs : B.filter (fun x => x = 1) ⊆ {1} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_singleton]; exact hx.2
  obtain ⟨c, hc⟩ := h3
  rcases Finset.subset_singleton_iff.1 hs with h | h
  · rw [h, hc]; simp
  · rw [h, hc]; simp

theorem three_halves_two_not_isGoodPair : ¬ IsGoodPair (3 / 2) 2 := by
  intro hgood
  unfold IsGoodPair IsAddComplete at hgood
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hgood
  obtain ⟨B, hBsub, hk⟩ := hN (3 * (N.natAbs : ℤ) + 2) (by omega)
  have hB : ∀ x ∈ B, x = 1 ∨ (3 : ℤ) ∣ x := by
    intro x hx
    obtain ⟨n, rfl⟩ := hBsub (Finset.mem_coe.2 hx)
    exact term n
  have := sum_mod B hB
  rw [← hk] at this
  omega

end Erdos349

#print axioms Erdos349.three_halves_two_not_isGoodPair
