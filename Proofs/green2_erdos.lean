import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Green2

def maxRestrictedSumAvoidingSubsetSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter fun S => Disjoint S.restrictedSumset A).sup Finset.card

lemma mem_rs {S : Finset ℤ} {a y : ℤ} (ha : a ∈ S) (hy : y ∈ S) (hne : a ≠ y) :
    a + y ∈ S.restrictedSumset :=
  Finset.mem_image.2 ⟨(a, y), Finset.mem_offDiag.2 ⟨ha, hy, hne⟩, rfl⟩

/-- Core bound: a subset of `[-k, M]` with `M = 2k + r`, `r ≤ 2`, whose restricted sumset
avoids `[-k, M]`, has at most `k + 2` elements. -/
lemma core (k M : ℤ) (hk : 0 ≤ k) (hM1 : 2 * k ≤ M) (hM2 : M ≤ 2 * k + 2)
    (S : Finset ℤ) (hS : S ⊆ Finset.Icc (-k) M)
    (hd : Disjoint S.restrictedSumset (Finset.Icc (-k) M)) :
    (S.card : ℤ) ≤ k + 2 := by
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; simp; omega
  set a := S.min' hne with ha_def
  have haS : a ∈ S := S.min'_mem hne
  have haI := Finset.mem_Icc.1 (hS haS)
  have hcard : (S.card : ℤ) = ((S.erase a).card : ℤ) + 1 := by
    rw [Finset.card_erase_of_mem haS]
    have : 0 < S.card := Finset.card_pos.2 hne
    omega
  -- facts about other elements
  have other : ∀ y ∈ S.erase a, a < y ∧ y ≤ M ∧ (a + y < -k ∨ M < a + y) := by
    intro y hy
    obtain ⟨hya, hyS⟩ := Finset.mem_erase.1 hy
    have hle : a ≤ y := S.min'_le y hyS
    have hlt : a < y := lt_of_le_of_ne hle (Ne.symm hya)
    have hyI := Finset.mem_Icc.1 (hS hyS)
    have hnot : a + y ∉ Finset.Icc (-k) M :=
      Finset.disjoint_left.1 hd (mem_rs haS hyS (ne_of_lt hlt))
    rw [Finset.mem_Icc] at hnot
    refine ⟨hlt, hyI.2, ?_⟩
    by_contra hc
    push Not at hc
    exact hnot ⟨hc.1, hc.2⟩
  rw [hcard]
  by_cases han : a < 0
  · have hsub : S.erase a ⊆ Finset.Ioo a (-k - a) := by
      intro y hy
      obtain ⟨h1, h2, h3⟩ := other y hy
      rw [Finset.mem_Ioo]
      omega
    have := Finset.card_le_card hsub
    rw [Int.card_Ioo] at this
    have : ((S.erase a).card : ℤ) ≤ ((-k - a - a - 1).toNat : ℤ) := by exact_mod_cast this
    omega
  · by_cases h2a : M ≤ 2 * a
    · have hsub : S.erase a ⊆ Finset.Ioc a M := by
        intro y hy
        obtain ⟨h1, h2, h3⟩ := other y hy
        rw [Finset.mem_Ioc]
        omega
      have := Finset.card_le_card hsub
      rw [Int.card_Ioc] at this
      have : ((S.erase a).card : ℤ) ≤ ((M - a).toNat : ℤ) := by exact_mod_cast this
      omega
    · have hsub : S.erase a ⊆ Finset.Ioc (M - a) M := by
        intro y hy
        obtain ⟨h1, h2, h3⟩ := other y hy
        rw [Finset.mem_Ioc]
        omega
      have := Finset.card_le_card hsub
      rw [Int.card_Ioc] at this
      have : ((S.erase a).card : ℤ) ≤ ((M - (M - a)).toNat : ℤ) := by exact_mod_cast this
      omega

lemma M_le (k M : ℤ) (hk : 0 ≤ k) (hM1 : 2 * k ≤ M) (hM2 : M ≤ 2 * k + 2) :
    (maxRestrictedSumAvoidingSubsetSize (Finset.Icc (-k) M) : ℤ) ≤ k + 2 := by
  have : maxRestrictedSumAvoidingSubsetSize (Finset.Icc (-k) M) ≤ (k + 2).toNat := by
    unfold maxRestrictedSumAvoidingSubsetSize
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    have := core k M hk hM1 hM2 S hS.1 hS.2
    omega
  omega

theorem green_2_upper_bound_erdos :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ A : Finset ℤ, A.card = n ∧
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card / 3 + C := by
  refine ⟨2, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
  set k : ℕ := (n - 1) / 3 with hk
  set r : ℕ := (n - 1) % 3 with hr
  have hn' : n = 3 * k + r + 1 := by omega
  have hr2 : r ≤ 2 := by omega
  refine ⟨Finset.Icc (-(k : ℤ)) (2 * k + r), ?_, ?_⟩
  · rw [Int.card_Icc]; omega
  · have hc : (Finset.Icc (-(k : ℤ)) (2 * k + r)).card = n := by
      rw [Int.card_Icc]; omega
    rw [hc]
    have h := M_le (k : ℤ) (2 * k + r) (by omega) (by omega) (by omega)
    have h' : (maxRestrictedSumAvoidingSubsetSize (Finset.Icc (-(k : ℤ)) (2 * k + r)) : ℝ)
        ≤ (k : ℝ) + 2 := by exact_mod_cast h
    have hnr : (n : ℝ) = 3 * k + r + 1 := by exact_mod_cast hn'
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [hnr]
    linarith

end Green2

#print axioms Green2.green_2_upper_bound_erdos
