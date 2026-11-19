import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/-- Local copy of FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean. -/
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Erdos787

noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

theorem disjoint_restrictedSumset_iff {G : Type*} [Add G] [DecidableEq G] (A B : Finset G) :
    Disjoint B.restrictedSumset A ↔ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A := by
  unfold Finset.restrictedSumset
  rw [Finset.disjoint_left]
  constructor
  · intro h b₁ hb₁ b₂ hb₂ hne hmem
    have hmem' : b₁ + b₂ ∈ Finset.image (fun p : G × G => p.1 + p.2) B.offDiag :=
      Finset.mem_image.2 ⟨(b₁, b₂), Finset.mem_offDiag.2 ⟨hb₁, hb₂, hne⟩, rfl⟩
    exact h hmem' hmem
  · intro h x hx hxA
    obtain ⟨⟨b₁, b₂⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hb₁, hb₂, hne⟩ := Finset.mem_offDiag.1 hp
    exact h b₁ hb₁ b₂ hb₂ hne hxA

theorem le_g {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) : m ≤ g ℝ n := by
  refine le_csSup (bddAbove_def.2 ⟨n, fun m' hm' => ?_⟩) h
  have hm'' : ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, m' ≤ B.card ∧ Disjoint B.restrictedSumset A := hm'
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm'' A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans_eq hA)

namespace KL

/-- Greedy choice among the positive elements, picking each new element as the largest
admissible one below the previous ones. Potential: `S = ∑_{c ∈ C} #{a ∈ A : c ≤ a}`. -/
lemma grow (A : Finset ℝ) : ∀ k : ℕ, 3 ^ k ≤ (A.filter (fun x => 0 < x)).card →
    ∃ C : Finset ℝ, C ⊆ A.filter (fun x => 0 < x) ∧ C.card = k ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → x + y ∉ A) ∧
      2 * ∑ c ∈ C, (A.filter (fun x => c ≤ x)).card + 1 ≤ 3 ^ k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    intro hk
    have hk' : 3 ^ k ≤ (A.filter (fun x => 0 < x)).card :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)) hk
    obtain ⟨C, hCP, hCk, hCs, hS⟩ := ih hk'
    set P := A.filter (fun x => 0 < x) with hP
    set S := ∑ c ∈ C, (A.filter (fun x => c ≤ x)).card with hSdef
    set B0 : Finset ℝ := C.biUnion (fun c => A.filter (fun x => c ≤ x) ∪
        (A.filter (fun x => c ≤ x)).image (fun x => x - c)) with hB0def
    have hB0 : B0.card ≤ 2 * S := by
      calc B0.card ≤ ∑ c ∈ C, (A.filter (fun x => c ≤ x) ∪
          (A.filter (fun x => c ≤ x)).image (fun x => x - c)).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ C, 2 * (A.filter (fun x => c ≤ x)).card := by
          apply Finset.sum_le_sum
          intro c _
          refine (Finset.card_union_le _ _).trans ?_
          have := Finset.card_image_le (s := A.filter (fun x => c ≤ x)) (f := fun x => x - c)
          omega
        _ = 2 * S := by rw [← Finset.mul_sum]
    have memB0 : ∀ a ∈ P, (∃ c ∈ C, c ≤ a ∨ a + c ∈ A) → a ∈ B0 := by
      intro a ha h
      obtain ⟨c, hc, h⟩ := h
      have ha0 : 0 < a := (Finset.mem_filter.1 ha).2
      have haA : a ∈ A := (Finset.mem_filter.1 ha).1
      refine Finset.mem_biUnion.2 ⟨c, hc, ?_⟩
      rcases h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨haA, h⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_image.2 ⟨a + c, Finset.mem_filter.2 ⟨h, by linarith⟩, by ring⟩)
    set R := P.filter (fun s => (∀ c ∈ C, s < c) ∧ ∀ c ∈ C, s + c ∉ A) with hRdef
    have hR : R.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hsub : P ⊆ B0 := by
        intro a ha
        apply memB0 a ha
        by_contra hno
        have haR : a ∈ R := Finset.mem_filter.2 ⟨ha,
          fun c hc => not_le.1 (fun h' => hno ⟨c, hc, Or.inl h'⟩),
          fun c hc h' => hno ⟨c, hc, Or.inr h'⟩⟩
        rw [hne] at haR
        simp at haR
      have := Finset.card_le_card hsub
      have : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      omega
    obtain ⟨s, hsR, hmax⟩ : ∃ s ∈ R, ∀ a ∈ R, a ≤ s :=
      ⟨R.max' hR, R.max'_mem hR, fun a ha => R.le_max' a ha⟩
    have hsR' := Finset.mem_filter.1 hsR
    have hsP : s ∈ P := hsR'.1
    have hs0 : 0 < s := (Finset.mem_filter.1 hsP).2
    have hNs : (A.filter (fun x => s ≤ x)) ⊆ insert s B0 := by
      intro a ha
      obtain ⟨haA, hsa⟩ := Finset.mem_filter.1 ha
      rcases eq_or_lt_of_le hsa with h | h
      · rw [← h]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have haP : a ∈ P := Finset.mem_filter.2 ⟨haA, by linarith⟩
        apply memB0 a haP
        by_contra hno
        have haR : a ∈ R := Finset.mem_filter.2 ⟨haP,
          fun c hc => not_le.1 (fun h' => hno ⟨c, hc, Or.inl h'⟩),
          fun c hc h' => hno ⟨c, hc, Or.inr h'⟩⟩
        have := hmax a haR
        linarith
    have hNs' := (Finset.card_le_card hNs).trans (Finset.card_insert_le _ _)
    have hsC : s ∉ C := fun h => lt_irrefl s (hsR'.2.1 s h)
    refine ⟨insert s C, Finset.insert_subset hsP hCP, by
      rw [Finset.card_insert_of_notMem hsC, hCk], ?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact absurd (hx.trans hy.symm) hxy
      · rw [hx]; exact hsR'.2.2 y hy
      · rw [hy, add_comm]; exact hsR'.2.2 x hx
      · exact hCs x hx y hy hxy
    · rw [Finset.sum_insert hsC]
      have : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      omega

lemma exists_B (A : Finset ℝ) (k : ℕ) (hn : 2 * 3 ^ k + 1 ≤ A.card) :
    ∃ B ⊆ A, k ≤ B.card ∧ Disjoint B.restrictedSumset A := by
  have hcover : A ⊆ insert 0 (A.filter (fun x => 0 < x) ∪ A.filter (fun x => x < 0)) := by
    intro a ha
    rcases lt_trichotomy a 0 with h | h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha, h⟩))
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha, h⟩))
  have hc1 := (Finset.card_le_card hcover).trans (Finset.card_insert_le _ _)
  have hc2 := Finset.card_union_le (A.filter (fun x => 0 < x)) (A.filter (fun x => x < 0))
  have hneg : (A.filter (fun x => x < 0)).card ≤
      ((A.image (fun x => -x)).filter (fun x => 0 < x)).card := by
    rw [← Finset.card_image_of_injective (A.filter (fun x => x < 0)) neg_injective]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨haA, ha0⟩ := Finset.mem_filter.1 ha
    exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨a, haA, rfl⟩, by simpa using ha0⟩
  by_cases hp : 3 ^ k ≤ (A.filter (fun x => 0 < x)).card
  · obtain ⟨C, hCP, hCk, hCs, -⟩ := grow A k hp
    refine ⟨C, hCP.trans (Finset.filter_subset _ _), hCk.ge, ?_⟩
    rw [disjoint_restrictedSumset_iff]
    exact hCs
  · have hq : 3 ^ k ≤ ((A.image (fun x => -x)).filter (fun x => 0 < x)).card := by omega
    obtain ⟨C, hCP, hCk, hCs, -⟩ := grow (A.image (fun x => -x)) k hq
    refine ⟨C.image (fun x => -x), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hx' := (Finset.mem_filter.1 (hCP hx)).1
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx'
      simpa using ha
    · rw [Finset.card_image_of_injective C neg_injective, hCk]
    · rw [disjoint_restrictedSumset_iff]
      intro b₁ hb₁ b₂ hb₂ hne hmem
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb₂
      have hxy : x ≠ y := fun h => hne (by rw [h])
      apply hCs x hx y hy hxy
      exact Finset.mem_image.2 ⟨-x + -y, hmem, by ring⟩

end KL

theorem erdos_787.variants.klarner :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (g ℝ n : ℝ) := by
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨1 / (4 * Real.log 3), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 729] with n hn
  set L := Nat.log 9 n with hL
  have hL3 : 3 ≤ L := Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num) hn)
  have hpow : 9 ^ L ≤ n := Nat.pow_log_le_self 9 (by omega)
  have hlt : n < 9 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk : 2 * 3 ^ (L - 1) + 1 ≤ n := by
    have e : 9 ^ L = 9 * 9 ^ (L - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 3 ^ (L - 1) ≤ 9 ^ (L - 1) := Nat.pow_le_pow_left (by norm_num) _
    omega
  have hg : L - 1 ≤ g ℝ n := le_g (fun A hA => KL.exists_B A (L - 1) (by rw [hA]; exact hk))
  have hgR : ((L - 1 : ℕ) : ℝ) ≤ (g ℝ n : ℝ) := by exact_mod_cast hg
  have hlog : Real.log n < (L + 1) * (2 * Real.log 3) := by
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have : (n:ℝ) < (9:ℝ) ^ (L + 1) := by exact_mod_cast hlt
    calc Real.log n < Real.log ((9:ℝ) ^ (L + 1)) := Real.log_lt_log hn0 this
      _ = (L + 1) * (2 * Real.log 3) := by
        rw [Real.log_pow, show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL1 : ((L - 1 : ℕ) : ℝ) = (L:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hL3' : (3:ℝ) ≤ L := by exact_mod_cast hL3
  rw [hL1] at hgR
  have key : 1 / (4 * Real.log 3) * Real.log n ≤ ((L:ℝ) + 1) / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  linarith

end Erdos787

#print axioms Erdos787.erdos_787.variants.klarner
