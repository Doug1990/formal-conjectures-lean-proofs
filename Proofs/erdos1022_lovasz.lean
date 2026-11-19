import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Finset

def HasPropertyB {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∃ f : α → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

variable {V : Type*} [DecidableEq V]

def hypergraphInduce (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter (· ⊆ S)

end Finset

namespace Erdos1022

def SparseImpliesPropertyB (t : ℕ) (c : ℝ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ A ∈ F, t ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → ((F.hypergraphInduce X).card : ℝ) < c * (X.card : ℝ)) →
    F.HasPropertyB

namespace Lov

open Finset

def e (F : Finset (Finset ℕ)) (X : Finset ℕ) : ℕ := (F.filter (· ⊆ X)).card

def Sp (F : Finset (Finset ℕ)) : Prop := ∀ X : Finset ℕ, X.Nonempty → e F X < X.card

lemma Sp_mono {F G : Finset (Finset ℕ)} (h : G ⊆ F) (hF : Sp F) : Sp G := fun X hX =>
  lt_of_le_of_lt (card_le_card (filter_subset_filter _ h)) (hF X hX)

lemma tight {F : Finset (Finset ℕ)} (hF : Sp F) {A : Finset ℕ} (hA : A ∈ F) {v : ℕ}
    {X : Finset ℕ} (hX : X.Nonempty) (h : X.card ≤ e (insert (A.erase v) (F.erase A)) X) :
    ¬ A ⊆ X ∧ A.erase v ⊆ X ∧ X.card ≤ e F X + 1 := by
  have hFX := hF X hX
  by_cases hs : A.erase v ⊆ X
  · by_cases hA' : A ⊆ X
    · exfalso
      have hsub : (insert (A.erase v) (F.erase A)).filter (· ⊆ X) ⊆
          insert (A.erase v) ((F.filter (· ⊆ X)).erase A) := by
        intro B hB
        simp only [mem_filter, mem_insert, mem_erase] at hB ⊢
        tauto
      have h1 := card_le_card hsub
      have h2 := card_insert_le (A.erase v) ((F.filter (· ⊆ X)).erase A)
      have h3 : ((F.filter (· ⊆ X)).erase A).card + 1 = (F.filter (· ⊆ X)).card :=
        card_erase_add_one (mem_filter.2 ⟨hA, hA'⟩)
      unfold e at h hFX; omega
    · refine ⟨hA', hs, ?_⟩
      have hsub : (insert (A.erase v) (F.erase A)).filter (· ⊆ X) ⊆
          insert (A.erase v) (F.filter (· ⊆ X)) := by
        intro B hB
        simp only [mem_filter, mem_insert, mem_erase] at hB ⊢
        tauto
      have h1 := card_le_card hsub
      have h2 := card_insert_le (A.erase v) (F.filter (· ⊆ X))
      unfold e at h ⊢; omega
  · exfalso
    have hsub : (insert (A.erase v) (F.erase A)).filter (· ⊆ X) ⊆ F.filter (· ⊆ X) := by
      intro B hB
      simp only [mem_filter, mem_insert, mem_erase] at hB ⊢
      rcases hB with ⟨rfl | ⟨_, hB⟩, hBX⟩
      · exact absurd hBX hs
      · exact ⟨hB, hBX⟩
    have h1 := card_le_card hsub
    unfold e at h hFX; omega

lemma not_Sp {F : Finset (Finset ℕ)} (h : ¬ Sp F) : ∃ X : Finset ℕ, X.Nonempty ∧ X.card ≤ e F X := by
  by_contra h'
  apply h
  intro X hX
  by_contra h''
  exact h' ⟨X, hX, not_lt.1 h''⟩

lemma shrink {F : Finset (Finset ℕ)} (hF : Sp F) {A : Finset ℕ} (hA : A ∈ F) (h3 : 3 ≤ A.card) :
    ∃ v ∈ A, Sp (insert (A.erase v) (F.erase A)) := by
  obtain ⟨v, hv, w, hw, hvw⟩ : ∃ v ∈ A, ∃ w ∈ A, v ≠ w := one_lt_card.1 (by omega)
  by_cases hv' : Sp (insert (A.erase v) (F.erase A))
  · exact ⟨v, hv, hv'⟩
  by_cases hw' : Sp (insert (A.erase w) (F.erase A))
  · exact ⟨w, hw, hw'⟩
  exfalso
  obtain ⟨X, hX, hXc⟩ := not_Sp hv'
  obtain ⟨Y, hY, hYc⟩ := not_Sp hw'
  obtain ⟨hAX, hsX, hX1⟩ := tight hF hA hX hXc
  obtain ⟨hAY, hsY, hY1⟩ := tight hF hA hY hYc
  have hpos : 0 < ((A.erase v).erase w).card := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hvw.symm, hw⟩), card_erase_of_mem hv]; omega
  obtain ⟨u, hu⟩ := card_pos.1 hpos
  simp only [mem_erase] at hu
  have hI : (X ∩ Y).Nonempty :=
    ⟨u, mem_inter.2 ⟨hsX (mem_erase.2 ⟨hu.2.1, hu.2.2⟩), hsY (mem_erase.2 ⟨hu.1, hu.2.2⟩)⟩⟩
  have hU : (X ∪ Y).Nonempty := hX.mono subset_union_left
  have hAU : A ⊆ X ∪ Y := by
    intro a ha
    by_cases hav : a = v
    · subst hav
      exact mem_union_right _ (hsY (mem_erase.2 ⟨hvw, ha⟩))
    · exact mem_union_left _ (hsX (mem_erase.2 ⟨hav, ha⟩))
  have hPQ : F.filter (· ⊆ X) ∩ F.filter (· ⊆ Y) = F.filter (· ⊆ X ∩ Y) := by
    ext B
    simp only [mem_inter, mem_filter, subset_inter_iff]
    tauto
  have hsub : insert A (F.filter (· ⊆ X) ∪ F.filter (· ⊆ Y)) ⊆ F.filter (· ⊆ X ∪ Y) := by
    intro B hB
    simp only [mem_insert, mem_union, mem_filter] at hB ⊢
    rcases hB with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hA, hAU⟩
    · exact ⟨h1, h2.trans subset_union_left⟩
    · exact ⟨h1, h2.trans subset_union_right⟩
  have hAn : A ∉ F.filter (· ⊆ X) ∪ F.filter (· ⊆ Y) := by
    rw [mem_union, not_or]
    exact ⟨fun h => hAX (mem_filter.1 h).2, fun h => hAY (mem_filter.1 h).2⟩
  have c1 := card_le_card hsub
  rw [card_insert_of_notMem hAn] at c1
  have c2 := card_union_add_card_inter (F.filter (· ⊆ X)) (F.filter (· ⊆ Y))
  rw [hPQ] at c2
  have c3 := card_union_add_card_inter X Y
  have c4 := hF (X ∪ Y) hU
  have c5 := hF (X ∩ Y) hI
  unfold e at hX1 hY1 c4 c5
  omega

lemma leaf {F : Finset (Finset ℕ)} (hne : F.Nonempty) (h2 : ∀ A ∈ F, A.card = 2) (hF : Sp F) :
    ∃ v A, A ∈ F ∧ v ∈ A ∧ ∀ B ∈ F, v ∈ B → B = A := by
  by_contra hcon
  have hdeg : ∀ v ∈ F.biUnion id, 2 ≤ (F.filter (v ∈ ·)).card := by
    intro v hv
    obtain ⟨A, hA, hvA⟩ := mem_biUnion.1 hv
    have : ∃ B ∈ F, v ∈ B ∧ B ≠ A := by
      by_contra hnB
      apply hcon
      refine ⟨v, A, hA, hvA, fun B hB hvB => ?_⟩
      by_contra hBA
      exact hnB ⟨B, hB, hvB, hBA⟩
    obtain ⟨B, hB, hvB, hBA⟩ := this
    have : 1 < (F.filter (v ∈ ·)).card :=
      one_lt_card.2 ⟨A, mem_filter.2 ⟨hA, hvA⟩, B, mem_filter.2 ⟨hB, hvB⟩, fun h => hBA h.symm⟩
    omega
  obtain ⟨A0, hA0⟩ := hne
  have hVne : (F.biUnion id).Nonempty := by
    have : 0 < A0.card := by rw [h2 A0 hA0]; omega
    obtain ⟨x, hx⟩ := card_pos.1 this
    exact ⟨x, mem_biUnion.2 ⟨A0, hA0, hx⟩⟩
  have hall : F.filter (· ⊆ F.biUnion id) = F :=
    filter_true_of_mem (fun A hA => subset_biUnion_of_mem id hA)
  have hlt := hF _ hVne
  unfold e at hlt
  rw [hall] at hlt
  have hdc : ∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card =
      ∑ A ∈ F, ((F.biUnion id).filter (· ∈ A)).card := by
    simp only [card_filter]
    exact sum_comm
  have hlo : ∑ v ∈ F.biUnion id, 2 ≤ ∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card :=
    sum_le_sum hdeg
  have hhi : ∑ A ∈ F, ((F.biUnion id).filter (· ∈ A)).card ≤ ∑ A ∈ F, 2 := by
    apply sum_le_sum
    intro A hA
    rw [← h2 A hA]
    exact card_le_card (fun x hx => (mem_filter.1 hx).2)
  simp only [sum_const, smul_eq_mul] at hlo hhi
  omega

theorem main : ∀ n, ∀ F : Finset (Finset ℕ), ∑ B ∈ F, B.card = n →
    (∀ A ∈ F, 2 ≤ A.card) → Sp F → F.HasPropertyB := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hn h2 hF
  by_cases hbig : ∃ A ∈ F, 3 ≤ A.card
  · obtain ⟨A, hA, h3⟩ := hbig
    obtain ⟨v, hv, hsp⟩ := shrink hF hA h3
    have hlt : ∑ B ∈ insert (A.erase v) (F.erase A), B.card < n := by
      have hs1 : ∑ B ∈ insert (A.erase v) (F.erase A), B.card ≤
          (A.erase v).card + ∑ B ∈ F.erase A, B.card := by
        by_cases hm : A.erase v ∈ F.erase A
        · rw [insert_eq_of_mem hm]; omega
        · rw [sum_insert hm]
      have := sum_erase_add F Finset.card hA
      have := card_erase_of_mem hv
      omega
    obtain ⟨f, hf⟩ := ih _ hlt (insert (A.erase v) (F.erase A)) rfl (by
      intro B hB
      rcases mem_insert.1 hB with rfl | hB
      · rw [card_erase_of_mem hv]; omega
      · exact h2 B (mem_of_mem_erase hB)) hsp
    refine ⟨f, fun B hB => ?_⟩
    by_cases hBA : B = A
    · subst hBA
      obtain ⟨x, hx, y, hy, hxy⟩ := hf _ (mem_insert_self _ _)
      exact ⟨x, mem_of_mem_erase hx, y, mem_of_mem_erase hy, hxy⟩
    · exact hf B (mem_insert_of_mem (mem_erase.2 ⟨hBA, hB⟩))
  · have h2' : ∀ A ∈ F, A.card = 2 := by
      intro A hA
      have := h2 A hA
      have : ¬ 3 ≤ A.card := fun h => hbig ⟨A, hA, h⟩
      omega
    by_cases hFe : F = ∅
    · subst hFe
      exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, A, hA, hvA, huniq⟩ := leaf (nonempty_iff_ne_empty.2 hFe) h2' hF
    have hlt : ∑ B ∈ F.erase A, B.card < n := by
      have := sum_erase_add F Finset.card hA
      have := h2 A hA
      omega
    obtain ⟨f, hf⟩ := ih _ hlt (F.erase A) rfl (fun B hB => h2 B (mem_of_mem_erase hB))
      (Sp_mono (erase_subset _ _) hF)
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ A, w ≠ v := by
      have : 1 < A.card := by have := h2 A hA; omega
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 this
      by_cases hav : a = v
      · exact ⟨b, hb, fun h => hab (hav.trans h.symm)⟩
      · exact ⟨a, ha, hav⟩
    refine ⟨Function.update f v (if f w = 0 then 1 else 0), fun B hB => ?_⟩
    by_cases hBA : B = A
    · subst hBA
      refine ⟨v, hvA, w, hw, ?_⟩
      rw [Function.update_self, Function.update_of_ne hwv]
      split_ifs with h
      · rw [h]; decide
      · exact fun e => h e.symm
    · obtain ⟨x, hx, y, hy, hxy⟩ := hf B (mem_erase.2 ⟨hBA, hB⟩)
      have hvB : v ∉ B := fun h => hBA (huniq B hB h)
      refine ⟨x, hx, y, hy, ?_⟩
      rwa [Function.update_of_ne (fun h : x = v => hvB (h ▸ hx)),
        Function.update_of_ne (fun h : y = v => hvB (h ▸ hy))]

def T : Finset (Finset ℕ) := {{0, 1}, {1, 2}, {0, 2}}

def g (B : Finset ℕ) : ℕ := if B = {0, 1} then 0 else if B = {1, 2} then 1 else 2

lemma T_e (X : Finset ℕ) : (T.filter (· ⊆ X)).card ≤ X.card := by
  apply card_le_card_of_injOn g
  · intro B hB
    have hB' := mem_filter.1 hB
    have hBT := hB'.1
    simp only [T, mem_insert, mem_singleton] at hBT
    rcases hBT with rfl | rfl | rfl
    · have : g {0, 1} = 0 := by decide
      rw [this]; exact hB'.2 (by simp)
    · have : g {1, 2} = 1 := by decide
      rw [this]; exact hB'.2 (by simp)
    · have : g {0, 2} = 2 := by decide
      rw [this]; exact hB'.2 (by simp)
  · intro B1 hB1 B2 hB2 h
    have h1 := (mem_filter.1 hB1).1
    have h2 := (mem_filter.1 hB2).1
    simp only [T, mem_insert, mem_singleton] at h1 h2
    revert h
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> decide

lemma T_noB : ¬ T.HasPropertyB := by
  rintro ⟨f, hf⟩
  have key : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by decide
  have hmono : ∀ a b : ℕ, f a = f b → ∀ x ∈ ({a, b} : Finset ℕ), ∀ y ∈ ({a, b} : Finset ℕ),
      f x = f y := by
    intro a b hab
    simp only [mem_insert, mem_singleton]
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have hT : ∀ A ∈ T, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y := hf
  by_cases h01 : f 0 = f 1
  · obtain ⟨x, hx, y, hy, hxy⟩ := hT {0, 1} (by simp [T])
    exact hxy (hmono 0 1 h01 x hx y hy)
  by_cases h12 : f 1 = f 2
  · obtain ⟨x, hx, y, hy, hxy⟩ := hT {1, 2} (by simp [T])
    exact hxy (hmono 1 2 h12 x hx y hy)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hT {0, 2} (by simp [T])
    exact hxy (hmono 0 2 (key _ _ _ h01 h12) x hx y hy)

end Lov

open Finset in
theorem erdos_1022.variants.lovasz :
    IsGreatest {c : ℝ | SparseImpliesPropertyB 2 c} 1 := by
  refine ⟨?_, ?_⟩
  · intro F h2 hc
    refine Lov.main _ F rfl h2 (fun X hX => ?_)
    have := hc X hX
    rw [one_mul] at this
    exact_mod_cast this
  · intro c hc
    by_contra hle
    have hlt : 1 < c := not_le.1 hle
    apply Lov.T_noB
    apply hc Lov.T
    · intro A hA
      simp only [Lov.T, mem_insert, mem_singleton] at hA
      rcases hA with rfl | rfl | rfl <;> decide
    · intro X hX
      have h1 : ((Lov.T.hypergraphInduce X).card : ℝ) ≤ (X.card : ℝ) := by
        exact_mod_cast Lov.T_e X
      have h2 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
      have h3 := mul_lt_mul_of_pos_right hlt h2
      linarith

end Erdos1022

#print axioms Erdos1022.erdos_1022.variants.lovasz
