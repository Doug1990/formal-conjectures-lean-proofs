import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common

namespace ReconstructionConjecture

variable {V W : Type*}

def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

namespace Lov
open Finset Classical

variable {V : Type*} [Fintype V]

noncomputable def EF (K : SimpleGraph V) : Finset (Sym2 V) := univ.filter (· ∈ K.edgeSet)

noncomputable def N (K : SimpleGraph V) (F : Finset (Sym2 V)) : ℕ :=
  (univ.filter fun σ : Equiv.Perm V => ∀ f ∈ F, Sym2.map σ f ∈ K.edgeSet).card

lemma mem_EF {K : SimpleGraph V} {e : Sym2 V} : e ∈ EF K ↔ e ∈ K.edgeSet := by
  simp [EF]

omit [Fintype V] in
lemma map_trans {K K' : SimpleGraph V} (τ : K ≃g K') (σ : Equiv.Perm V) (f : Sym2 V) :
    Sym2.map (σ.trans τ.toEquiv) f ∈ K'.edgeSet ↔ Sym2.map σ f ∈ K.edgeSet := by
  rw [← τ.map_mem_edgeSet_iff, Sym2.map_map]
  rfl

lemma N_iso {K K' : SimpleGraph V} (τ : K ≃g K') (F : Finset (Sym2 V)) : N K F = N K' F := by
  unfold N
  refine Finset.card_nbij' (fun σ => σ.trans τ.toEquiv) (fun σ => σ.trans τ.symm.toEquiv)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    intro f hf
    exact (map_trans τ σ f).2 (hσ f hf)
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    intro f hf
    exact (map_trans τ.symm σ f).2 (hσ f hf)
  · intro σ _
    ext x
    simp
  · intro σ _
    ext x
    simp

lemma kelly (K : SimpleGraph V) (F : Finset (Sym2 V)) :
    ∑ e ∈ EF K, N (K.deleteEdges {e}) F = ((EF K).card - F.card) * N K F := by
  simp only [N, card_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ f ∈ F, Sym2.map σ f ∈ K.edgeSet
  · rw [if_pos h, mul_one]
    have hsub : F.image (Sym2.map σ) ⊆ EF K := by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.1 he
      exact mem_EF.2 (h f hf)
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    rw [card_image_of_injective _ (Sym2.map.injective σ.injective)] at h1
    have hD : ∀ e ∈ EF K, ((∀ f ∈ F, Sym2.map σ f ∈ (K.deleteEdges {e}).edgeSet) ↔
        e ∈ EF K \ F.image (Sym2.map σ)) := by
      intro e he
      simp only [mem_sdiff, mem_image, SimpleGraph.edgeSet_deleteEdges,
        Set.mem_sdiff, Set.mem_singleton_iff, not_exists, not_and]
      constructor
      · intro h2
        exact ⟨he, fun f hf => (h2 f hf).2⟩
      · rintro ⟨-, h2⟩
        exact fun f hf => ⟨h f hf, h2 f hf⟩
    calc _ = ∑ x ∈ EF K, (if x ∈ EF K \ F.image (Sym2.map σ) then 1 else 0) :=
          Finset.sum_congr rfl fun x hx => by
            by_cases hp : x ∈ EF K \ F.image (Sym2.map σ)
            · rw [if_pos hp, if_pos ((hD x hx).2 hp)]
            · rw [if_neg hp, if_neg (fun h' => hp ((hD x hx).1 h'))]
      _ = (EF K \ F.image (Sym2.map σ)).card := by
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 Finset.sdiff_subset,
            ← Finset.card_eq_sum_ones]
      _ = _ := by omega
  · rw [if_neg h, mul_zero]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro h2
    apply h
    intro f hf
    have := h2 f hf
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.1

lemma sum_eq (K : SimpleGraph V) (φ : Sym2 V → ℕ) :
    ∑ e ∈ EF K, φ e = ∑ x : K.edgeSet, φ x.1 :=
  Finset.sum_subtype _ (fun _ => mem_EF) φ

lemma card_EF_eq {G H : SimpleGraph V} (h : EdgeHypomorphic G H) :
    (EF G).card = (EF H).card := by
  obtain ⟨σ', -⟩ := h
  rw [card_eq_sum_ones, card_eq_sum_ones, sum_eq, sum_eq]
  exact Fintype.sum_equiv σ' _ _ (fun _ => rfl)

lemma N_eq {G H : SimpleGraph V} (h : EdgeHypomorphic G H) (F : Finset (Sym2 V))
    (hF : F.card < (EF G).card) : N G F = N H F := by
  have hc := card_EF_eq h
  obtain ⟨σ', hσ'⟩ := h
  have key : ((EF G).card - F.card) * N G F = ((EF G).card - F.card) * N H F := by
    calc ((EF G).card - F.card) * N G F = ∑ e ∈ EF G, N (G.deleteEdges {e}) F := (kelly G F).symm
      _ = ∑ x : G.edgeSet, N (G.deleteEdges {x.1}) F := sum_eq G _
      _ = ∑ x : G.edgeSet, N (H.deleteEdges {(σ' x).1}) F :=
          Finset.sum_congr rfl fun x _ => N_iso (hσ' x).some F
      _ = ∑ y : H.edgeSet, N (H.deleteEdges {y.1}) F := Fintype.sum_equiv σ' _ _ (fun _ => rfl)
      _ = ∑ e ∈ EF H, N (H.deleteEdges {e}) F :=
          (sum_eq H (fun e => N (H.deleteEdges {e}) F)).symm
      _ = ((EF H).card - F.card) * N H F := kelly H F
      _ = ((EF G).card - F.card) * N H F := by rw [hc]
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- Inclusion–exclusion with a fixed base set `A`. -/
lemma incl_excl' (K : SimpleGraph V) (A S : Finset (Sym2 V)) :
    ∑ B ∈ S.powerset, (-1 : ℤ) ^ B.card * (N K (A ∪ B) : ℤ) =
      ((univ.filter fun σ : Equiv.Perm V => (∀ f ∈ A, Sym2.map σ f ∈ K.edgeSet) ∧
        ∀ f ∈ S, Sym2.map σ f ∉ K.edgeSet).card : ℤ) := by
  simp only [N, card_filter]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hA : ∀ f ∈ A, Sym2.map σ f ∈ K.edgeSet
  · calc _ = ∑ B ∈ S.powerset,
          (if B ⊆ S.filter (fun f => Sym2.map σ f ∈ K.edgeSet) then (-1 : ℤ) ^ B.card else 0) := by
          refine Finset.sum_congr rfl fun B hB => ?_
          by_cases hB2 : B ⊆ S.filter (fun f => Sym2.map σ f ∈ K.edgeSet)
          · rw [if_pos hB2, if_pos, mul_one]
            intro f hf
            rcases mem_union.1 hf with hf | hf
            · exact hA f hf
            · exact (mem_filter.1 (hB2 hf)).2
          · rw [if_neg hB2, if_neg, mul_zero]
            intro h
            apply hB2
            intro f hf
            exact mem_filter.2 ⟨mem_powerset.1 hB hf, h f (mem_union_right _ hf)⟩
      _ = ∑ B ∈ (S.filter (fun f => Sym2.map σ f ∈ K.edgeSet)).powerset, (-1 : ℤ) ^ B.card := by
          rw [← Finset.sum_filter]
          congr 1
          ext B
          simp only [mem_filter, mem_powerset]
          constructor
          · rintro ⟨-, h⟩
            exact h
          · intro h
            exact ⟨h.trans (filter_subset _ _), h⟩
      _ = _ := by
          rw [Finset.sum_powerset_neg_one_pow_card]
          by_cases h : ∀ f ∈ S, Sym2.map σ f ∉ K.edgeSet
          · rw [if_pos (Finset.filter_eq_empty_iff.2 h), if_pos ⟨hA, h⟩]
          · rw [if_neg (fun h2 => h (Finset.filter_eq_empty_iff.1 h2)), if_neg (fun h2 => h h2.2)]
  · rw [if_neg (fun h2 => hA h2.1)]
    apply Finset.sum_eq_zero
    intro B _
    rw [if_neg, mul_zero]
    intro h
    exact hA fun f hf => h f (mem_union_left _ hf)

lemma pos_N (G : SimpleGraph V) : 0 < N G (EF G) := by
  apply Finset.card_pos.2
  refine ⟨1, ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  intro f hf
  rw [Equiv.Perm.coe_one, Sym2.map_id]
  exact mem_EF.1 hf

lemma iso_of {G H : SimpleGraph V} (hc : (EF G).card = (EF H).card) (σ : Equiv.Perm V)
    (hσ : ∀ f ∈ EF G, Sym2.map σ f ∈ H.edgeSet) : Nonempty (G ≃g H) := by
  have himg : (EF G).image (Sym2.map σ) = EF H := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.1 he
      exact mem_EF.2 (hσ f hf)
    · rw [card_image_of_injective _ (Sym2.map.injective σ.injective), ← hc]
  refine ⟨⟨σ, fun {a b} => ?_⟩⟩
  constructor
  · intro hab
    have hmem : s(σ a, σ b) ∈ EF H := mem_EF.2 hab
    rw [← himg, mem_image] at hmem
    obtain ⟨f, hf, hfe⟩ := hmem
    have hf2 : f = s(a, b) := Sym2.map.injective σ.injective (by rw [hfe]; rfl)
    subst hf2
    exact mem_EF.1 hf
  · intro hab
    exact hσ s(a, b) (mem_EF.2 hab)

lemma M_pos {G H : SimpleGraph V} (h : EdgeHypomorphic G H) (hni : ¬ Nonempty (G ≃g H))
    (A : Finset (Sym2 V)) (hA : A ⊆ EF G) (hpar : (EF G \ A).card % 2 = 0) :
    ∃ σ : Equiv.Perm V, (∀ f ∈ A, Sym2.map σ f ∈ G.edgeSet) ∧
      ∀ f ∈ EF G \ A, Sym2.map σ f ∉ G.edgeSet := by
  have hNH : N H (EF G) = 0 := by
    rw [N, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    exact hni (iso_of (card_EF_eq h) σ hσ)
  have d := incl_excl' G A (EF G \ A)
  have d2 := incl_excl' H A (EF G \ A)
  have hsum : ∑ B ∈ (EF G \ A).powerset,
      (-1 : ℤ) ^ B.card * ((N G (A ∪ B) : ℤ) - N H (A ∪ B)) = (N G (EF G) : ℤ) := by
    rw [Finset.sum_eq_single (EF G \ A)]
    · rw [Finset.union_sdiff_of_subset hA, hNH, Even.neg_one_pow (Nat.even_iff.2 hpar)]
      simp
    · intro B hB hne
      have hB' := mem_powerset.1 hB
      have hlt : (A ∪ B).card < (EF G).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.union_subset hA (hB'.trans sdiff_subset), fun heq => hne ?_⟩
        apply Finset.Subset.antisymm hB'
        intro x hx
        have hxS := mem_sdiff.1 hx
        have hx2 : x ∈ A ∪ B := by rw [heq]; exact hxS.1
        rcases mem_union.1 hx2 with h1 | h1
        · exact absurd h1 hxS.2
        · exact h1
      rw [N_eq h _ hlt, sub_self, mul_zero]
    · intro h'
      exact absurd (mem_powerset_self _) h'
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  rw [d, d2] at hsum
  have hpos := pos_N G
  have hc : 0 < (univ.filter fun σ : Equiv.Perm V => (∀ f ∈ A, Sym2.map σ f ∈ G.edgeSet) ∧
        ∀ f ∈ EF G \ A, Sym2.map σ f ∉ G.edgeSet).card := by
    have h0 : (0 : ℤ) ≤ ((univ.filter fun σ : Equiv.Perm V =>
        (∀ f ∈ A, Sym2.map σ f ∈ H.edgeSet) ∧
        ∀ f ∈ EF G \ A, Sym2.map σ f ∉ H.edgeSet).card : ℤ) := Nat.cast_nonneg _
    have h1 : (0 : ℤ) < (N G (EF G) : ℤ) := by exact_mod_cast hpos
    have h2 : (0 : ℤ) < ((univ.filter fun σ : Equiv.Perm V =>
        (∀ f ∈ A, Sym2.map σ f ∈ G.edgeSet) ∧
        ∀ f ∈ EF G \ A, Sym2.map σ f ∉ G.edgeSet).card : ℤ) := by linarith
    exact_mod_cast h2
  obtain ⟨σ, hσ⟩ := Finset.card_pos.1 hc
  exact ⟨σ, (mem_filter.1 hσ).2⟩

end Lov

open Finset Lov in
theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  by_contra hni
  have hG : G.edgeSet.ncard = (EF G).card := by
    have : G.edgeSet = ↑(EF G) := by
      ext e
      simp [mem_EF]
    rw [this, Set.ncard_coe_finset]
  rw [hG] at hE
  have hfac := Nat.factorial_pos (Fintype.card V)
  have hm : 0 < (EF G).card := by
    rcases Nat.eq_zero_or_pos (EF G).card with h0 | h0
    · rw [h0, Nat.zero_sub, pow_zero] at hE
      omega
    · exact h0
  obtain ⟨e0, he0⟩ := Finset.card_pos.1 hm
  have hchoose : ∀ A ∈ (EF G).powerset.filter (fun A => (EF G \ A).card % 2 = 0),
      ∃ σ : Equiv.Perm V, (∀ f ∈ A, Sym2.map σ f ∈ G.edgeSet) ∧
        ∀ f ∈ EF G \ A, Sym2.map σ f ∉ G.edgeSet := fun A hA =>
    M_pos h hni A (mem_powerset.1 (mem_filter.1 hA).1) (mem_filter.1 hA).2
  choose! g hg using hchoose
  have hinj : Set.InjOn g ↑((EF G).powerset.filter (fun A => (EF G \ A).card % 2 = 0)) := by
    intro A hA A' hA' heq
    have h1 := hg A hA
    have h2 := hg A' hA'
    rw [heq] at h1
    have sA := mem_powerset.1 (mem_filter.1 hA).1
    have sA' := mem_powerset.1 (mem_filter.1 hA').1
    ext x
    constructor
    · intro hx
      by_contra hx'
      exact (h2.2 x (mem_sdiff.2 ⟨sA hx, hx'⟩)) (h1.1 x hx)
    · intro hx
      by_contra hx'
      exact (h1.2 x (mem_sdiff.2 ⟨sA' hx, hx'⟩)) (h2.1 x hx)
  have hP_le : ((EF G).powerset.filter (fun A => (EF G \ A).card % 2 = 0)).card ≤
      (Fintype.card V).factorial := by
    have := Finset.card_le_card_of_injOn g (t := (univ : Finset (Equiv.Perm V)))
      (by intro a _; exact mem_univ _) hinj
    rwa [Finset.card_univ, Fintype.card_perm] at this
  have hP_ge : 2 ^ ((EF G).card - 1) ≤
      ((EF G).powerset.filter (fun A => (EF G \ A).card % 2 = 0)).card := by
    have hcard : ((EF G).erase e0).powerset.card = 2 ^ ((EF G).card - 1) := by
      rw [card_powerset, card_erase_of_mem he0]
    rw [← hcard]
    apply Finset.card_le_card_of_injOn
      (fun B => if (EF G \ B).card % 2 = 0 then B else insert e0 B)
    · intro B hB
      have hB' := mem_powerset.1 hB
      have hBS : B ⊆ EF G := hB'.trans (erase_subset _ _)
      have he0B : e0 ∉ B := fun h => (mem_erase.1 (hB' h)).1 rfl
      have c1 := card_sdiff_add_card_eq_card hBS
      dsimp only
      split_ifs with hpar
      · exact mem_filter.2 ⟨mem_powerset.2 hBS, hpar⟩
      · have hiS : insert e0 B ⊆ EF G := insert_subset he0 hBS
        have c2 := card_sdiff_add_card_eq_card hiS
        rw [card_insert_of_notMem he0B] at c2
        exact mem_filter.2 ⟨mem_powerset.2 hiS, by omega⟩
    · intro B hB B' hB' heq
      have he0B : e0 ∉ B := fun h => (mem_erase.1 (mem_powerset.1 hB h)).1 rfl
      have he0B' : e0 ∉ B' := fun h => (mem_erase.1 (mem_powerset.1 hB' h)).1 rfl
      dsimp only at heq
      split_ifs at heq with h1 h2 h2
      · exact heq
      · exfalso
        apply he0B
        rw [heq]
        exact mem_insert_self e0 B'
      · exfalso
        apply he0B'
        rw [← heq]
        exact mem_insert_self e0 B
      · rw [← erase_insert he0B, heq, erase_insert he0B']
  omega

end ReconstructionConjecture

#print axioms ReconstructionConjecture.edge_reconstruction_conjecture.variants.mueller
