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

lemma incl_excl (K : SimpleGraph V) (S : Finset (Sym2 V)) :
    ∑ F ∈ S.powerset, (-1 : ℤ) ^ F.card * (N K F : ℤ) =
      ((univ.filter fun σ : Equiv.Perm V => ∀ f ∈ S, Sym2.map σ f ∉ K.edgeSet).card : ℤ) := by
  simp only [N, card_filter]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have : S.powerset.filter (fun F => ∀ f ∈ F, Sym2.map σ f ∈ K.edgeSet)
      = (S.filter fun f => Sym2.map σ f ∈ K.edgeSet).powerset := by
    ext F
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨h1, h2⟩ f hf
      exact mem_filter.2 ⟨h1 hf, h2 f hf⟩
    · intro h
      exact ⟨fun f hf => (mem_filter.1 (h hf)).1, fun f hf => (mem_filter.1 (h hf)).2⟩
  rw [this, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : ∀ f ∈ S, Sym2.map σ f ∉ K.edgeSet
  · rw [if_pos h, if_pos (Finset.filter_eq_empty_iff.2 h)]
  · rw [if_neg h, if_neg]
    intro h2
    exact h (Finset.filter_eq_empty_iff.1 h2)

end Lov

open Finset Lov in
theorem edge_reconstruction_conjecture.variants.lovasz {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : (Fintype.card V).choose 2 < 2 * G.edgeSet.ncard)
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  have hG : G.edgeSet.ncard = (EF G).card := by
    have : G.edgeSet = ↑(EF G) := by
      ext e
      simp [mem_EF]
    rw [this, Set.ncard_coe_finset]
  have htop : (EF (⊤ : SimpleGraph V)).card = (Fintype.card V).choose 2 := by
    rw [← SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    congr 1
    ext e
    simp [mem_EF]
  have top : ∀ K : SimpleGraph V, (EF K).card = (EF G).card →
      ∀ σ : Equiv.Perm V, ¬ ∀ f ∈ EF G, Sym2.map σ f ∉ K.edgeSet := by
    intro K hK σ hσ
    have hd : Disjoint ((EF G).image (Sym2.map σ)) (EF K) := by
      rw [Finset.disjoint_left]
      intro e he he2
      obtain ⟨f, hf, rfl⟩ := mem_image.1 he
      exact hσ f hf (mem_EF.1 he2)
    have hsub : (EF G).image (Sym2.map σ) ∪ EF K ⊆ EF (⊤ : SimpleGraph V) := by
      intro e he
      rw [mem_union] at he
      rw [mem_EF]
      rcases he with he | he
      · obtain ⟨f, hf, rfl⟩ := mem_image.1 he
        have hf' : f ∈ G.edgeSet := mem_EF.1 hf
        induction f using Sym2.ind with
        | h a b =>
          change s(σ a, σ b) ∈ (⊤ : SimpleGraph V).edgeSet
          rw [SimpleGraph.mem_edgeSet] at hf' ⊢
          exact (SimpleGraph.top_adj _ _).2 (σ.injective.ne (G.ne_of_adj hf'))
      · exact SimpleGraph.edgeSet_subset_edgeSet.2 le_top (mem_EF.1 he)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd,
      card_image_of_injective _ (Sym2.map.injective σ.injective), hK, htop] at hc
    omega
  have zero : ∀ K : SimpleGraph V, (EF K).card = (EF G).card →
      ∑ F ∈ (EF G).powerset, (-1 : ℤ) ^ F.card * (N K F : ℤ) = 0 := by
    intro K hK
    rw [incl_excl, Finset.filter_eq_empty_iff.2 (fun σ _ => top K hK σ)]
    simp
  have diff : ∑ F ∈ (EF G).powerset, (-1 : ℤ) ^ F.card * ((N G F : ℤ) - N H F) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, zero G rfl, zero H (card_EF_eq h).symm,
      sub_self]
  rw [Finset.sum_eq_single (EF G)] at diff
  · have hpow : ((-1 : ℤ)) ^ (EF G).card ≠ 0 := pow_ne_zero _ (by norm_num)
    have hNS : N G (EF G) = N H (EF G) := by
      have := (mul_eq_zero.1 diff).resolve_left hpow
      omega
    have hpos : 0 < N G (EF G) := by
      apply Finset.card_pos.2
      refine ⟨1, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      intro f hf
      rw [Equiv.Perm.coe_one, Sym2.map_id]
      exact mem_EF.1 hf
    rw [hNS] at hpos
    obtain ⟨σ, hσ⟩ := Finset.card_pos.1 hpos
    simp only [mem_filter, mem_univ, true_and] at hσ
    have himg : (EF G).image (Sym2.map σ) = EF H := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨f, hf, rfl⟩ := mem_image.1 he
        exact mem_EF.2 (hσ f hf)
      · rw [card_image_of_injective _ (Sym2.map.injective σ.injective), ← card_EF_eq h]
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
  · intro F hF hne
    have hlt : F.card < (EF G).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨mem_powerset.1 hF, hne⟩)
    rw [N_eq h F hlt, sub_self, mul_zero]
  · intro h'
    exact absurd (mem_powerset_self (EF G)) h'

end ReconstructionConjecture

#print axioms ReconstructionConjecture.edge_reconstruction_conjecture.variants.lovasz
