import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! WOWII 101 (Hajnal's inequality). Definitions restated from
FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean. -/

namespace WOWII101Aux

open SimpleGraph

variable {β : Type*} [Fintype β] [DecidableEq β] (G : SimpleGraph β)

omit [Fintype β] in
/-- Swap lemma: `W ∪ X` independent, so `|X| ≤ |S \ W|` for a maximum `S`. -/
lemma swap_le {S X W : Finset β} (hS : G.IsIndepSet (S : Set β))
    (hX : G.IsIndepSet (X : Set β))
    (hSmax : ∀ T : Finset β, G.IsIndepSet (T : Set β) → T.card ≤ S.card)
    (hXS : Disjoint X S) (hW : W ⊆ S) (hna : ∀ w ∈ W, ∀ x ∈ X, ¬ G.Adj w x) :
    X.card ≤ (S \ W).card := by
  have hind : G.IsIndepSet ((W ∪ X : Finset β) : Set β) := by
    intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hS (hW ha) (hW hb) hab
    · exact hna a ha b hb
    · exact fun h => hna b hb a ha h.symm
    · exact hX ha hb hab
  have h1 := hSmax _ hind
  have h2 : (W ∪ X).card = W.card + X.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left hW hXS.symm)
  have h3 := Finset.card_sdiff_add_card_eq_card hW
  omega

/-- Set-and-collection lemma (Levit–Mandrescu) relative to a fixed maximum set `S0`. -/
lemma collection (S0 : Finset β) (h0 : G.IsIndepSet (S0 : Set β))
    (hc0 : S0.card = G.indepNum) :
    ∀ Γ : Finset (Finset β), (∀ T ∈ Γ, G.IsIndepSet (T : Set β) ∧ T.card = G.indepNum) →
    2 * G.indepNum ≤ (S0.filter (fun v => ∀ T ∈ Γ, v ∈ T)).card + (S0 ∪ Γ.biUnion id).card := by
  intro Γ
  induction Γ using Finset.induction_on with
  | empty => intro _; simp; omega
  | insert S Γ hSΓ ih =>
    intro hΓ
    have hS := hΓ S (Finset.mem_insert_self _ _)
    have ih := ih (fun T hT => hΓ T (Finset.mem_insert_of_mem hT))
    set I := S0.filter (fun v => ∀ T ∈ Γ, v ∈ T) with hI
    set U := S0 ∪ Γ.biUnion id with hU
    have eI : S0.filter (fun v => ∀ T ∈ insert S Γ, v ∈ T) = I ∩ S := by
      ext v
      simp only [hI, Finset.mem_filter, Finset.mem_inter, Finset.forall_mem_insert]
      tauto
    have eU : S0 ∪ (insert S Γ).biUnion id = U ∪ S := by
      ext v
      simp only [hU, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, id]
      constructor
      · rintro (h | ⟨T, rfl | hT, hv⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inr hv
        · exact Or.inl (Or.inr ⟨T, hT, hv⟩)
      · rintro ((h | ⟨T, hT, hv⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨T, Or.inr hT, hv⟩
        · exact Or.inr ⟨S, Or.inl rfl, h⟩
    rw [eI, eU]
    have hIS0 : I ⊆ S0 := Finset.filter_subset _ _
    have key0 := swap_le G (S := S) (X := I \ S) (W := S ∩ U) hS.1
      (Set.Pairwise.mono (Finset.coe_subset.2 ((Finset.sdiff_subset).trans hIS0)) h0)
      (fun T hT => hS.2 ▸ hT.card_le_indepNum) Finset.sdiff_disjoint Finset.inter_subset_left
      (by
        intro w hw x hx hadj
        have hne : w ≠ x := G.ne_of_adj hadj
        rw [Finset.mem_inter] at hw
        rw [Finset.mem_sdiff, hI, Finset.mem_filter] at hx
        rw [hU, Finset.mem_union, Finset.mem_biUnion] at hw
        rcases hw.2 with h | ⟨T, hT, hwT⟩
        · exact h0 h hx.1.1 hne hadj
        · exact (hΓ T (Finset.mem_insert_of_mem hT)).1 hwT (hx.1.2 T hT) hne hadj)
    have e : S \ (S ∩ U) = S \ U := by
      ext v; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [e] at key0
    have c1 := Finset.card_sdiff_add_card_inter I S
    have c2 := Finset.card_sdiff_add_card S U
    rw [Finset.union_comm] at c2
    omega

end WOWII101Aux

namespace WrittenOnTheWallII.GraphConjecture101

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def indepNumDeleteVertex (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (Set.univ \ {v})).indepNum

noncomputable def alphaCore (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => indepNumDeleteVertex G v < G.indepNum)

omit [Nontrivial α] [DecidableEq α] in
lemma mem_core (G : SimpleGraph α) (v : α)
    (hv : ∀ T : Finset α, G.IsIndepSet (T : Set α) → T.card = G.indepNum → v ∈ T) :
    v ∈ alphaCore G := by
  unfold alphaCore
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold indepNumDeleteVertex
  by_contra hlt
  have hge := not_lt.1 hlt
  obtain ⟨s, hs⟩ := (G.induce (Set.univ \ {v})).exists_isNIndepSet_indepNum
  let t : Finset α := s.map (Function.Embedding.subtype _)
  have ht : G.IsIndepSet (t : Set α) := by
    intro a ha b hb hab hadj
    simp only [t, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact hs.isIndepSet ha' hb' (fun e => hab (congrArg Subtype.val e)) hadj
  have hcard : t.card = (G.induce (Set.univ \ {v})).indepNum := by
    simp [t, hs.card_eq]
  have hle := ht.card_le_indepNum
  have hvt := hv t ht (by omega)
  simp only [t, Finset.mem_map, Function.Embedding.coe_subtype] at hvt
  obtain ⟨a, _, ha⟩ := hvt
  have := a.2
  rw [ha] at this
  simp at this

theorem conjecture101 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2 := by
  classical
  obtain ⟨S0, hS0⟩ := G.exists_isNIndepSet_indepNum
  let Γ : Finset (Finset α) :=
    Finset.univ.filter (fun T => G.IsIndepSet (T : Set α) ∧ T.card = G.indepNum)
  have hc := WOWII101Aux.collection G S0 hS0.isIndepSet hS0.card_eq Γ
    (fun T hT => (Finset.mem_filter.1 hT).2)
  have h1 : (S0.filter (fun v => ∀ T ∈ Γ, v ∈ T)).card ≤ (alphaCore G).card := by
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    apply mem_core G v
    intro T hT hTc
    exact hv.2 T (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, hTc⟩)
  have h2 := Finset.card_le_univ (S0 ∪ Γ.biUnion id)
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

end WrittenOnTheWallII.GraphConjecture101

#print axioms WrittenOnTheWallII.GraphConjecture101.conjecture101
