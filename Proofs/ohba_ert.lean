import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph Finset

namespace OhbaConjecture

variable {V : Type*}

def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

lemma disj_two {ι : Type*} (L : (Σ _ : ι, Fin 2) → Finset ℕ) (i : ι)
    (hd : Disjoint (L ⟨i, 0⟩) (L ⟨i, 1⟩)) :
    ∀ a b : Fin 2, a ≠ b → Disjoint (L ⟨i, a⟩) (L ⟨i, b⟩) := by
  simp only [Fin.forall_fin_two]
  exact ⟨⟨fun h => absurd rfl h, fun _ => hd⟩, ⟨fun _ => hd.symm, fun h => absurd rfl h⟩⟩

/-- Hall step: all parts have disjoint lists. -/
lemma hall_case {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : (Σ _ : ι, Fin 2) → Finset ℕ)
    (hL : ∀ v : (Σ _ : ι, Fin 2), v.1 ∈ s → s.card ≤ (L v).card)
    (hdisj : ∀ i ∈ s, Disjoint (L ⟨i, 0⟩) (L ⟨i, 1⟩)) :
    ∃ c : (Σ _ : ι, Fin 2) → ℕ, (∀ v, v.1 ∈ s → c v ∈ L v) ∧
      ∀ u v : (Σ _ : ι, Fin 2), u.1 ∈ s → v.1 ∈ s → u.1 ≠ v.1 → c u ≠ c v := by
  let t : {v : (Σ _ : ι, Fin 2) // v.1 ∈ s} → Finset ℕ := fun v => L v.1
  have hall : ∀ X : Finset {v : (Σ _ : ι, Fin 2) // v.1 ∈ s}, X.card ≤ (X.biUnion t).card := by
    intro X
    by_cases hX : X.card ≤ s.card
    · rcases X.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · simp
      · calc X.card ≤ s.card := hX
          _ ≤ (L v.1).card := hL v.1 v.2
          _ ≤ (X.biUnion t).card := card_le_card (subset_biUnion_of_mem t hv)
    · push Not at hX
      have hmap : Set.MapsTo (fun v : {v : (Σ _ : ι, Fin 2) // v.1 ∈ s} => v.1.1) X s := by
        intro v _
        exact v.2
      obtain ⟨u, hu, w, hw, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hX hmap
      have hXc : X.card ≤ 2 * s.card := by
        have : X.card ≤ (s ×ˢ (univ : Finset (Fin 2))).card := by
          apply card_le_card_of_injOn (fun v : {v : (Σ _ : ι, Fin 2) // v.1 ∈ s} => (v.1.1, v.1.2))
          · intro v _
            simp only [coe_product, coe_univ, Set.mem_prod, mem_coe, Set.mem_univ, and_true]
            exact v.2
          · rintro ⟨⟨a1, b1⟩, h1⟩ - ⟨⟨a2, b2⟩, h2⟩ - h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        rw [card_product, card_univ, Fintype.card_fin] at this
        omega
      rcases u with ⟨⟨i, a⟩, hu'⟩
      rcases w with ⟨⟨j, b⟩, hw'⟩
      simp only at heq
      subst heq
      have hab : a ≠ b := by
        intro h
        subst h
        exact hne rfl
      have hd := disj_two L i (hdisj i hu') a b hab
      have h1 := hL ⟨i, a⟩ hu'
      have h2 := hL ⟨i, b⟩ hw'
      have hsub : L ⟨i, a⟩ ∪ L ⟨i, b⟩ ⊆ X.biUnion t := by
        apply union_subset
        · exact subset_biUnion_of_mem t hu
        · exact subset_biUnion_of_mem t hw
      have := card_le_card hsub
      rw [card_union_of_disjoint hd] at this
      omega
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨fun v => if h : v.1 ∈ s then f ⟨v, h⟩ else 0, ?_, ?_⟩
  · intro v hv
    simp only [hv, dif_pos]
    exact hf ⟨v, hv⟩
  · intro u v hu hv huv
    simp only [hu, hv, dif_pos]
    intro h
    have := hfinj h
    exact huv (congrArg (fun x => x.1.1) this)

lemma main {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ L : (Σ _ : ι, Fin 2) → Finset ℕ,
      (∀ v : (Σ _ : ι, Fin 2), v.1 ∈ s → s.card ≤ (L v).card) →
      ∃ c : (Σ _ : ι, Fin 2) → ℕ, (∀ v, v.1 ∈ s → c v ∈ L v) ∧
        ∀ u v : (Σ _ : ι, Fin 2), u.1 ∈ s → v.1 ∈ s → u.1 ≠ v.1 → c u ≠ c v := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro L hL
  by_cases hA : ∃ i ∈ s, (L ⟨i, 0⟩ ∩ L ⟨i, 1⟩).Nonempty
  · obtain ⟨i, hi, x, hx⟩ := hA
    rw [mem_inter] at hx
    have hx' : ∀ b : Fin 2, x ∈ L ⟨i, b⟩ := Fin.forall_fin_two.2 hx
    obtain ⟨c', hc1, hc2⟩ := ih (s.erase i) (erase_ssubset hi) (fun v => (L v).erase x) (by
      intro v hv
      have h1 := hL v (mem_of_mem_erase hv)
      have h2 := pred_card_le_card_erase (s := L v) (a := x)
      have h3 := card_erase_of_mem hi
      omega)
    refine ⟨fun v => if v.1 = i then x else c' v, ?_, ?_⟩
    · intro v hv
      by_cases h : v.1 = i
      · simp only [h, if_true]
        rcases v with ⟨j, b⟩
        simp only at h
        subst h
        exact hx' b
      · simp only [h, if_false]
        exact mem_of_mem_erase (hc1 v (mem_erase.2 ⟨h, hv⟩))
    · intro u v hu hv huv
      by_cases h1 : u.1 = i <;> by_cases h2 : v.1 = i
      · exact absurd (h1.trans h2.symm) huv
      · simp only [h1, h2, if_true, if_false]
        have := hc1 v (mem_erase.2 ⟨h2, hv⟩)
        exact fun h => (mem_erase.1 this).1 h.symm
      · simp only [h1, h2, if_true, if_false]
        exact (mem_erase.1 (hc1 u (mem_erase.2 ⟨h1, hu⟩))).1
      · simp only [h1, h2, if_false]
        exact hc2 u v (mem_erase.2 ⟨h1, hu⟩) (mem_erase.2 ⟨h2, hv⟩) huv
  · have hdisj : ∀ i ∈ s, Disjoint (L ⟨i, 0⟩) (L ⟨i, 1⟩) := fun i hi =>
      Finset.disjoint_iff_inter_eq_empty.2
        (Finset.not_nonempty_iff_eq_empty.1 (fun h => hA ⟨i, hi, h⟩))
    exact hall_case s L hL hdisj

theorem ohba_conjecture.variants.erdos_rubin_taylor (k : ℕ) :
    Choosable (completeMultipartiteGraph (fun _ : Fin k => Fin 2)) k := by
  intro L hL
  obtain ⟨c, h1, h2⟩ := main (univ : Finset (Fin k)) L
    (fun v _ => by rw [hL v, card_univ, Fintype.card_fin])
  exact ⟨c, fun v => h1 v (mem_univ _), fun u v huv => h2 u v (mem_univ _) (mem_univ _) huv⟩

end OhbaConjecture

#print axioms OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor
