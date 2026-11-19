import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! WOWII 315. Definitions restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean. -/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `S` is a total dominating set of `G` if every vertex has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

/-- A total dominating set `S` is minimal if no proper subset of `S` is also a
total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

/-- A graph `G` is well totally dominated if every minimal total dominating set
has the same cardinality. -/
def IsWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

/-- The set of pendant vertices (leaves) of `G`: vertices of degree 1. -/
noncomputable def pendantVertices (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun v => G.degree v = 1)

end SimpleGraph

namespace W315

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

lemma uniq {v w x : α} (hv : G.degree v = 1) (h1 : G.Adj v w) (h2 : G.Adj v x) : w = x := by
  obtain ⟨y, _, hy⟩ := degree_eq_one_iff_existsUnique_adj.1 hv
  rw [hy w h1, hy x h2]

lemma closed (hG : G.Connected) (K : Finset α) (a : α) (ha : a ∈ K)
    (hK : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (v : α) : v ∈ K := by
  suffices H : ∀ u w (p : G.Walk u w), u ∈ K → w ∈ K from
    H _ _ (hG.preconnected a v).some ha
  intro u w p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (hK _ hu _ h)

lemma P_indep (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card) :
    ∀ p ∈ pendantVertices G, ∀ q ∈ pendantVertices G, ¬ G.Adj p q := by
  intro p hp q hq hpq
  have hp1 : G.degree p = 1 := (Finset.mem_filter.1 hp).2
  have hq1 : G.degree q = 1 := (Finset.mem_filter.1 hq).2
  have hall : ∀ v, v ∈ ({p, q} : Finset α) := closed G hG _ p (by simp) (by
    intro x hx y hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (uniq G hp1 hxy hpq)
    · exact Or.inl (uniq G hq1 hxy hpq.symm))
  have hpq' : p ≠ q := hpq.ne
  have hPc : (pendantVertices G).card = 2 := by
    have e : pendantVertices G = {p, q} := by
      refine Finset.eq_of_subset_of_card_le (fun v _ => hall v) ?_
      refine Finset.card_le_card ?_
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    rw [e, Finset.card_pair hpq']
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hs2 : s = {p, q} := by
    refine Finset.eq_of_subset_of_card_le (fun v _ => hall v) ?_
    have := hs.card_eq
    rw [Finset.card_pair hpq']
    omega
  exact hs.isIndepSet (by rw [hs2]; simp) (by rw [hs2]; simp) hpq' hpq

lemma supp (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card) :
    ∀ v ∉ pendantVertices G, ∃ p ∈ pendantVertices G, G.Adj v p := by
  intro v hv
  by_contra hc
  simp only [not_exists, not_and] at hc
  have hind : G.IsIndepSet ((insert v (pendantVertices G) : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hc b hb
    · exact fun e => hc a ha e.symm
    · exact P_indep G hG h a ha b hb
  have := hind.card_le_indepNum
  rw [Finset.card_insert_of_notMem hv, h] at this
  omega

lemma mem_tds (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card) {T : Finset α}
    (hT : IsTotalDominatingSet G T) : ∀ v ∉ pendantVertices G, v ∈ T := by
  intro v hv
  obtain ⟨p, hp, hvp⟩ := supp G hG h v hv
  obtain ⟨w, hw, hpw⟩ := hT p
  have : w = v := uniq G (Finset.mem_filter.1 hp).2 hpw hvp.symm
  rwa [← this]

end W315

namespace WrittenOnTheWallII.GraphConjecture315

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conjecture315 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : G.indepNum = (pendantVertices G).card) :
    IsWellTotallyDominated G := by
  by_cases hA : ∀ v ∉ pendantVertices G, ∃ w ∉ pendantVertices G, G.Adj v w
  · have key : ∀ T, IsMinimalTotalDominatingSet G T →
        T = Finset.univ.filter (· ∉ pendantVertices G) := by
      rintro T ⟨hT, hmin⟩
      have hsub : Finset.univ.filter (· ∉ pendantVertices G) ⊆ T := fun v hv =>
        W315.mem_tds G hG h hT v (Finset.mem_filter.1 hv).2
      have htds : IsTotalDominatingSet G (Finset.univ.filter (· ∉ pendantVertices G)) := by
        intro v
        by_cases hv : v ∈ pendantVertices G
        · obtain ⟨w, hw⟩ := (degree_eq_one_iff_existsUnique_adj.1 (Finset.mem_filter.1 hv).2).exists
          exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _,
            fun hwP => W315.P_indep G hG h v hv w hwP hw⟩, hw⟩
        · obtain ⟨w, hw, hvw⟩ := hA v hv
          exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩, hvw⟩
      by_contra hne
      exact hmin _ (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hne e.symm⟩) htds
    intro S T hS hT
    rw [key S hS, key T hT]
  · rcases not_forall.1 hA with ⟨s, hs⟩
    rcases Classical.not_imp.1 hs with ⟨hsP, hs2⟩
    have hnb : ∀ w, G.Adj s w → w ∈ pendantVertices G := fun w hw => by
      by_contra hw'
      exact hs2 ⟨w, hw', hw⟩
    have hall := W315.closed G hG (insert s (G.neighborFinset s)) s (Finset.mem_insert_self _ _) (by
      intro x hx y hxy
      rw [Finset.mem_insert, mem_neighborFinset] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inr hxy
      · exact Or.inl (W315.uniq G (Finset.mem_filter.1 (hnb x hx)).2 hxy hx.symm))
    have hadj : ∀ x, x ≠ s → G.Adj s x := fun x hx => by
      have := hall x
      rw [Finset.mem_insert, mem_neighborFinset] at this
      tauto
    have key : ∀ T, IsMinimalTotalDominatingSet G T → T.card = 2 := by
      rintro T ⟨hT, hmin⟩
      have hsT : s ∈ T := W315.mem_tds G hG h hT s hsP
      obtain ⟨l, hl, hsl⟩ := hT s
      have hls : s ≠ l := hsl.ne
      have htds : IsTotalDominatingSet G {s, l} := by
        intro v
        by_cases hv : v = s
        · rw [hv]; exact ⟨l, by simp, hsl⟩
        · exact ⟨s, by simp, (hadj v hv).symm⟩
      have hsub : ({s, l} : Finset α) ⊆ T := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      have e : T = {s, l} := by
        by_contra hne
        exact hmin _ (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hne e.symm⟩) htds
      rw [e, Finset.card_pair hls]
    intro S T hS hT
    rw [key S hS, key T hT]

end WrittenOnTheWallII.GraphConjecture315

#print axioms WrittenOnTheWallII.GraphConjecture315.conjecture315
