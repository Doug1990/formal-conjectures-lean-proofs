import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! WOWII 316. Definitions restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean and
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean. -/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

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

namespace W316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

lemma uniq {v w x : α} (hv : G.degree v = 1) (h1 : G.Adj v w) (h2 : G.Adj v x) : w = x := by
  obtain ⟨y, _, hy⟩ := degree_eq_one_iff_existsUnique_adj.1 hv
  rw [hy w h1, hy x h2]

omit [DecidableEq α] [DecidableRel G.Adj] in
lemma closed (hG : G.Connected) (K : Finset α) (a : α) (ha : a ∈ K)
    (hK : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (v : α) : v ∈ K := by
  suffices H : ∀ u w (p : G.Walk u w), u ∈ K → w ∈ K from
    H _ _ (hG.preconnected a v).some ha
  intro u w p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (hK _ hu _ h)

lemma pp (hG : G.Connected) {l q : α} (hl : l ∈ pendantVertices G) (hq : q ∈ pendantVertices G)
    (hlq : G.Adj l q) (v : α) : v = l ∨ v = q := by
  have hl1 : G.degree l = 1 := (Finset.mem_filter.1 hl).2
  have hq1 : G.degree q = 1 := (Finset.mem_filter.1 hq).2
  have := closed G hG ({l, q} : Finset α) l (by simp) (by
    intro x hx y hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (uniq G hl1 hxy hlq)
    · exact Or.inl (uniq G hq1 hxy hlq.symm)) v
  simpa using this

lemma sum_inter (s : Finset α) :
    ∑ v, (G.neighborFinset v ∩ s).card = ∑ w ∈ s, G.degree w := by
  have h1 : ∀ v, (G.neighborFinset v ∩ s).card = ∑ w ∈ s, if G.Adj v w then 1 else 0 := by
    intro v
    rw [← Finset.card_filter]
    congr 1
    ext w
    simp [mem_neighborFinset, and_comm]
  have h2 : ∀ w, G.degree w = ∑ v, if G.Adj v w then 1 else 0 := by
    intro w
    rw [← Finset.card_filter, ← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp [mem_neighborFinset, G.adj_comm]
  simp only [h1, h2]
  exact Finset.sum_comm

lemma cl (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card)
    (a b : α) (ha : a ∉ pendantVertices G) (hb : b ∉ pendantVertices G) (hab : a ≠ b) :
    G.Adj a b := by
  by_contra hn
  obtain ⟨P, hP⟩ : ∃ P, P = pendantVertices G := ⟨_, rfl⟩
  rw [← hP] at h ha hb
  obtain ⟨C, hC⟩ : ∃ C, C = Finset.univ \ P := ⟨_, rfl⟩
  have hmC : ∀ v, v ∈ C ↔ v ∉ P := fun v => by simp [hC]
  have haC : a ∈ C := (hmC a).2 ha
  have hbC : b ∈ C := (hmC b).2 hb
  have hn_eq : C.card + P.card = Fintype.card α := by
    rw [hC]; exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hPdeg : ∀ v ∈ P, G.degree v = 1 := fun v hv => by
    rw [hP] at hv; exact (Finset.mem_filter.1 hv).2
  by_cases hc : 3 ≤ C.card
  · have hnpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
    have hE : (∑ v, Gᶜ.degree v) ≤ P.card * Fintype.card α := by
      unfold averageDegree at h
      rw [div_le_iff₀ (by exact_mod_cast hnpos)] at h
      have h' : ((∑ v, Gᶜ.degree v : ℕ) : ℚ) ≤ ((P.card * Fintype.card α : ℕ) : ℚ) := by
        rw [Nat.cast_sum, Nat.cast_mul]; exact h
      exact Nat.cast_le.1 h'
    have hsum : ∑ v, (Gᶜ.degree v + G.degree v + 1) = Fintype.card α * Fintype.card α := by
      rw [Finset.sum_congr rfl (g := fun _ => Fintype.card α), Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
      intro v _
      rw [degree_compl]
      have := G.degree_lt_card_verts v
      omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
    have hD : ∑ v, G.degree v = ∑ v ∈ C, G.degree v + P.card := by
      rw [← Finset.sum_sdiff (Finset.subset_univ P), ← hC]
      congr 1
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl hPdeg
    have hsplit : ∀ v, G.degree v =
        (G.neighborFinset v \ P).card + (G.neighborFinset v ∩ P).card := fun v => by
      rw [Finset.card_sdiff_add_card_inter, card_neighborFinset_eq_degree]
    have hg : ∑ v ∈ C, (G.neighborFinset v ∩ P).card ≤ P.card := by
      calc _ ≤ ∑ v, (G.neighborFinset v ∩ P).card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = ∑ w ∈ P, G.degree w := sum_inter G P
        _ = P.card := by
          rw [Finset.card_eq_sum_ones]
          exact Finset.sum_congr rfl hPdeg
    have hf1 : ∀ v ∈ C, (G.neighborFinset v \ P).card + 1 ≤ C.card := fun v hv => by
      have hs : G.neighborFinset v \ P ⊆ C.erase v := by
        intro w hw
        rw [Finset.mem_sdiff, mem_neighborFinset] at hw
        exact Finset.mem_erase.2 ⟨hw.1.ne.symm, (hmC w).2 hw.2⟩
      have h1 := Finset.card_le_card hs
      rw [Finset.card_erase_of_mem hv] at h1
      omega
    have hf2 : ∀ x y, x ∈ C → y ∈ C → x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x \ P).card + 2 ≤ C.card := fun x y hx hy hxy hnxy => by
      have hs : G.neighborFinset x \ P ⊆ (C.erase x).erase y := by
        intro w hw
        rw [Finset.mem_sdiff, mem_neighborFinset] at hw
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨hw.1.ne.symm, (hmC w).2 hw.2⟩⟩
        rintro rfl
        exact hnxy hw.1
      have h1 := Finset.card_le_card hs
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩),
        Finset.card_erase_of_mem hx] at h1
      omega
    have hfa := hf2 a b haC hbC hab hn
    have hfb := hf2 b a hbC haC hab.symm (fun e => hn e.symm)
    have hbC' : b ∈ C.erase a := Finset.mem_erase.2 ⟨hab.symm, hbC⟩
    have hrest : ∑ v ∈ (C.erase a).erase b, ((G.neighborFinset v \ P).card + 1) ≤
        ((C.erase a).erase b).card * C.card := by
      have := Finset.sum_le_card_nsmul ((C.erase a).erase b)
        (fun v => (G.neighborFinset v \ P).card + 1) C.card (fun v hv =>
          hf1 v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)))
      simpa [smul_eq_mul] using this
    have hcard : ((C.erase a).erase b).card + 2 = C.card := by
      rw [Finset.card_erase_of_mem hbC', Finset.card_erase_of_mem haC]
      omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hrest
    have hCsum : ∑ v ∈ C, (G.neighborFinset v \ P).card + C.card + 2 ≤ C.card * C.card := by
      rw [← Finset.add_sum_erase C _ haC, ← Finset.add_sum_erase (C.erase a) _ hbC']
      have e : ((C.erase a).erase b).card * C.card + 2 * C.card = C.card * C.card := by
        rw [← hcard]; ring
      linarith
    have hCdeg : ∑ v ∈ C, G.degree v = ∑ v ∈ C, (G.neighborFinset v \ P).card +
        ∑ v ∈ C, (G.neighborFinset v ∩ P).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => hsplit v)
    have e1 : Fintype.card α * Fintype.card α =
        C.card * C.card + 2 * (C.card * P.card) + P.card * P.card := by rw [← hn_eq]; ring
    have e2 : P.card * Fintype.card α = C.card * P.card + P.card * P.card := by
      rw [← hn_eq]; ring
    have e3 : 3 * P.card ≤ C.card * P.card := Nat.mul_le_mul_right _ hc
    linarith
  · have hCab : ∀ v, v ∉ P → v = a ∨ v = b := by
      intro v hv
      by_contra hne
      simp only [not_or] at hne
      have hs : ({a, b, v} : Finset α) ⊆ C := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact haC
        · exact hbC
        · exact (hmC _).2 hv
      have h1 := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hne.1]),
        Finset.card_pair (Ne.symm hne.2)] at h1
      omega
    have hall := closed G hG (insert a (Finset.univ.filter (fun l => l ∈ P ∧ G.Adj l a))) a
      (Finset.mem_insert_self _ _) (by
        intro x hx y hxy
        rw [Finset.mem_insert, Finset.mem_filter] at hx
        rw [Finset.mem_insert, Finset.mem_filter]
        rcases hx with rfl | ⟨_, hxP, hxa⟩
        · right
          refine ⟨Finset.mem_univ _, ?_, hxy.symm⟩
          by_contra hyP
          rcases hCab y hyP with rfl | rfl
          · exact hxy.ne rfl
          · exact hn hxy
        · left
          exact uniq G (hPdeg x hxP) hxy hxa) b
    rw [Finset.mem_insert, Finset.mem_filter] at hall
    rcases hall with h1 | ⟨_, h2, _⟩
    · exact hab h1.symm
    · exact hb h2

lemma sub_T {T : Finset α} (hT : IsTotalDominatingSet G T) {l s : α}
    (hl : l ∈ pendantVertices G) (hls : G.Adj l s) : s ∈ T := by
  obtain ⟨w, hw, hlw⟩ := hT l
  rwa [uniq G (Finset.mem_filter.1 hl).2 hls hlw]

lemma two {T : Finset α} (hT : IsMinimalTotalDominatingSet G T) {x : α} (hx : x ∈ T)
    (hu : ∀ v, v ≠ x → G.Adj v x) : T.card = 2 := by
  obtain ⟨w, hw, hxw⟩ := hT.1 x
  have htds : IsTotalDominatingSet G {x, w} := by
    intro v
    by_cases hv : v = x
    · rw [hv]; exact ⟨w, by simp, hxw⟩
    · exact ⟨x, by simp, hu v hv⟩
  have hsub : ({x, w} : Finset α) ⊆ T := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have e : T = {x, w} := by
    by_contra hne
    exact hT.2 _ (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hne e.symm⟩) htds
  rw [e, Finset.card_pair hxw.ne]

end W316

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conjecture316 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    IsWellTotallyDominated G := by
  have cl := W316.cl G hG h
  obtain ⟨v0⟩ := hG.nonempty
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset α,
      Q = Finset.univ.filter (fun s => ∃ l ∈ pendantVertices G, G.Adj l s) := ⟨_, rfl⟩
  have hmQ : ∀ s, s ∈ Q ↔ ∃ l ∈ pendantVertices G, G.Adj l s := fun s => by simp [hQ]
  by_cases hQ2 : 2 ≤ Q.card
  · have key : ∀ T, IsMinimalTotalDominatingSet G T → T = Q := by
      rintro T ⟨hT, hmin⟩
      have hsub : Q ⊆ T := by
        intro s hs
        obtain ⟨l, hl, hls⟩ := (hmQ s).1 hs
        exact W316.sub_T G hT hl hls
      have htds : IsTotalDominatingSet G Q := by
        intro v
        by_cases hv : v ∈ pendantVertices G
        · obtain ⟨w, hw⟩ :=
            (degree_eq_one_iff_existsUnique_adj.1 (Finset.mem_filter.1 hv).2).exists
          exact ⟨w, (hmQ w).2 ⟨v, hv, hw⟩, hw⟩
        · obtain ⟨q, hq, hqv⟩ := Q.exists_mem_ne (by omega) v
          refine ⟨q, hq, ?_⟩
          by_cases hqP : q ∈ pendantVertices G
          · exfalso
            obtain ⟨l, hl, hlq⟩ := (hmQ q).1 hq
            rcases W316.pp G hG hl hqP hlq v with rfl | rfl
            · exact hv hl
            · exact hv hqP
          · exact cl v q hv hqP hqv.symm
      by_contra hne
      exact hmin _ (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hne e.symm⟩) htds
    intro S T hS hT
    rw [key S hS, key T hT]
  · have key : ∀ T, IsMinimalTotalDominatingSet G T → T.card = 2 := by
      intro T hT
      by_cases hQe : Q.Nonempty
      · obtain ⟨s, hs⟩ := hQe
        obtain ⟨l, hl, hls⟩ := (hmQ s).1 hs
        apply W316.two G hT (W316.sub_T G hT.1 hl hls)
        intro v hvs
        by_cases hv : v ∈ pendantVertices G
        · obtain ⟨w, hw⟩ :=
            (degree_eq_one_iff_existsUnique_adj.1 (Finset.mem_filter.1 hv).2).exists
          have hwQ : w ∈ Q := (hmQ w).2 ⟨v, hv, hw⟩
          have : w = s := Finset.card_le_one.1 (by omega) _ hwQ _ hs
          rw [← this]; exact hw
        · by_cases hsP : s ∈ pendantVertices G
          · exfalso
            rcases W316.pp G hG hl hsP hls v with rfl | rfl
            · exact hv hl
            · exact hv hsP
          · exact cl v s hv hsP hvs
      · have hP : ∀ v, v ∉ pendantVertices G := fun v hv => by
          obtain ⟨w, hw⟩ :=
            (degree_eq_one_iff_existsUnique_adj.1 (Finset.mem_filter.1 hv).2).exists
          exact hQe ⟨w, (hmQ w).2 ⟨v, hv, hw⟩⟩
        obtain ⟨x, hx, -⟩ := hT.1 v0
        exact W316.two G hT hx (fun v hvx => cl v x (hP v) (hP x) hvx)
    intro S T hS hT
    rw [key S hS, key T hT]

end WrittenOnTheWallII.GraphConjecture316

#print axioms WrittenOnTheWallII.GraphConjecture316.conjecture316
