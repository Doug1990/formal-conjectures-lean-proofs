import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Order.Lattice.Nat

namespace LinearArboricityConjecture

variable {V : Type*}

def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, (F.neighborSet v).ncard ≤ 2

def HasLinearForestDecomposition (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Fin k → SimpleGraph V, (∀ i, IsLinearForest (D i) ∧ D i ≤ G) ∧
    ∀ u v, G.Adj u v ↔ ∃! i, (D i).Adj u v

noncomputable def linearArboricity (G : SimpleGraph V) : ℕ :=
  sInf {k | HasLinearForestDecomposition G k}

namespace LAC

open SimpleGraph Finset Classical

variable [Fintype V]

def Valid (G R : SimpleGraph V) : Prop :=
  R ≤ G ∧ ∀ x, (R.neighborSet x).ncard ≤ 2 ∧ ((G \ R).neighborSet x).ncard ≤ 2

noncomputable def P (G R : SimpleGraph V) : ℕ :=
  #(univ.filter (fun q : V × V => R.Reachable q.1 q.2)) +
  #(univ.filter (fun q : V × V => (G \ R).Reachable q.1 q.2))

lemma split {G R : SimpleGraph V} (hR : R ≤ G) (x : V) :
    (G.neighborSet x).ncard = (R.neighborSet x).ncard + ((G \ R).neighborSet x).ncard := by
  have : G.neighborSet x = R.neighborSet x ∪ (G \ R).neighborSet x := by
    ext y
    simp only [Set.mem_union, mem_neighborSet, sdiff_adj]
    constructor
    · intro h
      by_cases h' : R.Adj x y
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h)
      · exact hR h
      · exact h.1
  rw [this]
  exact Set.ncard_union_eq (Set.disjoint_left.2 fun y h1 h2 => by
    rw [mem_neighborSet, sdiff_adj] at h2; exact h2.2 h1)

omit [Fintype V] in
lemma sdsd {G B : SimpleGraph V} (hB : B ≤ G) : G \ (G \ B) = B := by
  ext x y
  simp only [sdiff_adj, not_and, not_not]
  constructor
  · rintro ⟨h1, h2⟩; exact h2 h1
  · intro h; exact ⟨hB h, fun _ => h⟩

omit [Fintype V] in
lemma valid_swap {G R : SimpleGraph V} (hR : Valid G R) : Valid G (G \ R) := by
  refine ⟨sdiff_le, fun x => ⟨(hR.2 x).2, ?_⟩⟩
  rw [sdsd hR.1]; exact (hR.2 x).1

omit [Fintype V] in
lemma reach_del {R : SimpleGraph V} {v w : V}
    (h : (R.deleteEdges {s(v, w)}).Reachable v w) {x y : V} (hxy : R.Reachable x y) :
    (R.deleteEdges {s(v, w)}).Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hab p ih =>
    refine Reachable.trans ?_ ih
    by_cases he : s(a, b) = s(v, w)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
    · exact Adj.reachable (by
        rw [deleteEdges_adj]
        exact ⟨hab, fun hm => he (Set.mem_singleton_iff.1 hm)⟩)

omit [Fintype V] in
lemma two_nbrs {R : SimpleGraph V} {v w : V} (hadj : R.Adj v w) (p : R.Walk v w)
    (hp : s(v, w) ∉ p.edges) :
    ∃ x, x ≠ w ∧ R.Adj v x ∧ ∃ q : R.Walk v x, s(v, x) ∉ q.edges := by
  have key : ∀ r : R.Walk v w, r.IsPath → s(v, w) ∉ r.edges →
      ∃ x, x ≠ w ∧ R.Adj v x ∧ ∃ q : R.Walk v x, s(v, x) ∉ q.edges := by
    intro r hr hre
    cases r with
    | nil => exact (hadj.ne rfl).elim
    | @cons _ x _ h q =>
      rw [Walk.cons_isPath_iff] at hr
      have hxw : x ≠ w := by
        rintro rfl
        exact hre (by simp)
      refine ⟨x, hxw, h, Walk.cons hadj q.reverse, ?_⟩
      rw [Walk.edges_cons, List.mem_cons, Walk.edges_reverse, List.mem_reverse]
      rintro (he | he)
      · rcases Sym2.eq_iff.1 he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hxw h2
        · exact hadj.ne h1
      · exact hr.2 (q.fst_mem_support_of_mem_edges he)
  exact key _ (p.toPath).2 (fun h => hp (Walk.edges_toPath_subset_edges p h))

lemma three_ends_aux (H : SimpleGraph V) (C : H.ConnectedComponent)
    (hdeg : ∀ x, (H.neighborSet x).ncard ≤ 2) (a b c : C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : (H.neighborSet a.1).ncard ≤ 1) (hb : (H.neighborSet b.1).ncard ≤ 1)
    (hc : (H.neighborSet c.1).ncard ≤ 1) : False := by
  have hK := C.connected_toSimpleGraph
  have h1 := hK.card_vert_le_card_edgeSet_add_one
  have hsum := C.toSimpleGraph.sum_degrees_eq_twice_card_edges
  have hdK : ∀ x, C.toSimpleGraph.degree x ≤ (H.neighborSet x.1).ncard := by
    intro x
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      ← Set.ncard_image_of_injective _ Subtype.val_injective]
    exact Set.ncard_le_ncard (by rintro _ ⟨y, hy, rfl⟩; exact hy) (Set.toFinite _)
  have haS : a ∉ ({b, c} : Finset C) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have hS : ({a, b, c} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_pair hbc]
  have hS1 : ∀ x ∈ ({a, b, c} : Finset C), C.toSimpleGraph.degree x ≤ 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_trans (hdK _) ha
    · exact le_trans (hdK _) hb
    · exact le_trans (hdK _) hc
  have hsumS : ∑ x ∈ ({a, b, c} : Finset C), C.toSimpleGraph.degree x ≤ 3 := by
    calc _ ≤ ∑ x ∈ ({a, b, c} : Finset C), 1 := Finset.sum_le_sum hS1
      _ = 3 := by rw [Finset.sum_const, hS, smul_eq_mul, mul_one]
  have hrest : ∑ x ∈ ({a, b, c} : Finset C)ᶜ, C.toSimpleGraph.degree x
      ≤ 2 * ({a, b, c} : Finset C)ᶜ.card := by
    calc _ ≤ ∑ x ∈ ({a, b, c} : Finset C)ᶜ, 2 :=
          Finset.sum_le_sum (fun x _ => le_trans (hdK x) (hdeg x.1))
      _ = 2 * ({a, b, c} : Finset C)ᶜ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplit := Finset.sum_add_sum_compl ({a, b, c} : Finset C)
    (fun x => C.toSimpleGraph.degree x)
  rw [Finset.card_compl, hS] at hrest
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h1
  have hS3 : 3 ≤ Fintype.card C := hS ▸ Finset.card_le_univ _
  omega

lemma three_ends (H : SimpleGraph V) (hdeg : ∀ x, (H.neighborSet x).ncard ≤ 2)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : (H.neighborSet a).ncard ≤ 1) (hb : (H.neighborSet b).ncard ≤ 1)
    (hc : (H.neighborSet c).ncard ≤ 1)
    (rb : H.Reachable a b) (rc : H.Reachable a c) : False := by
  have ma : a ∈ H.connectedComponentMk a := (ConnectedComponent.mem_supp_iff _ _).2 rfl
  have mb : b ∈ H.connectedComponentMk a :=
    (ConnectedComponent.mem_supp_iff _ _).2 (ConnectedComponent.eq.2 rb.symm)
  have mc : c ∈ H.connectedComponentMk a :=
    (ConnectedComponent.mem_supp_iff _ _).2 (ConnectedComponent.eq.2 rc.symm)
  exact three_ends_aux H _ hdeg ⟨a, ma⟩ ⟨b, mb⟩ ⟨c, mc⟩
    (fun h => hab (congrArg Subtype.val h)) (fun h => hac (congrArg Subtype.val h))
    (fun h => hbc (congrArg Subtype.val h)) ha hb hc

lemma improve {G R : SimpleGraph V} (hR : Valid G R)
    {v w : V} (hadj : R.Adj v w) (p : R.Walk v w) (hp : s(v, w) ∉ p.edges)
    (hv : ((G \ R).neighborSet v).ncard ≤ 1) (hw : ((G \ R).neighborSet w).ncard ≤ 1)
    (hnr : ¬ (G \ R).Reachable v w) :
    ∃ R', Valid G R' ∧ P G R < P G R' := by
  have hne : v ≠ w := hadj.ne
  have hR'R : R.deleteEdges {s(v, w)} ≤ R := deleteEdges_le _
  have hBB : G \ R ≤ G \ R.deleteEdges {s(v, w)} := fun a b h => by
    rw [sdiff_adj] at h ⊢; exact ⟨h.1, fun h' => h.2 (hR'R h')⟩
  have hBvw : (G \ R.deleteEdges {s(v, w)}).Adj v w := by
    rw [sdiff_adj, deleteEdges_adj]
    exact ⟨hR.1 hadj, fun h => h.2 (Set.mem_singleton _)⟩
  have hB' : ∀ a b, (G \ R.deleteEdges {s(v, w)}).Adj a b →
      (G \ R).Adj a b ∨ (a = v ∧ b = w) ∨ (a = w ∧ b = v) := by
    intro a b h
    rw [sdiff_adj, deleteEdges_adj] at h
    by_cases he : s(a, b) = s(v, w)
    · exact Or.inr (Sym2.eq_iff.1 he)
    · left
      rw [sdiff_adj]
      exact ⟨h.1, fun h' => h.2 ⟨h', fun hm => he (Set.mem_singleton_iff.1 hm)⟩⟩
  have hdeg : ∀ x, ((G \ R.deleteEdges {s(v, w)}).neighborSet x).ncard ≤ 2 := by
    intro x
    by_cases hxv : x = v
    · subst hxv
      have hsub : (G \ R.deleteEdges {s(x, w)}).neighborSet x ⊆
          insert w ((G \ R).neighborSet x) := by
        intro y hy
        rcases hB' x y hy with h | ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Set.mem_insert_of_mem _ h
        · rw [h2]; exact Set.mem_insert _ _
        · exact absurd h1 hne
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := Set.ncard_insert_le w ((G \ R).neighborSet x)
      omega
    by_cases hxw : x = w
    · subst hxw
      have hsub : (G \ R.deleteEdges {s(v, x)}).neighborSet x ⊆
          insert v ((G \ R).neighborSet x) := by
        intro y hy
        rcases hB' x y hy with h | ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Set.mem_insert_of_mem _ h
        · exact absurd h1.symm hne
        · rw [h2]; exact Set.mem_insert _ _
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := Set.ncard_insert_le v ((G \ R).neighborSet x)
      omega
    have hsub : (G \ R.deleteEdges {s(v, w)}).neighborSet x ⊆ (G \ R).neighborSet x := by
      intro y hy
      rcases hB' x y hy with h | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h
      · exact absurd h1 hxv
      · exact absurd h1 hxw
    exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (hR.2 x).2
  have hvalid : Valid G (R.deleteEdges {s(v, w)}) :=
    ⟨le_trans hR'R hR.1, fun x =>
      ⟨le_trans (Set.ncard_le_ncard (fun y hy => hR'R hy) (Set.toFinite _)) (hR.2 x).1,
        hdeg x⟩⟩
  have hdel : (R.deleteEdges {s(v, w)}).Reachable v w :=
    reachable_deleteEdges_iff_exists_walk.2 ⟨p, hp⟩
  refine ⟨_, hvalid, ?_⟩
  unfold P
  have e1 : univ.filter (fun q : V × V => R.Reachable q.1 q.2) =
      univ.filter (fun q : V × V => (R.deleteEdges {s(v, w)}).Reachable q.1 q.2) :=
    Finset.filter_congr (fun q _ => ⟨fun h => reach_del hdel h,
      fun h => Reachable.mono (deleteEdges_le _) h⟩)
  have e2 : univ.filter (fun q : V × V => (G \ R).Reachable q.1 q.2) ⊂
      univ.filter (fun q : V × V => (G \ R.deleteEdges {s(v, w)}).Reachable q.1 q.2) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(v, w), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hBvw.reachable
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hnr
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact Reachable.mono hBB hq
  rw [e1]
  have := Finset.card_lt_card e2
  omega

lemma break_cycle {G R : SimpleGraph V} (hR : Valid G R)
    (h3 : ∀ y, (G.neighborSet y).ncard = 3)
    (hc : ¬ R.IsAcyclic) : ∃ R', Valid G R' ∧ P G R < P G R' := by
  rw [isAcyclic_iff_forall_adj_isBridge] at hc
  push Not at hc
  obtain ⟨v, w, hadj, hbr⟩ := hc
  rw [isBridge_iff, not_not, reachable_deleteEdges_iff_exists_walk] at hbr
  obtain ⟨p, hp⟩ := hbr
  obtain ⟨x, hxw, hvx, q, hq⟩ := two_nbrs hadj p hp
  have lowdeg : ∀ {a b c : V}, b ≠ c → R.Adj a b → R.Adj a c →
      ((G \ R).neighborSet a).ncard ≤ 1 := by
    intro a b c hbc hab hac
    have h2 : 2 ≤ (R.neighborSet a).ncard := by
      rw [← Set.ncard_pair hbc]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hab
      · exact hac
    have := split hR.1 a
    rw [h3 a] at this
    omega
  have hv : ((G \ R).neighborSet v).ncard ≤ 1 := lowdeg hxw.symm hadj hvx
  obtain ⟨y, hyv, hwy, -, -⟩ := two_nbrs hadj.symm p.reverse (by
    rw [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap]; exact hp)
  have hw : ((G \ R).neighborSet w).ncard ≤ 1 := lowdeg hyv.symm hadj.symm hwy
  obtain ⟨z, hzv, hxz, -, -⟩ := two_nbrs hvx.symm q.reverse (by
    rw [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap]; exact hq)
  have hx : ((G \ R).neighborSet x).ncard ≤ 1 := lowdeg hzv.symm hvx.symm hxz
  by_cases h1 : (G \ R).Reachable v w
  · by_cases h2 : (G \ R).Reachable v x
    · exact (three_ends (G \ R) (fun y => (hR.2 y).2) hadj.ne hvx.ne hxw.symm hv hw hx
        h1 h2).elim
    · exact improve hR hvx q hq hv hx h2
  · exact improve hR hadj p hp hv hw h1

lemma start (G : SimpleGraph V) (h3 : ∀ y, (G.neighborSet y).ncard = 3) :
    ∃ R, Valid G R := by
  have hcard : ∀ y, (G.neighborFinset y).card = 3 := fun y => by
    have := Set.ncard_coe_finset (G.neighborFinset y)
    rw [coe_neighborFinset] at this
    rw [← this, h3 y]
  obtain ⟨g, hg, hgadj⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun y => G.neighborFinset y)).1 (by
    intro s
    have := Finset.card_mul_le_card_mul (r := G.Adj) (s := s)
      (t := s.biUnion (fun y => G.neighborFinset y)) (m := 3) (n := 3) ?_ ?_
    · omega
    · intro a ha
      have : (s.biUnion fun y => G.neighborFinset y).bipartiteAbove G.Adj a =
          G.neighborFinset a := by
        ext z
        simp only [Finset.mem_bipartiteAbove, Finset.mem_biUnion, mem_neighborFinset]
        exact ⟨fun h => h.2, fun h => ⟨⟨a, ha, h⟩, h⟩⟩
      rw [this, hcard]
    · intro b _
      calc _ ≤ (G.neighborFinset b).card := Finset.card_le_card (by
              intro z hz
              rw [Finset.mem_bipartiteBelow] at hz
              rw [mem_neighborFinset]
              exact hz.2.symm)
        _ = 3 := hcard b)
  have hgs : ∀ y, G.Adj y (g y) := fun y => (mem_neighborFinset _ _ _).1 (hgadj y)
  let B : SimpleGraph V := SimpleGraph.fromRel (fun x y => g x = y)
  have hBG : B ≤ G := by
    intro x y h
    rw [fromRel_adj] at h
    rcases h.2 with h' | h'
    · rw [← h']; exact hgs x
    · rw [← h']; exact (hgs y).symm
  refine ⟨G \ B, sdiff_le, fun x => ⟨?_, ?_⟩⟩
  · have hpos : 0 < (B.neighborSet x).ncard := by
      refine (Set.ncard_pos (Set.toFinite _)).2 ⟨g x, ?_⟩
      rw [mem_neighborSet, fromRel_adj]
      exact ⟨(hgs x).ne, Or.inl rfl⟩
    have := split hBG x
    rw [h3 x] at this
    omega
  · rw [sdsd hBG]
    obtain ⟨u, hu⟩ := hg.bijective_of_finite.2 x
    have hsub : B.neighborSet x ⊆ {g x, u} := by
      intro y hy
      rw [mem_neighborSet, fromRel_adj] at hy
      rcases hy.2 with h' | h'
      · rw [← h']; exact Set.mem_insert _ _
      · have : y = u := hg (h'.trans hu.symm)
        rw [this]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    calc _ ≤ ({g x, u} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({u} : Set V).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]

lemma upper (G : SimpleGraph V) (h3 : ∀ y, (G.neighborSet y).ncard = 3) :
    ∃ R, Valid G R ∧ R.IsAcyclic ∧ (G \ R).IsAcyclic := by
  obtain ⟨R0, hR0⟩ := start G h3
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image (Finset.univ.filter (Valid G)) (P G)
    ⟨R0, by simpa using hR0⟩
  have hR : Valid G R := by simpa using hRmem
  have noimp : ∀ R', Valid G R' → ¬ P G R < P G R' := fun R' hR' hlt =>
    absurd (hRmax R' (by simpa using hR')) (not_le.2 hlt)
  refine ⟨R, hR, ?_, ?_⟩
  · by_contra hc
    obtain ⟨R', h1, h2⟩ := break_cycle hR h3 hc
    exact noimp R' h1 h2
  · by_contra hc
    have hP : P G (G \ R) = P G R := by unfold P; rw [sdsd hR.1, add_comm]
    obtain ⟨R', h1, h2⟩ := break_cycle (valid_swap hR) h3 hc
    exact noimp R' h1 (hP ▸ h2)

end LAC

open SimpleGraph in
theorem linear_arboricity_conjecture.variants.cubic {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : ∀ v, G.degree v = 3) :
    linearArboricity G = 2 := by
  have h3 : ∀ y, (G.neighborSet y).ncard = 3 := fun y => by
    rw [← coe_neighborFinset, Set.ncard_coe_finset, card_neighborFinset_eq_degree]
    exact hreg y
  classical
  have hdec : HasLinearForestDecomposition G 2 := by
    obtain ⟨R, hR, hRa, hBa⟩ := LAC.upper G h3
    refine ⟨![R, G \ R], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨⟨hRa, fun x => (hR.2 x).1⟩, hR.1⟩
      · exact ⟨⟨hBa, fun x => (hR.2 x).2⟩, sdiff_le⟩
    · intro u v
      constructor
      · intro h
        by_cases hr : R.Adj u v
        · refine ⟨0, hr, ?_⟩
          intro j hj
          fin_cases j
          · rfl
          · have hj' : (G \ R).Adj u v := hj
            rw [sdiff_adj] at hj'
            exact absurd hr hj'.2
        · refine ⟨1, (show (G \ R).Adj u v by rw [sdiff_adj]; exact ⟨h, hr⟩), ?_⟩
          intro j hj
          fin_cases j
          · exact absurd hj hr
          · rfl
      · rintro ⟨i, hi, _⟩
        fin_cases i
        · exact hR.1 hi
        · have hi' : (G \ R).Adj u v := hi
          rw [sdiff_adj] at hi'
          exact hi'.1
  have lower : ∀ k ∈ {k | HasLinearForestDecomposition G k}, 2 ≤ k := by
    rintro k ⟨D, hD, hE⟩
    by_contra hk
    obtain ⟨v⟩ := ‹Nonempty V›
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · obtain ⟨w, hw⟩ : (G.neighborSet v).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by rw [h3 v]; omega)
      obtain ⟨i, _⟩ := (hE v w).1 hw
      exact i.elim0
    · have hsub : G.neighborSet v ⊆ (D 0).neighborSet v := by
        intro w hw
        obtain ⟨i, hi, _⟩ := (hE v w).1 hw
        have : i = 0 := Subsingleton.elim _ _
        rw [this] at hi
        exact hi
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := (hD 0).1.2 v
      rw [h3 v] at *
      omega
  exact le_antisymm (Nat.sInf_le hdec) (le_csInf ⟨2, hdec⟩ lower)

end LinearArboricityConjecture

#print axioms LinearArboricityConjecture.linear_arboricity_conjecture.variants.cubic
