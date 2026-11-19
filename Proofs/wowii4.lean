import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean and Degrees.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e

/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture4

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A spanning tree `T ≤ G` gives `Ls G ≥ #leaves T`. -/
lemma Ls_ge (G : SimpleGraph V) [DecidableRel G.Adj] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) :
    ((univ.filter (fun x => T.degree x = 1)).card : ℝ) ≤ Ls G := by
  let T' : G.Subgraph := SimpleGraph.toSubgraph T hTG
  have hspan : T'.IsSpanning := SimpleGraph.toSubgraph.isSpanning T _
  have htree : T'.coe.IsTree :=
    (Subgraph.spanningCoeEquivCoeOfSpanning T' hspan).isTree_iff.mp hT
  unfold Ls
  refine le_trans ?_ (le_csSup ?_ (Set.mem_image_of_mem _ (?_ : T' ∈ _)))
  · beta_reduce
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    have hw1 : T.degree w = 1 := (Finset.mem_filter.mp hw).2
    have hleaf : ∃! u, T'.Adj w u := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw1
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have e : ∀ (i1 : Fintype ↑T'.verts), w ∈ @Set.toFinset _ T'.verts i1 :=
        fun i1 => Set.mem_toFinset.mpr (hspan w)
      exact e _
    · have e2 : ∀ (i2 : Fintype ↑(T'.neighborSet w)), @Subgraph.degree _ _ T' w i2 = 1 :=
        fun i2 => Subgraph.degree_eq_one_iff_existsUnique_adj.mpr hleaf
      exact e2 _
  · refine ⟨Fintype.card V, ?_⟩
    rintro _ ⟨T, -, rfl⟩
    beta_reduce
    exact_mod_cast Finset.card_le_univ _
  · exact ⟨hspan, htree⟩

/-- In a tree, `deg u + deg v ≤ #leaves + 2` for distinct `u, v`. -/
lemma leaf_bound [Nontrivial V] (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    {u v : V} (huv : u ≠ v) :
    T.degree u + T.degree v ≤ (univ.filter (fun x => T.degree x = 1)).card + 2 := by
  have hpos : ∀ x, 1 ≤ T.degree x := by
    intro x
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨q⟩ := hT.connected.preconnected x y
    cases q with
    | nil => exact absurd rfl hy
    | @cons _ z _ h _ => exact (degree_pos_iff_exists_adj T x).2 ⟨z, h⟩
  have hsum := T.sum_degrees_eq_twice_card_edges
  have hE := hT.card_edgeFinset
  set s := (univ.erase u).erase v with hs_def
  have h1 : ∑ x, T.degree x = T.degree u + (T.degree v + ∑ x ∈ s, T.degree x) := by
    rw [hs_def, ← Finset.add_sum_erase _ _ (mem_univ u),
      ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨huv.symm, mem_univ v⟩)]
  have h2 : 2 * s.card ≤ ∑ x ∈ s, T.degree x + (s.filter (fun x => T.degree x = 1)).card := by
    have : ∀ x ∈ s, 2 ≤ T.degree x + (if T.degree x = 1 then 1 else 0) := fun x _ => by
      have := hpos x
      split_ifs <;> omega
    calc 2 * s.card = ∑ _x ∈ s, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ s, (T.degree x + if T.degree x = 1 then 1 else 0) := sum_le_sum this
      _ = _ := by rw [sum_add_distrib, card_filter]
  have h3 : (s.filter (fun x => T.degree x = 1)).card ≤
      (univ.filter (fun x => T.degree x = 1)).card :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  have hc : 1 < Fintype.card V := Fintype.one_lt_card
  have hs : s.card + 2 = Fintype.card V := by
    rw [hs_def, card_erase_of_mem (mem_erase.2 ⟨huv.symm, mem_univ v⟩),
      card_erase_of_mem (mem_univ u), card_univ]
    omega
  omega

omit [Fintype V] [DecidableEq V] in
/-- An edge whose only crossing of a cut `S` is itself is a bridge. -/
lemma bridge_cut {F : SimpleGraph V} {a b : V} (_hab : F.Adj a b) (S : Set V) (ha : a ∈ S)
    (hb : b ∉ S) (h : ∀ x y, F.Adj x y → x ∈ S → y ∉ S → s(x, y) = s(a, b)) :
    F.IsBridge s(a, b) := by
  rw [isBridge_iff]
  intro hr
  have p := hr.some
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  exact hadj.2 (by simpa using h _ _ hadj.1 hd1 hd2)

omit [Fintype V] [DecidableEq V] in
/-- A connected graph with a non-edge has an induced path `u - w - v`. -/
lemma exists_P2 {G : SimpleGraph V} (hc : G.Connected) {a b : V} (hab : a ≠ b)
    (hn : ¬G.Adj a b) : ∃ u v w, u ≠ v ∧ ¬G.Adj u v ∧ G.Adj u w ∧ G.Adj w v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  cases p with
  | nil => exact absurd rfl hab
  | @cons _ x _ h1 q =>
    cases q with
    | nil => exact absurd h1 hn
    | @cons _ y _ h2 q' =>
      refine ⟨a, y, x, ?_, ?_, h1, h2⟩
      · rintro rfl
        have := dist_le q'
        simp only [Walk.length_cons] at hp
        omega
      · intro hay
        have := dist_le (Walk.cons hay q')
        simp only [Walk.length_cons] at hp this
        omega

omit [Fintype V] [DecidableEq V] in
/-- The double star `u ∪ N(u)`, `v ∪ (N(v) \ N(u)) ∪ {w}` is acyclic. -/
lemma double_star_acyclic (G : SimpleGraph V) {u v w : V} (huv : u ≠ v) (hnuv : ¬G.Adj u v)
    (huw : G.Adj u w) (hwv : G.Adj w v) :
    (SimpleGraph.fromRel (fun p q => (p = u ∧ G.Adj u q) ∨
      (p = v ∧ (q = w ∨ (G.Adj v q ∧ ¬G.Adj u q))))).IsAcyclic := by
  set F := SimpleGraph.fromRel (fun p q => (p = u ∧ G.Adj u q) ∨
      (p = v ∧ (q = w ∨ (G.Adj v q ∧ ¬G.Adj u q)))) with hF
  have hvu : ¬G.Adj v u := fun h => hnuv h.symm
  have huu : ¬G.Adj u u := G.irrefl
  have hvv : ¬G.Adj v v := G.irrefl
  have huw' : u ≠ w := G.ne_of_adj huw
  have hvw' : v ≠ w := (G.ne_of_adj hwv).symm
  have hvw : G.Adj v w := hwv.symm
  have hFadj : ∀ x y, F.Adj x y ↔ x ≠ y ∧ (((x = u ∧ G.Adj u y) ∨
      (x = v ∧ (y = w ∨ (G.Adj v y ∧ ¬G.Adj u y)))) ∨ ((y = u ∧ G.Adj u x) ∨
      (y = v ∧ (x = w ∨ (G.Adj v x ∧ ¬G.Adj u x))))) := fun x y => by
    rw [hF, fromRel_adj]
  have key : ∀ a b, a ≠ b → ((a = u ∧ G.Adj u b) ∨
      (a = v ∧ (b = w ∨ (G.Adj v b ∧ ¬G.Adj u b)))) → F.IsBridge s(a, b) := by
    intro a b hne hR
    have hab : F.Adj a b := (hFadj a b).2 ⟨hne, Or.inl hR⟩
    rcases hR with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · by_cases hbw : b = w
      · subst hbw
        refine bridge_cut hab {z | z = a ∨ (G.Adj a z ∧ z ≠ b)} (Or.inl rfl)
          (by simp [hne.symm]) ?_
        intro x y hxy hx hy
        simp only [Set.mem_ofPred_eq, not_or, not_and, not_not] at hx hy
        rw [hFadj] at hxy
        rcases hx with rfl | ⟨hx1, hx2⟩
        · rcases hxy with ⟨hne', (⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, h'⟩)⟩
          · rw [hy.2 h]
          · exact absurd h huv
          · exact absurd h hy.1
          · subst h
            rcases h' with h' | ⟨h', -⟩
            · exact absurd h' hne
            · exact absurd h' hvu
        · rcases hxy with ⟨hne', (⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, h'⟩)⟩
          · exact absurd h (G.ne_of_adj hx1).symm
          · subst h; exact absurd hx1 hnuv
          · exact absurd h hy.1
          · rcases h' with h' | ⟨-, h'⟩
            · exact absurd h' hx2
            · exact absurd hx1 h'
      · refine bridge_cut hab {z | z ≠ b} hne (by simp) ?_
        intro x y hxy hx hy
        simp only [Set.mem_ofPred_eq, not_not] at hx hy
        subst hy
        rw [hFadj] at hxy
        rcases hxy with ⟨hne', (⟨h, -⟩ | ⟨h, h'⟩) | (⟨h, -⟩ | ⟨h, -⟩)⟩
        · rw [h]
        · rcases h' with h' | ⟨-, h'⟩
          · exact absurd h' hbw
          · exact absurd hb h'
        · exact absurd h (G.ne_of_adj hb).symm
        · subst h; exact absurd hb hnuv
    · by_cases hbw : b = w
      · subst hbw
        refine bridge_cut hab {z | z = a ∨ (z ≠ b ∧ G.Adj a z ∧ ¬G.Adj u z)} (Or.inl rfl)
          (by simp [hne.symm]) ?_
        intro x y hxy hx hy
        simp only [Set.mem_ofPred_eq, not_or, not_and, not_not] at hx hy
        rw [hFadj] at hxy
        rcases hx with rfl | ⟨hx1, hx2, hx3⟩
        · rcases hxy with ⟨hne', (⟨h, -⟩ | ⟨-, h⟩) | (⟨h, h'⟩ | ⟨h, -⟩)⟩
          · exact absurd h huv.symm
          · rcases h with h | ⟨h1, h2⟩
            · rw [h]
            · by_cases hyb : y = b
              · rw [hyb]
              · exact absurd (hy.2 hyb h1) h2
          · subst h; exact absurd h' hnuv
          · exact absurd h hy.1
        · rcases hxy with ⟨hne', (⟨h, -⟩ | ⟨h, -⟩) | (⟨h, h'⟩ | ⟨h, -⟩)⟩
          · subst h; exact absurd hx2 hvu
          · subst h; exact absurd hx2 hvv
          · subst h; exact absurd h' hx3
          · exact absurd h hy.1
      · rcases hb with hb | ⟨hb1, hb2⟩
        · exact absurd hb hbw
        refine bridge_cut hab {z | z ≠ b} hne (by simp) ?_
        intro x y hxy hx hy
        simp only [Set.mem_ofPred_eq, not_not] at hx hy
        subst hy
        rw [hFadj] at hxy
        rcases hxy with ⟨hne', (⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)⟩
        · exact absurd h hb2
        · rw [h]
        · subst h; exact absurd hb1 hvu
        · subst h; exact absurd hb1 hvv
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  obtain ⟨hne, h | h⟩ := (hFadj a b).1 hab
  · exact key a b hne h
  · rw [Sym2.eq_swap]
    exact key b a hne.symm h

theorem conjecture4 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (h_conn : G.Connected) :
    NG G - 1 ≤ Ls G := by
  by_cases h : (compl G).edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := h
    induction e using Sym2.ind with
    | h a b =>
    rw [mem_edgeFinset, mem_edgeSet, compl_adj] at he
    obtain ⟨u, v, w, huv, hnuv, huw, hwv⟩ := exists_P2 h_conn he.1 he.2
    have he' : s(u, v) ∈ (compl G).edgeFinset := by
      rw [mem_edgeFinset, mem_edgeSet, compl_adj]
      exact ⟨huv, hnuv⟩
    have hNG : NG G ≤ ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) := by
      unfold NG
      dsimp only
      rw [dif_pos ⟨_, he'⟩]
      have := Finset.min'_le _ _ (Finset.mem_image_of_mem (non_edge_neighborhood_card G) he')
      simp only [non_edge_neighborhood_card, Sym2.lift_mk] at this
      exact_mod_cast this
    set F := SimpleGraph.fromRel (fun p q => (p = u ∧ G.Adj u q) ∨
      (p = v ∧ (q = w ∨ (G.Adj v q ∧ ¬G.Adj u q)))) with hF
    have hFa : F.IsAcyclic := double_star_acyclic G huv hnuv huw hwv
    have hFG : F ≤ G := by
      have hR : ∀ a b, ((a = u ∧ G.Adj u b) ∨
          (a = v ∧ (b = w ∨ (G.Adj v b ∧ ¬G.Adj u b)))) → G.Adj a b := by
        rintro a b (⟨rfl, h⟩ | ⟨rfl, rfl | ⟨h, -⟩⟩)
        · exact h
        · exact hwv.symm
        · exact h
      intro a b hab
      rw [hF, fromRel_adj] at hab
      obtain ⟨-, h | h⟩ := hab
      · exact hR _ _ h
      · exact (hR _ _ h).symm
    obtain ⟨T, hFT, hTG, hT⟩ := h_conn.exists_isTree_le_of_le_of_isAcyclic hFG hFa
    classical
    have hu : G.neighborFinset u ⊆ T.neighborFinset u := by
      intro y hy
      rw [mem_neighborFinset] at hy ⊢
      apply hFT
      rw [hF, fromRel_adj]
      exact ⟨G.ne_of_adj hy, Or.inl (Or.inl ⟨rfl, hy⟩)⟩
    have hv : insert w (G.neighborFinset v \ G.neighborFinset u) ⊆ T.neighborFinset v := by
      intro y hy
      rw [mem_insert, mem_sdiff, mem_neighborFinset, mem_neighborFinset] at hy
      rw [mem_neighborFinset]
      apply hFT
      rw [hF, fromRel_adj]
      rcases hy with rfl | ⟨h1, h2⟩
      · exact ⟨G.ne_of_adj hwv.symm, Or.inl (Or.inr ⟨rfl, Or.inl rfl⟩)⟩
      · exact ⟨G.ne_of_adj h1, Or.inl (Or.inr ⟨rfl, Or.inr ⟨h1, h2⟩⟩)⟩
    have hw : w ∉ G.neighborFinset v \ G.neighborFinset u := by
      rw [mem_sdiff, mem_neighborFinset, mem_neighborFinset]
      exact fun h => h.2 huw
    have c1 := card_le_card hu
    have c2 := card_le_card hv
    rw [card_insert_of_notMem hw] at c2
    have c3 := card_sdiff_add_card (G.neighborFinset v) (G.neighborFinset u)
    rw [union_comm] at c3
    have hL := leaf_bound T hT huv
    have hLs := Ls_ge G T hTG hT
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at *
    have hN : (G.neighborFinset u ∪ G.neighborFinset v).card ≤
        (univ.filter (fun x => T.degree x = 1)).card + 1 := by omega
    have hN' : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤
        ((univ.filter (fun x => T.degree x = 1)).card : ℝ) + 1 := by exact_mod_cast hN
    linarith
  · have hNG : NG G = (Fintype.card V : ℝ) := by
      unfold NG
      dsimp only
      rw [dif_neg h]
    have hall : ∀ a b, a ≠ b → G.Adj a b := by
      intro a b hab
      by_contra hn
      apply h
      refine ⟨s(a, b), ?_⟩
      rw [mem_edgeFinset, mem_edgeSet, compl_adj]
      exact ⟨hab, hn⟩
    obtain ⟨r, -⟩ := exists_pair_ne V
    have hSG : starGraph r ≤ G := fun a b hab => hall a b ((starGraph_adj).1 hab).1
    have hLs := Ls_ge G (starGraph r) hSG (isTree_starGraph r)
    have hsub : univ.erase r ⊆ univ.filter (fun x => (starGraph r).degree x = 1) := by
      intro x hx
      rw [mem_filter]
      exact ⟨mem_univ x, degree_starGraph_of_ne_center (mem_erase.1 hx).1⟩
    have c := card_le_card hsub
    rw [card_erase_of_mem (mem_univ r), card_univ] at c
    have hc : 1 ≤ Fintype.card V := Fintype.card_pos
    have c' : ((Fintype.card V - 1 : ℕ) : ℝ) ≤
        ((univ.filter (fun x => (starGraph r).degree x = 1)).card : ℝ) := by exact_mod_cast c
    rw [Nat.cast_sub hc, Nat.cast_one] at c'
    linarith

end WrittenOnTheWallII.GraphConjecture4

#print axioms WrittenOnTheWallII.GraphConjecture4.conjecture4
