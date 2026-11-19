import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean, Temperature.lean and Domination.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

noncomputable def temp_v (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℝ :=
  let n := Fintype.card α
  let deg := G.degree v
  if n = deg then 0 else (deg : ℝ) / ((n : ℝ) - (deg : ℝ))

noncomputable def MaxTemp (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α] : ℝ :=
  let temps := Finset.univ.image (temp_v G)
  temps.max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

@[mk_iff]
structure IsNIndepDominatingSet (G : SimpleGraph α) (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}

end SimpleGraph

universe u

namespace WrittenOnTheWallII.GraphConjecture3

open SimpleGraph Finset

variable {α : Type u} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- A spanning tree `T ≤ G` gives `Ls G ≥ #leaves T` (copied from results/wowii4.lean). -/
lemma Ls_ge (G : SimpleGraph α) [DecidableRel G.Adj] (T : SimpleGraph α) [DecidableRel T.Adj]
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
  · refine ⟨Fintype.card α, ?_⟩
    rintro _ ⟨T, -, rfl⟩
    beta_reduce
    exact_mod_cast Finset.card_le_univ _
  · exact ⟨hspan, htree⟩

/-- In a tree, every degree is at most the number of leaves. -/
lemma leaf_bound1 [Nontrivial α] (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (u : α) : T.degree u ≤ (univ.filter (fun x => T.degree x = 1)).card := by
  have hpos : ∀ x, 1 ≤ T.degree x := by
    intro x
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨q⟩ := hT.connected.preconnected x y
    cases q with
    | nil => exact absurd rfl hy
    | @cons _ z _ h _ => exact (degree_pos_iff_exists_adj T x).2 ⟨z, h⟩
  have hsum := T.sum_degrees_eq_twice_card_edges
  have hE := hT.card_edgeFinset
  set s := univ.erase u with hs_def
  have h1 : ∑ x, T.degree x = T.degree u + ∑ x ∈ s, T.degree x := by
    rw [hs_def, ← Finset.add_sum_erase _ _ (mem_univ u)]
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
  have hc : 1 < Fintype.card α := Fintype.one_lt_card
  have hs : s.card + 1 = Fintype.card α := by
    rw [hs_def, card_erase_of_mem (mem_univ u), card_univ]
    omega
  omega

omit [Fintype α] [DecidableEq α] in
/-- An edge whose only crossing of a cut `S` is itself is a bridge. -/
lemma bridge_cut {F : SimpleGraph α} {a b : α} (S : Set α) (ha : a ∈ S)
    (hb : b ∉ S) (h : ∀ x y, F.Adj x y → x ∈ S → y ∉ S → s(x, y) = s(a, b)) :
    F.IsBridge s(a, b) := by
  rw [isBridge_iff]
  intro hr
  have p := hr.some
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  exact hadj.2 (by simpa using h _ _ hadj.1 hd1 hd2)

omit [Fintype α] [DecidableEq α] in
/-- The star of `G` at `v` is acyclic. -/
lemma star_acyclic (G : SimpleGraph α) (v : α) :
    (SimpleGraph.fromRel (fun p q => p = v ∧ G.Adj v q)).IsAcyclic := by
  set F := SimpleGraph.fromRel (fun p q => p = v ∧ G.Adj v q) with hF
  have hFadj : ∀ x y, F.Adj x y ↔ x ≠ y ∧ ((x = v ∧ G.Adj v y) ∨ (y = v ∧ G.Adj v x)) :=
    fun x y => by rw [hF, fromRel_adj]
  have key : ∀ b, G.Adj v b → F.IsBridge s(v, b) := by
    intro b hb
    refine bridge_cut {z | z ≠ b} (G.ne_of_adj hb) (by simp) ?_
    intro x y hxy hx hy
    simp only [Set.mem_ofPred_eq, not_not] at hx hy
    subst hy
    rw [hFadj] at hxy
    rcases hxy with ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
    · rw [h]
    · exact absurd h (G.ne_of_adj hb).symm
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  obtain ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ := (hFadj a b).1 hab
  · exact key b h
  · rw [Sym2.eq_swap]
    exact key a h

/-- `deg v ≤ Ls G` in a connected graph with at least two vertices. -/
lemma deg_le_Ls [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hc : G.Connected)
    (v : α) : (G.degree v : ℝ) ≤ Ls G := by
  set F := SimpleGraph.fromRel (fun p q => p = v ∧ G.Adj v q) with hF
  have hFG : F ≤ G := by
    intro a b hab
    rw [hF, fromRel_adj] at hab
    obtain ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ := hab
    · exact h
    · exact h.symm
  obtain ⟨T, hFT, hTG, hT⟩ := hc.exists_isTree_le_of_le_of_isAcyclic hFG (star_acyclic G v)
  classical
  have hu : G.neighborFinset v ⊆ T.neighborFinset v := by
    intro y hy
    rw [mem_neighborFinset] at hy ⊢
    apply hFT
    rw [hF, fromRel_adj]
    exact ⟨G.ne_of_adj hy, Or.inl ⟨rfl, hy⟩⟩
  have c1 := card_le_card hu
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at c1
  have hL := leaf_bound1 T hT v
  have hLs := Ls_ge G T hTG hT
  have : (G.degree v : ℝ) ≤ ((univ.filter (fun x => T.degree x = 1)).card : ℝ) := by
    exact_mod_cast c1.trans hL
  linarith

/-- `i(G) ≤ n − deg v` for every vertex `v`. -/
lemma indep_dom_le (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    G.indepDominationNumber ≤ Fintype.card α - G.degree v := by
  classical
  set C := (univ : Finset (Finset α)).filter
    (fun S : Finset α => v ∈ S ∧ G.IsIndepSet (S : Set α)) with hC
  have hne : C.Nonempty := ⟨{v}, by simp [hC]⟩
  obtain ⟨D, hD, hmax⟩ := C.exists_max_image Finset.card hne
  rw [hC, mem_filter] at hD
  obtain ⟨-, hvD, hind⟩ := hD
  have hdom : G.IsDominating (D : Set α) := by
    intro w
    by_contra hw
    push Not at hw
    obtain ⟨hwD, hadj⟩ := hw
    have hwD' : w ∉ D := by simpa using hwD
    have hins : insert w D ∈ C := by
      rw [hC, mem_filter]
      refine ⟨mem_univ _, mem_insert_of_mem hvD, ?_⟩
      rw [coe_insert]
      unfold IsIndepSet at hind ⊢
      rw [Set.pairwise_insert]
      exact ⟨hind, fun x hx _ => ⟨hadj x hx, fun h => hadj x hx h.symm⟩⟩
    have := hmax _ hins
    rw [card_insert_of_notMem hwD'] at this
    omega
  have hdisj : Disjoint D (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro x hx hxn
    rw [mem_neighborFinset] at hxn
    exact hind (mem_coe.2 hvD) (mem_coe.2 hx) (G.ne_of_adj hxn) hxn
  have hcard : D.card + G.degree v ≤ Fintype.card α := by
    rw [← card_neighborFinset_eq_degree, ← card_union_of_disjoint hdisj]
    exact card_le_univ _
  have hle : G.indepDominationNumber ≤ D.card :=
    Nat.sInf_le ⟨D, ⟨hind, hdom, rfl⟩⟩
  omega

theorem conjecture3 {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    G.indepDominationNumber * MaxTemp G ≤ Ls G := by
  have hmem := Finset.max'_mem (Finset.univ.image (temp_v G))
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hmem
  have hMT : MaxTemp G = temp_v G v := by
    unfold MaxTemp
    exact hv.symm
  rw [hMT]
  have hlt : G.degree v < Fintype.card α := G.degree_lt_card_verts v
  have hT : temp_v G v = (G.degree v : ℝ) / ((Fintype.card α : ℝ) - (G.degree v : ℝ)) := by
    unfold temp_v
    dsimp only
    rw [if_neg (by omega)]
  rw [hT]
  have hi := indep_dom_le G v
  have hi' : (G.indepDominationNumber : ℝ) ≤ (Fintype.card α : ℝ) - (G.degree v : ℝ) := by
    have : G.indepDominationNumber + G.degree v ≤ Fintype.card α := by omega
    have : ((G.indepDominationNumber + G.degree v : ℕ) : ℝ) ≤ (Fintype.card α : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) - (G.degree v : ℝ) := by
    have : ((G.degree v : ℕ) : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hlt
    linarith
  have hd0 : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg _
  have h1 : (G.indepDominationNumber : ℝ) *
      ((G.degree v : ℝ) / ((Fintype.card α : ℝ) - (G.degree v : ℝ))) ≤ G.degree v := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  exact h1.trans (deg_le_Ls G h_conn v)

end WrittenOnTheWallII.GraphConjecture3

#print axioms WrittenOnTheWallII.GraphConjecture3.conjecture3
