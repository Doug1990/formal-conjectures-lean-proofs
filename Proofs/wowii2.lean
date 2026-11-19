import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean and Independence.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Average of `indepNeighbors` over all vertices. -/
noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture2

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

omit [DecidableEq V] in
/-- In a tree, `deg u + deg v ≤ #leaves + 2` for distinct `u, v`. -/
lemma leaf_bound [Nontrivial V] (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    {u v : V} (huv : u ≠ v) :
    T.degree u + T.degree v ≤ (univ.filter (fun x => T.degree x = 1)).card + 2 := by
  classical
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
/-- An independent set of size `l(v)` inside `N(v)`. -/
lemma nbhd_indep (G : SimpleGraph V) (v : V) : ∃ I : Finset V, I.card = indepNeighborsCard G v ∧
    (∀ a ∈ I, G.Adj v a) ∧ (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) := by
  classical
  obtain ⟨J, hJ⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  refine ⟨J.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · rw [Finset.card_map, hJ.card_eq]; rfl
  · intro a ha
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.1 ha
    exact a'.2
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
    exact hJ.isIndepSet ha' hb' (fun h => hab.ne (by rw [h])) hab

/-- Triangle-freeness, in elementary form. -/
def TF (H : SimpleGraph V) : Prop := ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj a c

omit [Fintype V] [DecidableEq V] in
/-- The double star on an edge `uv` of a triangle-free graph is acyclic. -/
lemma dstar_acyclic (H : SimpleGraph V) (hH : TF H) {u v : V} (huv : H.Adj u v) :
    (SimpleGraph.fromRel (fun p q => (p = u ∧ H.Adj u q) ∨ (p = v ∧ H.Adj v q))).IsAcyclic := by
  set F := SimpleGraph.fromRel (fun p q => (p = u ∧ H.Adj u q) ∨ (p = v ∧ H.Adj v q)) with hF
  have hne : u ≠ v := H.ne_of_adj huv
  have hFadj : ∀ x y, F.Adj x y ↔ x ≠ y ∧ (((x = u ∧ H.Adj u y) ∨ (x = v ∧ H.Adj v y)) ∨
      ((y = u ∧ H.Adj u x) ∨ (y = v ∧ H.Adj v x))) := fun x y => by
    rw [hF, fromRel_adj]
  -- edge from a centre `c` (the other centre being `c'`) to a leaf `q ≠ c'`
  have leafB : ∀ c c', (c = u ∧ c' = v ∨ c = v ∧ c' = u) → ∀ q, H.Adj c q → q ≠ c' →
      F.IsBridge s(c, q) := by
    intro c c' hcc q hq hqc
    have hcc' : H.Adj c c' := by
      rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    have hab : F.Adj c q := by
      rw [hFadj]
      refine ⟨H.ne_of_adj hq, Or.inl ?_⟩
      rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, hq⟩
      · exact Or.inr ⟨rfl, hq⟩
    refine bridge_cut hab {z | z ≠ q} (H.ne_of_adj hq) (by simp) ?_
    intro x y hxy hx hy
    simp only [Set.mem_ofPred_eq, not_not] at hx hy
    subst hy
    have hqc0 : y ≠ c := (H.ne_of_adj hq).symm
    -- the neighbours of y in F are centres; y is not a centre
    have hyu : y ≠ u ∧ y ≠ v := by
      rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hqc0, hqc⟩
      · exact ⟨hqc, hqc0⟩
    rw [hFadj] at hxy
    rcases hxy with ⟨-, (⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨h, -⟩ | ⟨h, -⟩)⟩
    · rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd h (hH _ _ _ hcc'.symm hq)
    · rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd h (hH _ _ _ hcc'.symm hq)
      · rfl
    · exact absurd h hyu.1
    · exact absurd h hyu.2
  have hmid : F.IsBridge s(u, v) := by
    have hab : F.Adj u v := (hFadj u v).2 ⟨hne, Or.inl (Or.inl ⟨rfl, huv⟩)⟩
    refine bridge_cut hab {z | z = u ∨ (H.Adj u z ∧ z ≠ v)} (Or.inl rfl)
      (by simp [hne.symm]) ?_
    intro x y hxy hx hy
    simp only [Set.mem_ofPred_eq, not_or, not_and, not_not] at hx hy
    rw [hFadj] at hxy
    rcases hxy with ⟨hxy0, (⟨h, h'⟩ | ⟨h, h'⟩) | (⟨h, h'⟩ | ⟨h, h'⟩)⟩
    · rw [h, hy.2 (h ▸ h')]
    · rcases hx with h2 | ⟨-, h2⟩
      · exact absurd (h2.symm.trans h) hne
      · exact absurd h h2
    · exact absurd h hy.1
    · rcases hx with h2 | ⟨h1, -⟩
      · rw [h2, h]
      · exact absurd huv (hH _ _ _ h1 h'.symm)
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  obtain ⟨hab0, h⟩ := (hFadj a b).1 hab
  rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h⟩ | ⟨rfl, h⟩)
  · by_cases hb : b = v
    · subst hb; exact hmid
    · exact leafB _ v (Or.inl ⟨rfl, rfl⟩) b h hb
  · by_cases hb : b = u
    · subst hb; rw [Sym2.eq_swap]; exact hmid
    · exact leafB _ u (Or.inr ⟨rfl, rfl⟩) b h hb
  · rw [Sym2.eq_swap]
    by_cases ha : a = v
    · subst ha; exact hmid
    · exact leafB _ v (Or.inl ⟨rfl, rfl⟩) a h ha
  · rw [Sym2.eq_swap]
    by_cases ha : a = u
    · subst ha; rw [Sym2.eq_swap]; exact hmid
    · exact leafB _ u (Or.inr ⟨rfl, rfl⟩) a h ha

omit [Fintype V] [DecidableEq V] in
lemma H'adj (H : SimpleGraph V) (v : V) (I : Finset V) (hvI : v ∉ I) (x y : V) :
    (SimpleGraph.fromRel (fun x y => (H.Adj x y ∧ x ≠ v ∧ y ≠ v) ∨ (x = v ∧ y ∈ I))).Adj x y ↔
    (H.Adj x y ∧ x ≠ v ∧ y ≠ v) ∨ (x = v ∧ y ∈ I) ∨ (y = v ∧ x ∈ I) := by
  rw [fromRel_adj]
  constructor
  · rintro ⟨-, (h | h) | (⟨h1, h2, h3⟩ | h)⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h1.symm, h3, h2⟩
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨H.ne_of_adj h.1, Or.inl (Or.inl h)⟩
    · exact ⟨fun e => hvI (by rw [← h.1, e]; exact h.2), Or.inl (Or.inr h)⟩
    · exact ⟨fun e => hvI (by rw [← h.1, ← e]; exact h.2), Or.inr (Or.inr h)⟩

/-- In an edge-maximal triangle-free subgraph `H ≤ G`, `l(v) ≤ deg_H v`. -/
lemma switch (G H : SimpleGraph V) [DecidableRel H.Adj] (hHG : H ≤ G) (hH : TF H)
    (hmax : ∀ H' : SimpleGraph V, H' ≤ G → TF H' → H'.edgeSet.ncard ≤ H.edgeSet.ncard)
    (v : V) (I : Finset V) (hIv : ∀ a ∈ I, G.Adj v a) (hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) :
    I.card ≤ H.degree v := by
  classical
  have hvI : v ∉ I := fun h => G.irrefl (hIv v h)
  set H' := SimpleGraph.fromRel (fun x y => (H.Adj x y ∧ x ≠ v ∧ y ≠ v) ∨ (x = v ∧ y ∈ I))
    with hH'
  have hA := H'adj H v I hvI
  have h1 : H' ≤ G := by
    intro x y hxy
    rcases (hA x y).1 hxy with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact hHG h.1
    · exact hIv y h
    · exact (hIv x h).symm
  have hv : ∀ y, H'.Adj v y → y ∈ I := by
    intro y hy
    rcases (hA v y).1 hy with h | ⟨-, h⟩ | ⟨-, h'⟩
    · exact absurd rfl h.2.1
    · exact h
    · exact absurd h' hvI
  have hne : ∀ x y, x ≠ v → y ≠ v → H'.Adj x y → H.Adj x y := by
    intro x y hx hy hxy
    rcases (hA x y).1 hxy with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h.1
    · exact absurd h hx
    · exact absurd h hy
  have hIv' : ∀ x ∈ I, x ≠ v := fun x hx e => hvI (e ▸ hx)
  have h2 : TF H' := by
    intro a b c hab hbc hac
    by_cases ha : a = v
    · rw [ha] at hab hac
      have hb := hv b hab
      have hc := hv c hac
      exact hI b hb c hc (hHG (hne b c (hIv' b hb) (hIv' c hc) hbc))
    by_cases hb : b = v
    · rw [hb] at hab hbc
      have ha' := hv a hab.symm
      have hc := hv c hbc
      exact hI a ha' c hc (hHG (hne a c ha (hIv' c hc) hac))
    by_cases hc : c = v
    · rw [hc] at hac hbc
      have ha' := hv a hac.symm
      have hb' := hv b hbc.symm
      exact hI a ha' b hb' (hHG (hne a b ha hb hab))
    exact hH a b c (hne a b ha hb hab) (hne b c hb hc hbc) (hne a c ha hc hac)
  have hm := hmax H' h1 h2
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← coe_edgeFinset, Set.ncard_coe_finset] at hm
  set A := H.edgeFinset \ H.incidenceFinset v with hAdef
  set B := I.image (fun a => s(v, a)) with hB
  have hsub : A ∪ B ⊆ H'.edgeFinset := by
    intro e he
    rcases mem_union.1 he with he | he
    · rw [hAdef, mem_sdiff, mem_edgeFinset, mem_incidenceFinset] at he
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_edgeFinset, mem_edgeSet]
        have hxy : H.Adj x y := he.1
        have hnot : ¬ (v = x ∨ v = y) := fun hh => he.2 ⟨he.1, Sym2.mem_iff.2 hh⟩
        rw [not_or] at hnot
        exact (hA x y).2 (Or.inl ⟨hxy, fun e => hnot.1 e.symm, fun e => hnot.2 e.symm⟩)
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 he
      rw [mem_edgeFinset, mem_edgeSet]
      exact (hA v a).2 (Or.inr (Or.inl ⟨rfl, ha⟩))
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨a, -, rfl⟩ := mem_image.1 heB
    rw [hAdef, mem_sdiff, mem_incidenceFinset] at heA
    exact heA.2 ⟨mem_edgeFinset.1 heA.1, Sym2.mem_mk_left v a⟩
  have hBc : B.card = I.card := card_image_of_injective _ (fun a b h => Sym2.congr_right.1 h)
  have c1 := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hBc] at c1
  have c2 : H.edgeFinset.card ≤ A.card + (H.incidenceFinset v).card :=
    card_le_card_sdiff_add_card
  rw [card_incidenceFinset_eq_degree] at c2
  omega

omit [DecidableEq V] in
/-- Some edge has degree sum at least twice the average degree. -/
lemma heavy (H : SimpleGraph V) [DecidableRel H.Adj] (hD : ∑ x, H.degree x ≠ 0) :
    ∃ u v, H.Adj u v ∧ 2 * ∑ x, H.degree x ≤ (H.degree u + H.degree v) * Fintype.card V := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set D := ∑ x, H.degree x with hD'
  set n := Fintype.card V with hn
  have key : ∀ x, ∑ y ∈ H.neighborFinset x, ((H.degree x + H.degree y) * n + 1) ≤
      H.degree x * (2 * D) := by
    intro x
    calc ∑ y ∈ H.neighborFinset x, ((H.degree x + H.degree y) * n + 1)
        ≤ ∑ y ∈ H.neighborFinset x, 2 * D :=
          sum_le_sum fun y hy => hcon x y ((mem_neighborFinset _ _ _).1 hy)
      _ = H.degree x * (2 * D) := by
          rw [sum_const, card_neighborFinset_eq_degree, smul_eq_mul]
  have swap : ∑ x, ∑ y ∈ H.neighborFinset x, H.degree y = ∑ x, H.degree x * H.degree x := by
    calc ∑ x, ∑ y ∈ H.neighborFinset x, H.degree y
        = ∑ x, ∑ y, if H.Adj x y then H.degree y else 0 := by
          refine sum_congr rfl fun x _ => ?_
          rw [neighborFinset_eq_filter, sum_filter]
      _ = ∑ y, ∑ x, if H.Adj x y then H.degree y else 0 := sum_comm
      _ = ∑ y, H.degree y * H.degree y := by
          refine sum_congr rfl fun y _ => ?_
          rw [← sum_filter, sum_const, smul_eq_mul]
          congr 1
          rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
          congr 1
          ext x
          simp [adj_comm]
  have expand : ∀ x, ∑ y ∈ H.neighborFinset x, ((H.degree x + H.degree y) * n + 1) =
      H.degree x * H.degree x * n + (∑ y ∈ H.neighborFinset x, H.degree y) * n +
        H.degree x := by
    intro x
    rw [sum_add_distrib, ← sum_mul, sum_add_distrib, sum_const, sum_const,
      card_neighborFinset_eq_degree, smul_eq_mul, smul_eq_mul]
    ring
  have tot : ∑ x, (H.degree x * H.degree x * n + (∑ y ∈ H.neighborFinset x, H.degree y) * n +
      H.degree x) ≤ ∑ x, H.degree x * (2 * D) := by
    refine sum_le_sum fun x _ => ?_
    rw [← expand x]
    exact key x
  set Q := ∑ x, H.degree x * H.degree x with hQ
  have t1 : ∑ x, (H.degree x * H.degree x * n + (∑ y ∈ H.neighborFinset x, H.degree y) * n +
      H.degree x) = Q * n + Q * n + D := by
    rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, swap]
  have t2 : ∑ x, H.degree x * (2 * D) = D * (2 * D) := by rw [← sum_mul]
  rw [t1, t2] at tot
  have cs : D ^ 2 ≤ n * Q := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun x => (H.degree x : ℤ))
    rw [card_univ] at this
    have e : ∑ x, (H.degree x : ℤ) ^ 2 = ((Q : ℕ) : ℤ) := by
      rw [hQ]; push_cast; exact sum_congr rfl fun x _ => sq _
    rw [e] at this
    have e2 : ∑ x, (H.degree x : ℤ) = ((D : ℕ) : ℤ) := by rw [hD']; push_cast; rfl
    rw [e2] at this
    exact_mod_cast this
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  nlinarith

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

open scoped Classical in
theorem conjecture2 (G : SimpleGraph α) (h : G.Connected) :
  2 * (averageIndepNeighbors G - 1) ≤ Ls G := by
  classical
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image
    ((univ : Finset (SimpleGraph α)).filter (fun K => K ≤ G ∧ TF K))
    (fun K => K.edgeSet.ncard) ⟨⊥, mem_filter.2 ⟨mem_univ _, bot_le, fun a b c h => h.elim⟩⟩
  obtain ⟨hHG, hH⟩ := (mem_filter.1 hHmem).2
  have hmax : ∀ H', H' ≤ G → TF H' → H'.edgeSet.ncard ≤ H.edgeSet.ncard :=
    fun H' h1 h2 => hHmax H' (mem_filter.2 ⟨mem_univ _, h1, h2⟩)
  have hl : ∀ v, indepNeighborsCard G v ≤ H.degree v := by
    intro v
    obtain ⟨I, hIc, hIv, hI⟩ := nbhd_indep G v
    rw [← hIc]
    exact switch G H hHG hH hmax v I hIv hI
  set D := ∑ x, H.degree x with hD
  have hLD : ∑ x, indepNeighborsCard G x ≤ D := sum_le_sum fun x _ => hl x
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have havg : averageIndepNeighbors G =
      ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) / Fintype.card α := by
    unfold averageIndepNeighbors indepNeighbors
    rw [Nat.cast_sum]
  by_cases hD0 : D = 0
  · obtain ⟨T, hTG, hT⟩ := h.exists_isTree_le
    have hLs := Ls_ge G T hTG hT
    have hL0 : ∑ x, indepNeighborsCard G x = 0 := by omega
    rw [havg, hL0, Nat.cast_zero, zero_div]
    have : (0:ℝ) ≤ ((univ.filter (fun x => T.degree x = 1)).card : ℝ) := Nat.cast_nonneg _
    linarith
  · obtain ⟨u, v, huv, hbig⟩ := heavy H hD0
    set F := SimpleGraph.fromRel (fun p q => (p = u ∧ H.Adj u q) ∨ (p = v ∧ H.Adj v q))
      with hF
    have hFa : F.IsAcyclic := dstar_acyclic H hH huv
    have hFG : F ≤ G := by
      intro a b hab
      rw [hF, fromRel_adj] at hab
      rcases hab with ⟨-, (⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h⟩ | ⟨rfl, h⟩)⟩
      · exact hHG h
      · exact hHG h
      · exact (hHG h).symm
      · exact (hHG h).symm
    obtain ⟨T, hFT, hTG, hT⟩ := h.exists_isTree_le_of_le_of_isAcyclic hFG hFa
    have hu : H.neighborFinset u ⊆ T.neighborFinset u := by
      intro y hy
      rw [mem_neighborFinset] at hy ⊢
      apply hFT
      rw [hF, fromRel_adj]
      exact ⟨H.ne_of_adj hy, Or.inl (Or.inl ⟨rfl, hy⟩)⟩
    have hv : H.neighborFinset v ⊆ T.neighborFinset v := by
      intro y hy
      rw [mem_neighborFinset] at hy ⊢
      apply hFT
      rw [hF, fromRel_adj]
      exact ⟨H.ne_of_adj hy, Or.inl (Or.inr ⟨rfl, hy⟩)⟩
    have c1 := card_le_card hu
    have c2 := card_le_card hv
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at c1 c2
    have hL := leaf_bound T hT (H.ne_of_adj huv)
    have hLs := Ls_ge G T hTG hT
    have hbig' : (2 * D : ℝ) ≤ ((H.degree u + H.degree v : ℕ) : ℝ) * Fintype.card α := by
      exact_mod_cast hbig
    have hLD' : ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) ≤ D := by exact_mod_cast hLD
    have hsum : H.degree u + H.degree v ≤ (univ.filter (fun x => T.degree x = 1)).card + 2 := by
      omega
    have hsum' : ((H.degree u + H.degree v : ℕ) : ℝ) ≤
        ((univ.filter (fun x => T.degree x = 1)).card : ℝ) + 2 := by exact_mod_cast hsum
    rw [havg]
    have hq : ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) / Fintype.card α * 2 ≤
        ((H.degree u + H.degree v : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn']
      linarith
    linarith

end WrittenOnTheWallII.GraphConjecture2

#print axioms WrittenOnTheWallII.GraphConjecture2.conjecture2
