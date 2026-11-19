import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean and Independence.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture7

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

/-- The graph of `G`-edges inside `S`. -/
def K (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- `S`-internal edges plus one chosen edge `c v — v` for every `v ∉ S`. -/
def Hc (G : SimpleGraph V) (S : Finset V) (c : V → V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ((a ∈ S ∧ b ∈ S) ∨ (a ∉ S ∧ b = c a) ∨ (b ∉ S ∧ a = c b))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    rcases h.2 with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- A connected dominating set `S` gives `Ls G ≥ n - |S|`. -/
lemma tree_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (s : V) (hs : s ∈ S)
    (hreach : ∀ v ∈ S, (K G S).Reachable s v) (hdom : ∀ v, v ∈ S ∨ ∃ t ∈ S, G.Adj t v) :
    (Fintype.card V : ℝ) - S.card ≤ Ls G := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : V → V, ∀ v, v ∉ S → c v ∈ S ∧ G.Adj (c v) v :=
    ⟨fun v => if h : ∃ t ∈ S, G.Adj t v then h.choose else s, fun v hv => by
      have h := (hdom v).resolve_left hv
      dsimp only
      rw [dif_pos h]
      exact h.choose_spec⟩
  have hHG : Hc G S c ≤ G := fun _ _ h => h.1
  have hKH : K G S ≤ Hc G S c := fun a b h => ⟨h.1, Or.inl ⟨h.2.1, h.2.2⟩⟩
  have hr : ∀ v, (Hc G S c).Reachable s v := by
    intro v
    by_cases hv : v ∈ S
    · exact (hreach v hv).mono hKH
    · obtain ⟨h1, h2⟩ := hc v hv
      exact ((hreach _ h1).mono hKH).trans
        (Adj.reachable ⟨h2, Or.inr (Or.inr ⟨hv, rfl⟩)⟩)
  have : Nonempty V := ⟨s⟩
  have hconn : (Hc G S c).Connected := ⟨fun u v => (hr u).symm.trans (hr v)⟩
  obtain ⟨T, hTH, hT⟩ := hconn.exists_isTree_le
  have hleaf : ∀ v, v ∉ S → T.degree v = 1 := by
    intro v hv
    apply le_antisymm
    · have hsub : T.neighborFinset v ⊆ {c v} := by
        intro b hb
        rw [mem_neighborFinset] at hb
        have hb' := hTH hb
        rcases hb'.2 with h | h | h
        · exact absurd h.1 hv
        · rw [mem_singleton]; exact h.2
        · exact absurd (by rw [h.2]; exact (hc b h.1).1) hv
      rw [← card_neighborFinset_eq_degree]
      exact (card_le_card hsub).trans (card_singleton _).le
    · have hvs : v ≠ s := fun h => hv (h ▸ hs)
      obtain ⟨q⟩ := hT.connected.preconnected v s
      cases q with
      | nil => exact absurd rfl hvs
      | @cons _ z _ h _ => exact (degree_pos_iff_exists_adj T v).2 ⟨z, h⟩
  have hsub : Sᶜ ⊆ univ.filter (fun x => T.degree x = 1) := by
    intro x hx
    rw [mem_compl] at hx
    exact mem_filter.2 ⟨mem_univ _, hleaf x hx⟩
  have h1 := card_le_card hsub
  rw [card_compl] at h1
  have hS : S.card ≤ Fintype.card V := card_le_univ S
  have h2 : ((Fintype.card V - S.card : ℕ) : ℝ) ≤
      ((univ.filter (fun x => T.degree x = 1)).card : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_sub hS] at h2
  linarith [Ls_ge G T (hTH.trans hHG) hT]

/-- Invariant of the pair greedy started from a star: `S` connected around `s`, `Y ⊆ S`
independent and `|S| + L ≤ 2|Y| + 1`. -/
def Inv7 (G : SimpleGraph V) (L : ℕ) (s : V) (S Y : Finset V) : Prop :=
  s ∈ S ∧ Y ⊆ S ∧ (∀ a ∈ Y, ∀ b ∈ Y, ¬ G.Adj a b) ∧ S.card + L ≤ 2 * Y.card + 1 ∧
  (∀ v ∈ S, (K G S).Reachable s v)

omit [Fintype V] in
lemma step7 (G : SimpleGraph V) (L : ℕ) (s : V) (S Y : Finset V) (hI : Inv7 G L s S Y)
    (x y : V) (hxS : x ∉ S) (t : V) (ht : t ∈ S) (htx : G.Adj t x) (hyS : y ∉ S)
    (hyd : ∀ t ∈ S, ¬ G.Adj t y) (hxy : G.Adj x y) :
    Inv7 G L s (insert y (insert x S)) (insert y Y) := by
  obtain ⟨hsS, hYS, hind, hcard, hreach⟩ := hI
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hyx : y ∉ insert x S := by
    rw [mem_insert]; rintro (h | h); exact hxy' h.symm; exact hyS h
  have hyY : y ∉ Y := fun h => hyS (hYS h)
  have hmono : K G S ≤ K G (insert y (insert x S)) := fun a b h =>
    ⟨h.1, mem_insert_of_mem (mem_insert_of_mem h.2.1),
      mem_insert_of_mem (mem_insert_of_mem h.2.2)⟩
  refine ⟨mem_insert_of_mem (mem_insert_of_mem hsS), ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [mem_insert] at hv ⊢
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr (mem_insert_of_mem (hYS h))
  · intro a ha b hb
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.irrefl
    · exact fun h => hyd b (hYS hb) h.symm
    · exact hyd a (hYS ha)
    · exact hind a ha b hb
  · rw [card_insert_of_notMem hyx, card_insert_of_notMem hxS, card_insert_of_notMem hyY]
    omega
  · intro v hv
    have hrt : (K G (insert y (insert x S))).Reachable s t := (hreach t ht).mono hmono
    have hrx : (K G (insert y (insert x S))).Reachable s x :=
      hrt.trans (Adj.reachable ⟨htx, mem_insert_of_mem (mem_insert_of_mem ht),
        mem_insert_of_mem (mem_insert_self _ _)⟩)
    rw [mem_insert, mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact hrx.trans (Adj.reachable ⟨hxy, mem_insert_of_mem (mem_insert_self _ _),
        mem_insert_self _ _⟩)
    · exact hrx
    · exact (hreach v hv).mono hmono

lemma greedy7 (G : SimpleGraph V) (L : ℕ) (s : V) (S0 Y0 : Finset V) (h0 : Inv7 G L s S0 Y0)
    (hstep : ∀ S : Finset V, s ∈ S → (∃ w, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w) →
      ∃ x, x ∉ S ∧ (∃ t ∈ S, G.Adj t x) ∧ ∃ y, y ∉ S ∧ (∀ t ∈ S, ¬ G.Adj t y) ∧ G.Adj x y) :
    ∃ S Y : Finset V, Inv7 G L s S Y ∧ ∀ w, w ∈ S ∨ ∃ t ∈ S, G.Adj t w := by
  suffices H : ∀ m : ℕ, ∀ S Y : Finset V, Inv7 G L s S Y → Fintype.card V - S.card ≤ m →
      ∃ S Y : Finset V, Inv7 G L s S Y ∧ ∀ w, w ∈ S ∨ ∃ t ∈ S, G.Adj t w from
    H _ S0 Y0 h0 le_rfl
  intro m
  induction m with
  | zero =>
    intro S Y hI hm
    refine ⟨S, Y, hI, fun w => Or.inl ?_⟩
    have hle : (univ : Finset V).card ≤ S.card := by rw [card_univ]; omega
    rw [eq_of_subset_of_card_le (subset_univ S) hle]
    exact mem_univ w
  | succ m ih =>
    intro S Y hI hm
    by_cases hd : ∃ w, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w
    · obtain ⟨x, hxS, ⟨t, ht, htx⟩, y, hyS, hyd, hxy⟩ := hstep S hI.1 hd
      have hI' := step7 G L s S Y hI x y hxS t ht htx hyS hyd hxy
      apply ih _ _ hI'
      have hxy' : x ≠ y := G.ne_of_adj hxy
      have h1 : (insert y (insert x S)).card = S.card + 2 := by
        rw [card_insert_of_notMem, card_insert_of_notMem hxS]
        rw [mem_insert]; rintro (h | h); exact hxy' h.symm; exact hyS h
      have h2 := card_le_univ (insert y (insert x S))
      omega
    · refine ⟨S, Y, hI, fun w => ?_⟩
      by_cases hwS : w ∈ S
      · exact Or.inl hwS
      · exact Or.inr (by
          by_contra hno
          exact hd ⟨w, hwS, fun t ht hta => hno ⟨t, ht, hta⟩⟩)

omit [Fintype V] [DecidableEq V] in
lemma hstep7 (G : SimpleGraph V) (hc : G.Connected) (s : V) :
    ∀ S : Finset V, s ∈ S → (∃ w, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w) →
      ∃ x, x ∉ S ∧ (∃ t ∈ S, G.Adj t x) ∧ ∃ y, y ∉ S ∧ (∀ t ∈ S, ¬ G.Adj t y) ∧ G.Adj x y := by
  rintro S hsS ⟨w, hwS, hwd⟩
  obtain ⟨p⟩ := hc.preconnected s w
  obtain ⟨d, -, h1, h2⟩ := p.exists_boundary_dart {v | v ∈ S ∨ ∃ t ∈ S, G.Adj t v}
    (Or.inl hsS) (by
      rintro (h | ⟨t, ht, hta⟩)
      · exact hwS h
      · exact hwd t ht hta)
  have h2' : d.snd ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t d.snd :=
    ⟨fun h => h2 (Or.inl h), fun t ht hta => h2 (Or.inr ⟨t, ht, hta⟩)⟩
  have hxS : d.fst ∉ S := fun h => h2'.2 _ h d.adj
  rcases h1 with h1 | ⟨t, ht, htx⟩
  · exact absurd h1 hxS
  exact ⟨d.fst, hxS, ⟨t, ht, htx⟩, d.snd, h2'.1, h2'.2, d.adj⟩

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

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  classical
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1
    (Finset.max'_mem (Finset.univ.image (fun v => indepNeighborsCard G v)) (by simp))
  obtain ⟨I, hIc, hIv, hIind⟩ := nbhd_indep G v
  have hvI : v ∉ I := fun h => G.irrefl (hIv v h)
  have h0 : Inv7 G I.card v (insert v I) I := by
    refine ⟨mem_insert_self _ _, subset_insert _ _, hIind, ?_, ?_⟩
    · rw [card_insert_of_notMem hvI]; omega
    · intro w hw
      rw [mem_insert] at hw
      rcases hw with rfl | hw
      · exact Reachable.refl _
      · exact Adj.reachable ⟨hIv w hw, mem_insert_self _ _, mem_insert_of_mem hw⟩
  obtain ⟨S, Y, ⟨hsS, hYS, hind, hcard, hreach⟩, hdom⟩ :=
    greedy7 G I.card v _ _ h0 (hstep7 G h v)
  have hY : G.IsIndepSet (Y : Set α) :=
    fun a ha b hb _ => hind a (mem_coe.1 ha) b (mem_coe.1 hb)
  have hYa : (Y.card : ℝ) ≤ G.indepNum := by exact_mod_cast hY.card_le_indepNum
  have hT := tree_bound G S v hsS hreach hdom
  have hc' : (S.card : ℝ) + I.card ≤ 2 * Y.card + 1 := by exact_mod_cast hcard
  dsimp only
  rw [← hv, ← hIc]
  push_cast
  linarith

end WrittenOnTheWallII.GraphConjecture7

#print axioms WrittenOnTheWallII.GraphConjecture7.conjecture7
