import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean, Matching.lean and Clique.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

scoped notation "α(" G ")" => indepNum G

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

open scoped Classical in
/-- `matchingNumber G` is the size of a maximum matching of `G`. -/
noncomputable def matchingNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => (M.edgeSet.toFinset.card : ℝ)) matchings)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture6

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

omit [DecidableEq V] in
/-- A graph in which every vertex has at most one neighbour is a matching. -/
lemma mn_ge (G : SimpleGraph V) [DecidableRel G.Adj] (M : SimpleGraph V) [DecidableRel M.Adj]
    (hMG : M ≤ G) (huniq : ∀ a b c, M.Adj a b → M.Adj a c → b = c) :
    (M.edgeFinset.card : ℝ) ≤ matchingNumber G := by
  classical
  let Ms : G.Subgraph :=
    { verts := {v | ∃ w, M.Adj v w}
      Adj := M.Adj
      adj_sub := fun h => hMG h
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hMs : Ms.IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw, fun y hy => huniq _ _ _ hy hw⟩
  have hE : Ms.edgeSet = M.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h a b => rw [Subgraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
  unfold matchingNumber
  refine le_trans ?_ (le_csSup ?_ ⟨Ms, hMs, rfl⟩)
  · beta_reduce
    rw [edgeFinset, ← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card', hE]
  · refine ⟨(Fintype.card (Sym2 V) : ℝ), ?_⟩
    rintro _ ⟨N, -, rfl⟩
    beta_reduce
    exact_mod_cast Finset.card_le_univ _

/-- Handshake for a matching: `2·#edges = #matched vertices`. -/
lemma two_edges (M : SimpleGraph V) [DecidableRel M.Adj]
    (huniq : ∀ a b c, M.Adj a b → M.Adj a c → b = c) (D : Finset V)
    (hD : ∀ v, (∃ w, M.Adj v w) ↔ v ∈ D) : 2 * M.edgeFinset.card = D.card := by
  rw [← M.sum_degrees_eq_twice_card_edges]
  have hdeg : ∀ v, M.degree v = if v ∈ D then 1 else 0 := by
    intro v
    split_ifs with hv
    · obtain ⟨w, hw⟩ := (hD v).2 hv
      rw [← card_neighborFinset_eq_degree, card_eq_one]
      refine ⟨w, ?_⟩
      ext y
      rw [mem_neighborFinset, mem_singleton]
      exact ⟨fun hy => huniq _ _ _ hy hw, fun h => h ▸ hw⟩
    · rw [← card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_neighborFinset] at hy
      exact hv ((hD v).1 ⟨y, hy⟩)
  rw [Finset.sum_congr rfl (fun v _ => hdeg v), Finset.sum_boole]
  simp

omit [Fintype V] in
/-- Adding a disjoint edge to a matching. -/
lemma add_edge (G M : SimpleGraph V) (D : Finset V) (hMG : M ≤ G)
    (huniq : ∀ a b c, M.Adj a b → M.Adj a c → b = c) (hsupp : ∀ v, (∃ w, M.Adj v w) ↔ v ∈ D)
    (x y : V) (hxy : G.Adj x y) (hx : x ∉ D) (hy : y ∉ D) :
    ∃ M' : SimpleGraph V, M' ≤ G ∧ (∀ a b c, M'.Adj a b → M'.Adj a c → b = c) ∧
      ∀ v, (∃ w, M'.Adj v w) ↔ v ∈ insert y (insert x D) := by
  have hxy' : x ≠ y := G.ne_of_adj hxy
  set M' := M ⊔ SimpleGraph.fromRel (fun a b => a = x ∧ b = y) with hM'
  have hA : ∀ a b, M'.Adj a b ↔ M.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    intro a b
    simp only [hM', sup_adj, fromRel_adj]
    constructor
    · rintro (h | ⟨-, h | ⟨h1, h2⟩⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by rw [h1, h2]; exact hxy', Or.inl ⟨h1, h2⟩⟩
      · exact Or.inr ⟨by rw [h1, h2]; exact hxy'.symm, Or.inr ⟨h2, h1⟩⟩
  have hMD : ∀ a b, M.Adj a b → a ∈ D := fun a b h => (hsupp a).1 ⟨b, h⟩
  refine ⟨M', ?_, ?_, ?_⟩
  · intro a b h
    rcases (hA a b).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hMG h
    · rw [h1, h2]; exact hxy
    · rw [h1, h2]; exact hxy.symm
  · intro a b c h1 h2
    rw [hA] at h1 h2
    rcases h1 with h1 | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
      rcases h2 with h2 | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
    · exact huniq _ _ _ h1 h2
    · exact absurd (by rw [← h2a]; exact hMD _ _ h1) hx
    · exact absurd (by rw [← h2a]; exact hMD _ _ h1) hy
    · exact absurd (by rw [← h1a]; exact hMD _ _ h2) hx
    · rw [h1b, h2b]
    · exact absurd (h1a.symm.trans h2a) hxy'
    · exact absurd (by rw [← h1a]; exact hMD _ _ h2) hy
    · exact absurd (h2a.symm.trans h1a) hxy'
    · rw [h1b, h2b]
  · intro v
    rw [mem_insert, mem_insert]
    constructor
    · rintro ⟨w, hw⟩
      rcases (hA v w).1 hw with h | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr (Or.inr (hMD _ _ h))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
    · rintro (h | h | h)
      · exact ⟨x, (hA v x).2 (Or.inr (Or.inr ⟨h, rfl⟩))⟩
      · exact ⟨y, (hA v y).2 (Or.inr (Or.inl ⟨h, rfl⟩))⟩
      · obtain ⟨w, hw⟩ := (hsupp v).2 h
        exact ⟨w, (hA v w).2 (Or.inl hw)⟩

/-- Invariant of the pair greedy. -/
def Inv (G : SimpleGraph V) (W : Finset V) (s : V) (S Y : Finset V) (M : SimpleGraph V) :
    Prop :=
  S ⊆ W ∧ s ∈ S ∧ Y ⊆ S ∧ (∀ a ∈ Y, ∀ b ∈ Y, ¬ G.Adj a b) ∧ S.card + 1 = 2 * Y.card ∧
  M ≤ G ∧ (∀ a b c, M.Adj a b → M.Adj a c → b = c) ∧
  (∀ v, (∃ w, M.Adj v w) ↔ v ∈ S.erase s) ∧ (∀ v ∈ S, (K G S).Reachable s v)

omit [Fintype V] in
lemma step (G : SimpleGraph V) (W : Finset V) (s : V) (S Y : Finset V) (M : SimpleGraph V)
    (hI : Inv G W s S Y M) (x y : V) (hxW : x ∈ W) (hxS : x ∉ S) (t : V) (ht : t ∈ S)
    (htx : G.Adj t x) (hyW : y ∈ W) (hyS : y ∉ S) (hyd : ∀ t ∈ S, ¬ G.Adj t y)
    (hxy : G.Adj x y) :
    ∃ M' : SimpleGraph V, Inv G W s (insert y (insert x S)) (insert y Y) M' := by
  obtain ⟨hSW, hsS, hYS, hind, hcard, hMG, huniq, hsupp, hreach⟩ := hI
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hxs : x ≠ s := fun h => hxS (h ▸ hsS)
  have hys : y ≠ s := fun h => hyS (h ▸ hsS)
  obtain ⟨M', hM'G, hM'u, hM's⟩ := add_edge G M (S.erase s) hMG huniq hsupp x y hxy
    (fun h => hxS (mem_of_mem_erase h)) (fun h => hyS (mem_of_mem_erase h))
  have heq : insert y (insert x (S.erase s)) = (insert y (insert x S)).erase s := by
    ext v
    simp only [mem_insert, mem_erase]
    constructor
    · rintro (h | h | ⟨h1, h2⟩)
      · exact ⟨h ▸ hys, Or.inl h⟩
      · exact ⟨h ▸ hxs, Or.inr (Or.inl h)⟩
      · exact ⟨h1, Or.inr (Or.inr h2)⟩
    · rintro ⟨h1, h | h | h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  have hyx : y ∉ insert x S := by
    rw [mem_insert]; rintro (h | h); exact hxy' h.symm; exact hyS h
  have hyY : y ∉ Y := fun h => hyS (hYS h)
  have hmono : K G S ≤ K G (insert y (insert x S)) := fun a b h =>
    ⟨h.1, mem_insert_of_mem (mem_insert_of_mem h.2.1),
      mem_insert_of_mem (mem_insert_of_mem h.2.2)⟩
  refine ⟨M', ?_, ?_, ?_, ?_, ?_, hM'G, hM'u, ?_, ?_⟩
  · intro v hv
    rw [mem_insert, mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact hyW
    · exact hxW
    · exact hSW hv
  · exact mem_insert_of_mem (mem_insert_of_mem hsS)
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
  · intro v
    rw [hM's, heq]
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

lemma greedy (G : SimpleGraph V) (W : Finset V) (s : V) (hs : s ∈ W)
    (hstep : ∀ S : Finset V, S ⊆ W → s ∈ S → (∃ w ∈ W, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w) →
      ∃ x ∈ W, x ∉ S ∧ (∃ t ∈ S, G.Adj t x) ∧
        ∃ y ∈ W, y ∉ S ∧ (∀ t ∈ S, ¬ G.Adj t y) ∧ G.Adj x y) :
    ∃ S Y : Finset V, ∃ M : SimpleGraph V, Inv G W s S Y M ∧
      ∀ w ∈ W, w ∈ S ∨ ∃ t ∈ S, G.Adj t w := by
  suffices H : ∀ m : ℕ, ∀ S Y : Finset V, ∀ M : SimpleGraph V, Inv G W s S Y M →
      W.card - S.card ≤ m → ∃ S Y : Finset V, ∃ M : SimpleGraph V, Inv G W s S Y M ∧
        ∀ w ∈ W, w ∈ S ∨ ∃ t ∈ S, G.Adj t w by
    refine H W.card {s} {s} ⊥ ?_ (Nat.sub_le _ _)
    refine ⟨singleton_subset_iff.2 hs, mem_singleton_self _, subset_refl _, ?_, ?_, bot_le,
      ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [mem_singleton] at ha hb
      rw [ha, hb]
      exact G.irrefl
    · simp
    · intro a b c h
      exact absurd h (by simp)
    · intro v
      simp
    · intro v hv
      rw [mem_singleton] at hv
      rw [hv]
  intro m
  induction m with
  | zero =>
    intro S Y M hI hm
    refine ⟨S, Y, M, hI, fun w hw => Or.inl ?_⟩
    have hle : W.card ≤ S.card := by omega
    rw [eq_of_subset_of_card_le hI.1 hle]
    exact hw
  | succ m ih =>
    intro S Y M hI hm
    by_cases hd : ∃ w ∈ W, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w
    · obtain ⟨x, hxW, hxS, ⟨t, ht, htx⟩, y, hyW, hyS, hyd, hxy⟩ := hstep S hI.1 hI.2.1 hd
      obtain ⟨M', hI'⟩ := step G W s S Y M hI x y hxW hxS t ht htx hyW hyS hyd hxy
      apply ih _ _ _ hI'
      have h1 := hI'.2.2.2.2.1
      have h0 := hI.2.2.2.2.1
      have hY : (insert y Y).card = Y.card + 1 :=
        card_insert_of_notMem (fun h => hyS (hI.2.2.1 h))
      have h2 := card_le_card hI'.1
      omega
    · refine ⟨S, Y, M, hI, fun w hw => ?_⟩
      by_cases hwS : w ∈ S
      · exact Or.inl hwS
      · exact Or.inr (by
          by_contra hno
          exact hd ⟨w, hw, hwS, fun t ht hta => hno ⟨t, ht, hta⟩⟩)

omit [Fintype V] [DecidableEq V] in
lemma hstep_of_walks (G : SimpleGraph V) (W : Finset V) (s : V)
    (hw : ∀ w ∈ W, ∃ p : G.Walk s w, ∀ v ∈ p.support, v ∈ W) :
    ∀ S : Finset V, S ⊆ W → s ∈ S → (∃ w ∈ W, w ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t w) →
      ∃ x ∈ W, x ∉ S ∧ (∃ t ∈ S, G.Adj t x) ∧
        ∃ y ∈ W, y ∉ S ∧ (∀ t ∈ S, ¬ G.Adj t y) ∧ G.Adj x y := by
  rintro S - hsS ⟨w, hwW, hwS, hwd⟩
  obtain ⟨p, hp⟩ := hw w hwW
  obtain ⟨d, hd, h1, h2⟩ := p.exists_boundary_dart {v | v ∈ S ∨ ∃ t ∈ S, G.Adj t v}
    (Or.inl hsS) (by
      rintro (h | ⟨t, ht, hta⟩)
      · exact hwS h
      · exact hwd t ht hta)
  have h2' : d.snd ∉ S ∧ ∀ t ∈ S, ¬ G.Adj t d.snd := by
    refine ⟨fun h => h2 (Or.inl h), fun t ht hta => h2 (Or.inr ⟨t, ht, hta⟩)⟩
  have hxS : d.fst ∉ S := fun h => h2'.2 _ h d.adj
  rcases h1 with h1 | ⟨t, ht, htx⟩
  · exact absurd h1 hxS
  exact ⟨d.fst, hp _ (p.dart_fst_mem_support_of_mem_darts hd), hxS, ⟨t, ht, htx⟩, d.snd,
    hp _ (p.dart_snd_mem_support_of_mem_darts hd), h2'.1, h2'.2, d.adj⟩

omit [Fintype V] in
/-- Shortest walks from `u` avoid a vertex `r` farthest from `u`. -/
lemma avoid (G : SimpleGraph V) (u r : V) (hr : ∀ v, G.dist u v ≤ G.dist u r) (v : V)
    (hv : v ≠ r) (p : G.Walk u v) (hp : p.length = G.dist u v) : r ∉ p.support := by
  intro h
  have e := p.take_spec h
  have l := congrArg Walk.length e
  rw [Walk.length_append] at l
  have h1 : G.dist u r ≤ (p.takeUntil r h).length := dist_le _
  have h2 : (p.dropUntil r h).length ≠ 0 := fun h0 => hv (Walk.eq_of_length_eq_zero h0).symm
  have := hr v
  omega

lemma boundA (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] (hc : G.Connected) :
    (Fintype.card V : ℝ) + 1 - 2 * matchingNumber G ≤ Ls G := by
  classical
  obtain ⟨u⟩ : Nonempty V := inferInstance
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image univ (fun v => G.dist u v) univ_nonempty
  have hr' : ∀ v, G.dist u v ≤ G.dist u r := fun v => hr v (mem_univ v)
  have hur : u ≠ r := by
    obtain ⟨v, hv⟩ := exists_ne u
    have h1 := hc.pos_dist_of_ne hv.symm
    intro h
    have h2 := hr' v
    rw [← h, dist_self] at h2
    omega
  obtain ⟨s, hrs⟩ : ∃ s, G.Adj r s := by
    obtain ⟨p⟩ := hc.preconnected r u
    cases p with
    | nil => exact absurd rfl hur
    | @cons _ z _ h _ => exact ⟨z, h⟩
  have hsr : s ≠ r := (G.ne_of_adj hrs).symm
  have hwalk : ∀ w ∈ univ.erase r, ∃ p : G.Walk s w, ∀ v ∈ p.support, v ∈ univ.erase r := by
    intro w hw
    have hwr : w ≠ r := (mem_erase.1 hw).1
    obtain ⟨p1, hp1⟩ := hc.exists_walk_length_eq_dist u s
    obtain ⟨p2, hp2⟩ := hc.exists_walk_length_eq_dist u w
    refine ⟨p1.reverse.append p2, fun v hv => mem_erase.2 ⟨?_, mem_univ _⟩⟩
    intro hvr
    rw [hvr, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hv
    rcases hv with hv | hv
    · exact avoid G u r hr' s hsr p1 hp1 hv
    · exact avoid G u r hr' w hwr p2 hp2 hv
  obtain ⟨S, Y, M, hI, hdom⟩ := greedy G (univ.erase r) s (mem_erase.2 ⟨hsr, mem_univ _⟩)
    (hstep_of_walks G _ s hwalk)
  obtain ⟨hSW, hsS, hYS, hind, hcard, hMG, huniq, hsupp, hreach⟩ := hI
  have hrS : r ∉ S := fun h => (mem_erase.1 (hSW h)).1 rfl
  obtain ⟨M', hM'G, hM'u, hM's⟩ := add_edge G M (S.erase s) hMG huniq hsupp s r hrs.symm
    (fun h => (mem_erase.1 h).1 rfl) (fun h => hrS (mem_of_mem_erase h))
  have hD : (insert r (insert s (S.erase s))).card = S.card + 1 := by
    rw [card_insert_of_notMem, card_insert_of_notMem (fun h => (mem_erase.1 h).1 rfl),
      card_erase_of_mem hsS]
    · have : 1 ≤ S.card := card_pos.2 ⟨s, hsS⟩
      omega
    · rw [mem_insert]
      rintro (h | h)
      · exact hsr h.symm
      · exact hrS (mem_of_mem_erase h)
  have hE := two_edges M' hM'u _ hM's
  have hmn := mn_ge G M' hM'G hM'u
  have hT := tree_bound G S s hsS hreach (fun v => by
    by_cases hv : v = r
    · exact Or.inr ⟨s, hsS, hv ▸ hrs.symm⟩
    · exact hdom v (mem_erase.2 ⟨hv, mem_univ _⟩))
  have hE' : (M'.edgeFinset.card : ℝ) = Y.card := by
    have : M'.edgeFinset.card = Y.card := by omega
    exact_mod_cast this
  have hc' : (S.card : ℝ) + 1 = 2 * Y.card := by exact_mod_cast hcard
  linarith

lemma boundB (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] (hc : G.Connected) :
    (Fintype.card V : ℝ) + 1 - 2 * (G.indepNum : ℝ) ≤ Ls G := by
  classical
  obtain ⟨s⟩ : Nonempty V := inferInstance
  have hwalk : ∀ w ∈ (univ : Finset V), ∃ p : G.Walk s w, ∀ v ∈ p.support, v ∈ univ :=
    fun w _ => ⟨(hc.preconnected s w).some, fun v _ => mem_univ v⟩
  obtain ⟨S, Y, M, hI, hdom⟩ := greedy G univ s (mem_univ s) (hstep_of_walks G univ s hwalk)
  obtain ⟨hSW, hsS, hYS, hind, hcard, hMG, huniq, hsupp, hreach⟩ := hI
  have hY : G.IsIndepSet (Y : Set V) :=
    fun a ha b hb _ => hind a (mem_coe.1 ha) b (mem_coe.1 hb)
  have hYa := hY.card_le_indepNum
  have hT := tree_bound G S s hsS hreach (fun v => hdom v (mem_univ v))
  have hc' : (S.card : ℝ) + 1 = 2 * Y.card := by exact_mod_cast hcard
  have hYa' : (Y.card : ℝ) ≤ G.indepNum := by exact_mod_cast hYa
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture6 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    1 + (Fintype.card α : ℝ) - matchingNumber G - α(G) ≤ Ls G := by
  have hA := boundA G h_conn
  have hB := boundB G h_conn
  rcases le_total (matchingNumber G) (α(G) : ℝ) with h | h <;> linarith

end WrittenOnTheWallII.GraphConjecture6

#print axioms WrittenOnTheWallII.GraphConjecture6.conjecture6
