import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean, Induced.lean, VertexDistance.lean, Eccentricity.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

omit [Fintype α] in
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

def graphSquare {β : Type*} (G : SimpleGraph β) : SimpleGraph β where
  Adj u v := u ≠ v ∧ G.edist u v ≤ 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def maxEccentricityVertices {β : Type*} (G : SimpleGraph β) : Set β :=
  {v : β | G.eccent v = G.ediam}

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture181

open SimpleGraph

noncomputable def squarePeripheryAverage {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  let square := graphSquare G
  let periphery := Finset.univ.filter fun v => v ∈ maxEccentricityVertices square
  exact (∑ v ∈ periphery, ((square.neighborFinset v).card : ℝ)) / periphery.card

/-! ### General lemma -/

/-- A connected spanning subgraph has an edge across every nontrivial cut. -/
lemma cut_edge {V : Type*} [Fintype V] {G : SimpleGraph V} (T : G.Subgraph)
    (hspan : T.IsSpanning) (hconn : T.coe.Connected) (S : Set V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : ∃ x y, T.Adj x y ∧ x ∈ S ∧ y ∉ S := by
  let f : T.coe →g T.spanningCoe := ⟨fun x => x.1, fun {x y} h => h⟩
  have hr : T.coe.Reachable ⟨a, hspan a⟩ ⟨b, hspan b⟩ := hconn.preconnected _ _
  have p := (hr.map f).some
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  exact ⟨d.fst, d.snd, d.adj, hd1, hd2⟩

/-! ### The triangular graph `T(7) = L(K₇)` on `Fin 21` -/

def pa (v : Fin 21) : Fin 7 :=
  ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5] : List (Fin 7)).getD v.val 0

def pb (v : Fin 21) : Fin 7 :=
  ([1, 2, 3, 4, 5, 6, 2, 3, 4, 5, 6, 3, 4, 5, 6, 4, 5, 6, 5, 6, 6] : List (Fin 7)).getD v.val 0

def adjF (u v : Fin 21) : Prop :=
  u ≠ v ∧ (pa u = pa v ∨ pa u = pb v ∨ pb u = pa v ∨ pb u = pb v)

instance : DecidableRel adjF := fun u v => by unfold adjF; infer_instance

lemma adjF_symm (u v : Fin 21) (h : adjF u v) : adjF v u := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨Ne.symm h1, ?_⟩
  rcases h2 with e | e | e | e
  · exact Or.inl e.symm
  · exact Or.inr (Or.inr (Or.inl e.symm))
  · exact Or.inr (Or.inl e.symm)
  · exact Or.inr (Or.inr (Or.inr e.symm))

def G : SimpleGraph (Fin 21) where
  Adj := adjF
  symm := ⟨fun x y h => adjF_symm x y h⟩
  loopless := ⟨fun x h => h.1 rfl⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

def ep (v : Fin 21) : Finset (Fin 7) := {pa v, pb v}

def cover (S : Finset (Fin 21)) : Finset (Fin 7) := S.biUnion ep

lemma papb : ∀ v : Fin 21, pa v ≠ pb v := by decide

lemma ep_card (v : Fin 21) : (ep v).card = 2 := Finset.card_pair (papb v)

lemma share (x y : Fin 21) (h : adjF x y) : ∃ z, z ∈ ep x ∧ z ∈ ep y := by
  rcases h.2 with e | e | e | e
  · exact ⟨pa x, by simp [ep], by simp [ep, e]⟩
  · exact ⟨pa x, by simp [ep], by simp [ep, e]⟩
  · exact ⟨pb x, by simp [ep], by simp [ep, e]⟩
  · exact ⟨pb x, by simp [ep], by simp [ep, e]⟩

lemma inc_adj (a c : Fin 21) (x : Fin 7) (hac : a ≠ c) (ha : pa a = x ∨ pb a = x)
    (hc : pa c = x ∨ pb c = x) : adjF a c := by
  refine ⟨hac, ?_⟩
  rcases ha with e | e <;> rcases hc with f | f
  · exact Or.inl (e.trans f.symm)
  · exact Or.inr (Or.inl (e.trans f.symm))
  · exact Or.inr (Or.inr (Or.inl (e.trans f.symm)))
  · exact Or.inr (Or.inr (Or.inr (e.trans f.symm)))

lemma pair_ex : ∀ x y : Fin 7, x ≠ y → ∃ w : Fin 21,
    (pa w = x ∧ pb w = y) ∨ (pa w = y ∧ pb w = x) := by decide

set_option maxRecDepth 100000 in
lemma sq2 : ∀ u v : Fin 21, u ≠ v → adjF u v ∨ ∃ x, adjF u x ∧ adjF x v := by decide

lemma inc_card : ∀ v : Fin 21,
    (Finset.univ.filter (fun x : Fin 7 => pa v = x ∨ pb v = x)).card = 2 := by decide

/-! ### Independent sets have at most 3 elements -/

lemma indep3 (S : Finset (Fin 21)) (h : ∀ u ∈ S, ∀ v ∈ S, ¬ adjF u v) : S.card ≤ 3 := by
  have h1 : ∀ x : Fin 7, (S.filter (fun v => pa v = x ∨ pb v = x)).card ≤ 1 := by
    intro x
    apply Finset.card_le_one.2
    intro a ha c hc
    rw [Finset.mem_filter] at ha hc
    by_contra hac
    exact h a ha.1 c hc.1 (inc_adj a c x hac ha.2 hc.2)
  have hv : ∀ v : Fin 21, ∑ x : Fin 7, (if pa v = x ∨ pb v = x then 1 else 0) = 2 := by
    intro v
    rw [← Finset.card_filter]
    exact inc_card v
  have h2 : ∑ x : Fin 7, (S.filter (fun v => pa v = x ∨ pb v = x)).card = 2 * S.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [hv, Finset.sum_const, smul_eq_mul]
    ring
  have h3 : ∑ x : Fin 7, (S.filter (fun v => pa v = x ∨ pb v = x)).card ≤ ∑ _x : Fin 7, 1 :=
    Finset.sum_le_sum fun x _ => h1 x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  omega

/-! ### `b ≤ 6` -/

lemma b_le : b G ≤ 6 := by
  unfold b largestInducedBipartiteSubgraphSize
  have hS : sSup {n | ∃ s : Finset (Fin 21), (G.induce (s : Set (Fin 21))).IsBipartite ∧
      s.card = n} ≤ 6 := by
    apply csSup_le'
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring G s).1 hs
    have f2 : ∀ a b : Fin 2, a ≠ 0 → b ≠ 0 → a = b := by decide
    have hsub : s ⊆ s.filter (fun v => c v = 0) ∪ s.filter (fun v => ¬ c v = 0) := by
      intro v hv
      by_cases h : c v = 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hv, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hv, h⟩)
    have i0 := indep3 (s.filter (fun v => c v = 0)) (by
      intro u hu v hv huv
      rw [Finset.mem_filter] at hu hv
      exact hc u hu.1 v hv.1 huv (hu.2.trans hv.2.symm))
    have i1 := indep3 (s.filter (fun v => ¬ c v = 0)) (by
      intro u hu v hv huv
      rw [Finset.mem_filter] at hu hv
      exact hc u hu.1 v hv.1 huv (f2 _ _ hu.2 hv.2))
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  exact_mod_cast hS

/-! ### `α ≥ 3` -/

lemma alpha_ge : 3 ≤ G.indepNum := by
  have key : ∀ u v : Fin 21, u ∈ ({0, 11, 18} : Finset (Fin 21)) →
      v ∈ ({0, 11, 18} : Finset (Fin 21)) → u ≠ v → ¬ adjF u v := by decide
  have hI : G.IsIndepSet (({0, 11, 18} : Finset (Fin 21)) : Set (Fin 21)) := by
    intro u hu v hv huv
    exact key u v hu hv huv
  have := hI.card_le_indepNum
  have hc : ({0, 11, 18} : Finset (Fin 21)).card = 3 := by decide
  omega

/-! ### Connectivity and the square -/

lemma connected : G.Connected := by
  rw [connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  by_cases huv : u = v
  · rw [huv]
  · rcases sq2 u v huv with h | ⟨x, h1, h2⟩
    · exact Adj.reachable (G := G) h
    · exact (Adj.reachable (G := G) h1).trans (Adj.reachable (G := G) h2)

lemma sq_adj (u v : Fin 21) (h : u ≠ v) : (graphSquare G).Adj u v := by
  refine ⟨h, ?_⟩
  rcases sq2 u v h with h1 | ⟨x, h1, h2⟩
  · exact (edist_le_one_iff_adj_or_eq.2 (Or.inl h1)).trans (by norm_num)
  · calc G.edist u v ≤ G.edist u x + G.edist x v := SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := add_le_add (edist_le_one_iff_adj_or_eq.2 (Or.inl h1))
          (edist_le_one_iff_adj_or_eq.2 (Or.inl h2))
      _ = 2 := one_add_one_eq_two

lemma avg : squarePeripheryAverage G = 20 := by
  unfold squarePeripheryAverage
  dsimp only
  have hdeg : ∀ (v : Fin 21) (i : Fintype ↑((graphSquare G).neighborSet v)),
      (@neighborFinset _ (graphSquare G) v i).card = 20 := by
    intro v i
    have e : @neighborFinset _ (graphSquare G) v i = Finset.univ.erase v := by
      ext w
      rw [mem_neighborFinset, Finset.mem_erase]
      exact ⟨fun h => ⟨h.1.symm, Finset.mem_univ _⟩, fun h => sq_adj v w (Ne.symm h.1)⟩
    rw [e, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  obtain ⟨v0, hv0⟩ := (graphSquare G).exists_eccent_eq_ediam_of_finite
  rw [Finset.sum_congr rfl (fun v _ => by rw [hdeg v _])]
  rw [Finset.sum_const, nsmul_eq_mul]
  have key : ∀ P : Finset (Fin 21), P.Nonempty → (P.card : ℝ) * 20 / P.card = 20 := by
    intro P hP
    have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    rw [mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]
  apply key
  have mem : ∀ (p : Fin 21 → Prop) (i : DecidablePred p), p v0 →
      v0 ∈ @Finset.filter _ p i Finset.univ :=
    fun p i h => (@Finset.mem_filter _ p i _ _).2 ⟨Finset.mem_univ _, h⟩
  exact ⟨v0, mem _ _ hv0⟩

/-! ### `Ls ≤ 16` -/

lemma dom (T : G.Subgraph) (hspan : T.IsSpanning) (hconn : T.coe.Connected)
    (s : Finset (Fin 21)) (hs : ∀ v ∈ s, ∃! u, T.Adj v u) :
    ∀ w ∈ s, ∃ u, u ∉ s ∧ T.Adj w u := by
  intro w hw
  obtain ⟨u, hu, huniq⟩ := hs w hw
  refine ⟨u, ?_, hu⟩
  intro hus
  obtain ⟨u', -, huniq'⟩ := hs u hus
  have e1 : ∀ z, T.Adj u z → z = w := fun z hz => (huniq' z hz).trans (huniq' w hu.symm).symm
  obtain ⟨c, hc⟩ : ∃ c : Fin 21, c ≠ w ∧ c ≠ u := by
    by_contra hn
    simp only [not_exists, not_and, not_not] at hn
    have hsub : (Finset.univ : Finset (Fin 21)) ⊆ {w, u} := by
      intro c _
      by_cases h : c = w
      · simp [h]
      · simp [hn c h]
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    simp at this
  obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn {z | z = w ∨ z = u} w c (Or.inl rfl)
    (by simp only [Set.mem_setOf_eq]; tauto)
  simp only [Set.mem_setOf_eq] at hx hy
  rcases hx with rfl | rfl
  · exact hy (Or.inr (huniq y hxy))
  · exact hy (Or.inl (e1 y hxy))

lemma cutI (T : G.Subgraph) (hspan : T.IsSpanning) (hconn : T.coe.Connected)
    (s : Finset (Fin 21)) (hs : ∀ v ∈ s, ∃! u, T.Adj v u) (S : Finset (Fin 21))
    (a c : Fin 21) (ha : a ∈ S) (hc1 : c ∉ S) (hc2 : c ∉ s) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ y ∉ s ∧ T.Adj x y := by
  obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
    {z | z ∈ S ∨ (z ∈ s ∧ ∃ t ∈ S, T.Adj z t)} a c (Or.inl ha) (by
      simp only [Set.mem_setOf_eq]
      rintro (h | ⟨h, -⟩)
      · exact hc1 h
      · exact hc2 h)
  simp only [Set.mem_setOf_eq] at hx hy
  rcases hx with hx | ⟨hxs, t, ht, hxt⟩
  · refine ⟨x, hx, y, fun h => hy (Or.inl h), fun hys => hy (Or.inr ⟨hys, x, hx, hxy.symm⟩), hxy⟩
  · obtain ⟨u, -, hu⟩ := hs x hxs
    have e : y = t := (hu y hxy).trans (hu t hxt).symm
    exact absurd (Or.inl (e ▸ ht)) hy

lemma greedy (I : Finset (Fin 21))
    (hcut : ∀ S ⊆ I, S.Nonempty → ∀ c ∈ I, c ∉ S → ∃ x ∈ S, ∃ y ∈ I, y ∉ S ∧ adjF x y) :
    ∀ n ≤ I.card, ∃ S ⊆ I, S.card = n ∧ (cover S).card ≤ n + 1 := by
  intro n
  induction n with
  | zero => intro _; exact ⟨∅, Finset.empty_subset _, rfl, by simp [cover]⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, hS, hc, hcov⟩ := ih (by omega)
    obtain ⟨c, hcI, hcS⟩ : ∃ c ∈ I, c ∉ S := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      have := Finset.card_le_card (fun c hc => hne c hc : I ⊆ S)
      omega
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨{c}, Finset.singleton_subset_iff.2 hcI, rfl, ?_⟩
      simp [cover, ep_card]
    · have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨x, hx, y, hyI, hyS, hxy⟩ := hcut S hS hSne c hcI hcS
      refine ⟨insert y S, Finset.insert_subset hyI hS, by rw [Finset.card_insert_of_notMem hyS, hc], ?_⟩
      have e : cover (insert y S) = ep y ∪ cover S := by
        simp [cover, Finset.biUnion_insert]
      obtain ⟨z, hzx, hzy⟩ := share x y hxy
      have hz : z ∈ ep y ∩ cover S :=
        Finset.mem_inter.2 ⟨hzy, Finset.mem_biUnion.2 ⟨x, hx, hzx⟩⟩
      have h1 := Finset.card_union_add_card_inter (ep y) (cover S)
      have h2 : 1 ≤ (ep y ∩ cover S).card := Finset.card_pos.2 ⟨z, hz⟩
      rw [e]
      have := ep_card y
      omega

lemma cover_big (I : Finset (Fin 21)) (hdom : ∀ w, w ∉ I → ∃ u ∈ I, adjF w u) :
    6 ≤ (cover I).card := by
  by_contra hlt
  obtain ⟨x, hx⟩ : ∃ x, x ∉ cover I := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    have := Finset.card_le_card (fun x _ => hn x : (Finset.univ : Finset (Fin 7)) ⊆ cover I)
    simp at this
    omega
  obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ y ∉ cover I := by
    by_contra hn
    simp only [not_exists, not_and, not_not] at hn
    have hsub : Finset.univ.erase x ⊆ cover I := fun y hy => hn y (Finset.ne_of_mem_erase hy)
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at this
    simp at this
    omega
  obtain ⟨w, hw⟩ := pair_ex x y (Ne.symm hyx)
  have hwx : ∀ z ∈ ep w, z = x ∨ z = y := by
    intro z hz
    simp only [ep, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hw with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hz with rfl | rfl <;> simp [e1, e2]
  have hwI : w ∉ I := by
    intro hwI
    apply hx
    apply Finset.mem_biUnion.2 ⟨w, hwI, ?_⟩
    rcases hw with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp [ep, e1]
    · simp [ep, e2]
  obtain ⟨u, huI, hwu⟩ := hdom w hwI
  obtain ⟨z, hzw, hzu⟩ := share w u hwu
  have hzc : z ∈ cover I := Finset.mem_biUnion.2 ⟨u, huI, hzu⟩
  rcases hwx z hzw with rfl | rfl
  · exact hx hzc
  · exact hy hzc

lemma leaf_count (T : G.Subgraph) (hspan : T.IsSpanning) (hconn : T.coe.Connected)
    (s : Finset (Fin 21)) (hs : ∀ v ∈ s, ∃! u, T.Adj v u) : s.card ≤ 16 := by
  by_contra hlt
  have hI : sᶜ.card ≤ 4 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hdom : ∀ w, w ∉ sᶜ → ∃ u ∈ sᶜ, adjF w u := by
    intro w hw
    rw [Finset.mem_compl, not_not] at hw
    obtain ⟨u, hu, hwu⟩ := dom T hspan hconn s hs w hw
    exact ⟨u, Finset.mem_compl.2 hu, T.adj_sub hwu⟩
  have hcut : ∀ S ⊆ sᶜ, S.Nonempty → ∀ c ∈ sᶜ, c ∉ S →
      ∃ x ∈ S, ∃ y ∈ sᶜ, y ∉ S ∧ adjF x y := by
    intro S _ hSne c hc hcS
    obtain ⟨a, ha⟩ := hSne
    obtain ⟨x, hx, y, hyS, hys, hxy⟩ :=
      cutI T hspan hconn s hs S a c ha hcS (Finset.mem_compl.1 hc)
    exact ⟨x, hx, y, Finset.mem_compl.2 hys, hyS, T.adj_sub hxy⟩
  obtain ⟨S, hS, hc, hcov⟩ := greedy sᶜ hcut sᶜ.card le_rfl
  have e : S = sᶜ := Finset.eq_of_subset_of_card_le hS (by omega)
  rw [e] at hcov
  have := cover_big sᶜ hdom
  omega

lemma Ls_le : Ls G ≤ 16 := by
  unfold Ls
  apply Real.sSup_le _ (by norm_num)
  rintro _ ⟨T, ⟨hspan, htree⟩, rfl⟩
  beta_reduce
  have key : ∀ (i1 : Fintype ↑T.verts) (i2 : ∀ v, Fintype ↑(T.neighborSet v)),
      ((@Set.toFinset _ T.verts i1).filter
        (fun v => @Subgraph.degree _ _ T v (i2 v) = 1)).card ≤ 16 := by
    intro i1 i2
    apply leaf_count T hspan htree.connected
    intro v hv
    rw [Finset.mem_filter] at hv
    exact Subgraph.degree_eq_one_iff_existsUnique_adj.mp hv.2
  refine le_trans (Nat.cast_le.mpr (key _ _)) ?_
  norm_num

theorem conjecture181 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G + b G ≥ G.indepNum + squarePeripheryAverage G := by
  intro h
  have h1 := h (Fin 21) G connected
  have h2 := Ls_le
  have h3 := b_le
  have h4 : (3 : ℝ) ≤ G.indepNum := by exact_mod_cast alpha_ge
  rw [avg] at h1
  linarith

end WrittenOnTheWallII.GraphConjecture181

#print axioms WrittenOnTheWallII.GraphConjecture181.conjecture181
