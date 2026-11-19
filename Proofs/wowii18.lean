import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean
and VertexDistance.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

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

noncomputable def distMaxSet (G : SimpleGraph α) (S : Set α) : ℕ :=
  open scoped Classical in
  let members := Finset.univ.filter (fun v : α => v ∈ S)
  (members ×ˢ members).sup (fun p => G.dist p.1 p.2)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture18

open SimpleGraph

/-- Greedy lemma (from wowii17). -/
lemma comb : ∀ (n : ℕ) (P : ℕ → Prop), (∀ i < n, ¬(P i ∧ P (i + 1))) →
    ∃ S : Finset ℕ, (∀ i ∈ S, i ≤ n ∧ ¬ P i) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → i + 2 ≤ j) ∧
      n ≤ 3 * S.card := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP
  by_cases h0 : P 0
  · by_cases hn : n = 0
    · exact ⟨∅, by simp, by simp, by simp [hn]⟩
    have h1 : ¬ P 1 := fun h1 => hP 0 (by omega) ⟨h0, h1⟩
    by_cases hn3 : n < 3
    · refine ⟨{1}, ?_, ?_, ?_⟩
      · intro i hi; rw [Finset.mem_singleton] at hi; subst hi; exact ⟨by omega, h1⟩
      · intro i hi j hj hij; rw [Finset.mem_singleton] at hi hj; omega
      · simp; omega
    obtain ⟨S', h1', h2', h3'⟩ := ih (n - 3) (by omega) (fun i => P (i + 3))
      (fun i hi => hP (i + 3) (by omega))
    have hnot : (1 : ℕ) ∉ S'.image (· + 3) := by
      simp only [Finset.mem_image, not_exists, not_and]; intro x _; omega
    refine ⟨insert 1 (S'.image (· + 3)), ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_image] at hi
      rcases hi with rfl | ⟨x, hx, rfl⟩
      · exact ⟨by omega, h1⟩
      · exact ⟨by have := (h1' x hx).1; omega, (h1' x hx).2⟩
    · intro i hi j hj hij
      simp only [Finset.mem_insert, Finset.mem_image] at hi hj
      rcases hi with rfl | ⟨x, hx, rfl⟩ <;> rcases hj with rfl | ⟨y, hy, rfl⟩
      · omega
      · omega
      · omega
      · have := h2' x hx y hy (by omega); omega
    · rw [Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
      omega
  · by_cases hn2 : n < 2
    · refine ⟨{0}, ?_, ?_, ?_⟩
      · intro i hi; rw [Finset.mem_singleton] at hi; subst hi; exact ⟨by omega, h0⟩
      · intro i hi j hj hij; rw [Finset.mem_singleton] at hi hj; omega
      · simp; omega
    obtain ⟨S', h1', h2', h3'⟩ := ih (n - 2) (by omega) (fun i => P (i + 2))
      (fun i hi => hP (i + 2) (by omega))
    have hnot : (0 : ℕ) ∉ S'.image (· + 2) := by
      simp only [Finset.mem_image, not_exists, not_and]; intro x _; omega
    refine ⟨insert 0 (S'.image (· + 2)), ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_image] at hi
      rcases hi with rfl | ⟨x, hx, rfl⟩
      · exact ⟨by omega, h0⟩
      · exact ⟨by have := (h1' x hx).1; omega, (h1' x hx).2⟩
    · intro i hi j hj hij
      simp only [Finset.mem_insert, Finset.mem_image] at hi hj
      rcases hi with rfl | ⟨x, hx, rfl⟩ <;> rcases hj with rfl | ⟨y, hy, rfl⟩
      · omega
      · omega
      · omega
      · have := h2' x hx y hy (by omega); omega
    · rw [Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
      omega

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- Vertices along a geodesic from `u` to `v`. -/
lemma geoWalk (G : SimpleGraph α) (h : G.Connected) (u v : α) :
    ∃ f : ℕ → α, (∀ k ≤ G.dist u v, G.dist u (f k) = k ∧ G.dist (f k) v = G.dist u v - k) ∧
      ∀ k < G.dist u v, G.Adj (f k) (f (k + 1)) := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  refine ⟨p.getVert, fun k hk => ?_, fun k hk => p.adj_getVert_succ (by omega)⟩
  have h1 : G.dist u (p.getVert k) ≤ k := by
    have := SimpleGraph.dist_le (p.take k)
    rw [Walk.take_length] at this
    exact this.trans inf_le_left
  have h2 : G.dist (p.getVert k) v ≤ G.dist u v - k := by
    have := SimpleGraph.dist_le (p.drop k)
    rw [Walk.drop_length, hp] at this
    exact this
  have h3 := h.dist_triangle (u := u) (v := p.getVert k) (w := v)
  omega

omit [Fintype α] [DecidableEq α] in
lemma dist_adj {G : SimpleGraph α} (h : G.Connected) {u x y : α} (hxy : G.Adj x y) :
    G.dist u y ≤ G.dist u x + 1 := by
  have := h.dist_triangle (u := u) (v := x) (w := y)
  rw [dist_eq_one_iff_adj.mpr hxy] at this
  exact this

omit [Fintype α] [DecidableEq α] in
lemma far2 {G : SimpleGraph α} {x y : α} (hd : 2 ≤ G.dist x y) : x ≠ y ∧ ¬ G.Adj x y :=
  ⟨by rintro rfl; rw [SimpleGraph.dist_self] at hd; omega,
   fun hadj => by rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at hd; omega⟩

/-- An independent set `T` outside a maximum independent set `I` gives `α + |T| ≤ b`. -/
lemma gain (G : SimpleGraph α) (I T : Finset α) (hI : G.IsNIndepSet G.indepNum I)
    (hTI : ∀ x ∈ T, x ∉ I) (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y) :
    (G.indepNum : ℝ) + T.card ≤ b G := by
  have hdisj : Disjoint I T := Finset.disjoint_right.2 (fun x hx => hTI x hx)
  have hbip : (G.induce ((I ∪ T : Finset α) : Set α)).IsBipartite := by
    rw [induce_isBipartite_iff_exists_coloring]
    refine ⟨fun x => if x ∈ I then 0 else 1, ?_⟩
    intro x hx y hy hxy
    by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I <;> simp only [hxI, hyI, if_true, if_false]
    · exact absurd hxy (hI.isIndepSet hxI hyI hxy.ne)
    · decide
    · decide
    · have hxT : x ∈ T := by
        rcases Finset.mem_union.1 hx with h' | h'
        · exact absurd h' hxI
        · exact h'
      have hyT : y ∈ T := by
        rcases Finset.mem_union.1 hy with h' | h'
        · exact absurd h' hyI
        · exact h'
      exact absurd hxy (hT x hxT y hyT)
  have hb : ((I ∪ T).card : ℝ) ≤ b G := by
    unfold b largestInducedBipartiteSubgraphSize
    have hmem : (I ∪ T).card ∈
        { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n } := ⟨I ∪ T, hbip, rfl⟩
    have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n } :=
      ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    exact_mod_cast le_csSup hbdd hmem
  have hcard : (I ∪ T).card = I.card + T.card := by
    have := Finset.card_union_add_card_inter I T
    rw [Finset.disjoint_iff_inter_eq_empty.1 hdisj, Finset.card_empty] at this
    omega
  rw [hcard] at hb
  push_cast at hb
  rw [hI.card_eq] at hb
  exact hb

lemma gain2 (G : SimpleGraph α) (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) (a c : α)
    (ha : a ∉ I) (hc : c ∉ I) (hac : a ≠ c) (hn : ¬ G.Adj a c) :
    (G.indepNum : ℝ) + (2 : ℕ) ≤ b G := by
  have := gain G I {a, c} hI (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    (by
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy.ne rfl
      · exact hn hxy
      · exact hn hxy.symm
      · exact hxy.ne rfl)
  rwa [Finset.card_pair hac] at this

lemma gain3 (G : SimpleGraph α) (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) (a c e : α)
    (ha : a ∉ I) (hc : c ∉ I) (he : e ∉ I) (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a e) (n3 : ¬ G.Adj c e) :
    (G.indepNum : ℝ) + (3 : ℕ) ≤ b G := by
  have := gain G I {a, c, e} hI (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    (by
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
        | exact hxy.ne rfl
        | exact n1 hxy | exact n1 hxy.symm
        | exact n2 hxy | exact n2 hxy.symm
        | exact n3 hxy | exact n3 hxy.symm)
  rwa [Finset.card_eq_three.2 ⟨a, c, e, hac, hae, hce, rfl⟩] at this

/-- The geodesic argument of conjecture 17, for any pair `u v`. -/
lemma core17 (G : SimpleGraph α) (h : G.Connected) (u v : α) :
    ∃ s : ℕ, G.dist u v ≤ 3 * s ∧ (G.indepNum : ℝ) + s ≤ b G := by
  classical
  obtain ⟨f, hf, hfa⟩ := geoWalk G h u v
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨S, hS1, hS2, hS3⟩ := comb (G.dist u v) (fun i => f i ∈ I) (by
    intro i hi ⟨h1, h2⟩
    exact hI.isIndepSet h1 h2 (hfa i hi).ne (hfa i hi))
  have hinj : Set.InjOn f S := by
    intro i hi j hj hij
    have ha := (hf i (hS1 i hi).1).1
    have hb := (hf j (hS1 j hj).1).1
    rw [hij] at ha
    omega
  have hTcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hTI : ∀ x ∈ S.image f, x ∉ I := by
    intro x hxT hxI
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hxT
    exact (hS1 i hi).2 hxI
  have hTind : ∀ x ∈ S.image f, ∀ y ∈ S.image f, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    have ha := (hf i (hS1 i hi).1).1
    have hb := (hf j (hS1 j hj).1).1
    rcases lt_trichotomy i j with hij | hij | hij
    · have := hS2 i hi j hj hij
      have := dist_adj h (u := u) hxy
      omega
    · subst hij; exact hxy.ne rfl
    · have := hS2 j hj i hi hij
      have := dist_adj h (u := u) hxy.symm
      omega
  refine ⟨S.card, hS3, ?_⟩
  have := gain G I (S.image f) hI hTI hTind
  rwa [hTcard] at this

/-- A maximum-degree vertex with a vertex at distance ≥ 2 has two non-adjacent neighbours. -/
lemma endpt (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (u w : α)
    (hu : G.degree u = G.maxDegree) (hw : 2 ≤ G.dist u w) :
    ∃ x y, G.Adj u x ∧ G.Adj u y ∧ x ≠ y ∧ ¬ G.Adj x y := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨f, hf, hfa⟩ := geoWalk G h u w
  have h1 := (hf 1 (by omega)).1
  have h2 := (hf 2 hw).1
  have hu1 : G.Adj u (f 1) := dist_eq_one_iff_adj.1 h1
  have h12 : G.Adj (f 1) (f 2) := hfa 1 (by omega)
  have hsub : insert u (insert (f 2) ((G.neighborFinset u).erase (f 1))) ⊆
      G.neighborFinset (f 1) := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz
    rcases hz with hz | hz | ⟨hz1, hz2⟩
    · rw [hz]; exact hu1.symm
    · rw [hz]; exact h12
    · exact hcon _ _ hu1 hz2 (Ne.symm hz1)
  have hp2 : f 2 ∉ (G.neighborFinset u).erase (f 1) := by
    intro hm
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hm
    rw [dist_eq_one_iff_adj.2 hm.2] at h2
    omega
  have hu0 : u ∉ insert (f 2) ((G.neighborFinset u).erase (f 1)) := by
    intro hm
    rw [Finset.mem_insert, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hm
    rcases hm with hm | ⟨_, hm⟩
    · rw [← hm, SimpleGraph.dist_self] at h2; omega
    · exact hm.ne rfl
  have hmem : f 1 ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hu1
  have hpos : 0 < (G.neighborFinset u).card := Finset.card_pos.2 ⟨_, hmem⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hu0, Finset.card_insert_of_notMem hp2,
    Finset.card_erase_of_mem hmem] at hc
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc hpos
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have := G.degree_le_maxDegree (f 1)
  omega

lemma caseB2 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (I : Finset α)
    (hI : G.IsNIndepSet G.indepNum I) (u w : α) (hu : G.degree u = G.maxDegree)
    (huI : u ∈ I) (hw : 2 ≤ G.dist u w) :
    (G.indepNum : ℝ) + (2 : ℕ) ≤ b G := by
  obtain ⟨x, y, hx, hy, hxy, hn⟩ := endpt G h u w hu hw
  have nI : ∀ z, G.Adj u z → z ∉ I := fun z hz hzI => hI.isIndepSet huI hzI hz.ne hz
  exact gain2 G I hI x y (nI x hx) (nI y hy) hxy hn

lemma caseB3 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (I : Finset α)
    (hI : G.IsNIndepSet G.indepNum I) (u w : α) (hu : G.degree u = G.maxDegree)
    (huI : u ∈ I) (hwI : w ∉ I) (hw : 3 ≤ G.dist u w) :
    (G.indepNum : ℝ) + (3 : ℕ) ≤ b G := by
  obtain ⟨x, y, hx, hy, hxy, hn⟩ := endpt G h u w hu (by omega)
  have nI : ∀ z, G.Adj u z → z ∉ I := fun z hz hzI => hI.isIndepSet huI hzI hz.ne hz
  have far : ∀ z, G.Adj u z → ¬ G.Adj z w := fun z hz hzw => by
    have := dist_adj h (u := u) hzw
    rw [dist_eq_one_iff_adj.2 hz] at this
    omega
  have nez : ∀ z, G.Adj u z → z ≠ w := fun z hz hzw => by
    subst hzw
    rw [dist_eq_one_iff_adj.2 hz] at hw
    omega
  exact gain3 G I hI x y w (nI x hx) (nI y hy) hwI hxy (nez x hx) (nez y hy) hn
    (far x hx) (far y hy)

lemma two_case (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (I : Finset α)
    (hI : G.IsNIndepSet G.indepNum I) (u v : α) (hu : G.degree u = G.maxDegree)
    (hv : G.degree v = G.maxDegree) (hd : 2 ≤ G.dist u v) :
    (G.indepNum : ℝ) + (2 : ℕ) ≤ b G := by
  by_cases huI : u ∈ I
  · exact caseB2 G h I hI u v hu huI hd
  by_cases hvI : v ∈ I
  · exact caseB2 G h I hI v u hv hvI (by rw [SimpleGraph.dist_comm]; exact hd)
  exact gain2 G I hI u v huI hvI (far2 hd).1 (far2 hd).2

lemma endA (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (I : Finset α)
    (hI : G.IsNIndepSet G.indepNum I) (u v : α) (hu : G.degree u = G.maxDegree)
    (huI : u ∈ I) (hd : 5 ≤ G.dist u v) :
    (G.indepNum : ℝ) + (3 : ℕ) ≤ b G := by
  obtain ⟨f, hf, hfa⟩ := geoWalk G h u v
  have h34 : f 3 ∉ I ∨ f 4 ∉ I := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hI.isIndepSet hc.1 hc.2 (hfa 3 (by omega)).ne (hfa 3 (by omega))
  rcases h34 with h3 | h4
  · exact caseB3 G h I hI u (f 3) hu huI h3 (by have := (hf 3 (by omega)).1; omega)
  · exact caseB3 G h I hI u (f 4) hu huI h4 (by have := (hf 4 (by omega)).1; omega)

lemma three_case (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (I : Finset α)
    (hI : G.IsNIndepSet G.indepNum I) (u v : α) (hu : G.degree u = G.maxDegree)
    (hv : G.degree v = G.maxDegree) (hd : 5 ≤ G.dist u v) :
    (G.indepNum : ℝ) + (3 : ℕ) ≤ b G := by
  by_cases huI : u ∈ I
  · exact endA G h I hI u v hu huI hd
  by_cases hvI : v ∈ I
  · exact endA G h I hI v u hv hvI (by rw [SimpleGraph.dist_comm]; exact hd)
  obtain ⟨f, hf, hfa⟩ := geoWalk G h u v
  have key : ∀ k, 2 ≤ k → k ≤ 3 → f k ∉ I → (G.indepNum : ℝ) + (3 : ℕ) ≤ b G := by
    intro k hk2 hk3 hkI
    have a1 := (hf k (by omega)).1
    have a2 := (hf k (by omega)).2
    have e1 : 2 ≤ G.dist u (f k) := by omega
    have e2 : 2 ≤ G.dist (f k) v := by omega
    have e3 : 2 ≤ G.dist u v := by omega
    exact gain3 G I hI u (f k) v huI hkI hvI (far2 e1).1 (far2 e3).1 (far2 e2).1
      (far2 e1).2 (far2 e3).2 (far2 e2).2
  have h23 : f 2 ∉ I ∨ f 3 ∉ I := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hI.isIndepSet hc.1 hc.2 (hfa 2 (by omega)).ne (hfa 2 (by omega))
  rcases h23 with h2 | h3
  · exact key 2 le_rfl (by omega) h2
  · exact key 3 (by omega) le_rfl h3

omit [Fintype α] [DecidableEq α] in
lemma sup_aux (G : SimpleGraph α) (M : Set α) (s : Finset (α × α))
    (hs : ∀ p ∈ s, p.1 ∈ M ∧ p.2 ∈ M) (h0 : s.sup (fun p => G.dist p.1 p.2) ≠ 0) :
    ∃ u v, u ∈ M ∧ v ∈ M ∧ G.dist u v = s.sup (fun p => G.dist p.1 p.2) := by
  rcases s.eq_empty_or_nonempty with he | hne
  · subst he; simp at h0
  obtain ⟨q, hq, hq'⟩ := Finset.exists_mem_eq_sup s hne (fun p => G.dist p.1 p.2)
  exact ⟨q.1, q.2, (hs q hq).1, (hs q hq).2, hq'.symm⟩

lemma hex (G : SimpleGraph α) (M : Set α) (h0 : distMaxSet G M ≠ 0) :
    ∃ u v, u ∈ M ∧ v ∈ M ∧ G.dist u v = distMaxSet G M := by
  unfold distMaxSet at h0 ⊢
  exact sup_aux G M _ (fun p hp => by
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp) h0

lemma ceil_sqrt_le (D k : ℕ) (h : D ≤ k * k) : ⌈Real.sqrt (D : ℝ)⌉ ≤ (k : ℤ) := by
  rw [Int.ceil_le]
  have h1 : Real.sqrt (D : ℝ) ≤ Real.sqrt ((k : ℝ) * k) :=
    Real.sqrt_le_sqrt (by exact_mod_cast h)
  rw [Real.sqrt_mul_self (Nat.cast_nonneg k)] at h1
  exact_mod_cast h1

variable [Nontrivial α]

theorem conjecture18 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let M : Set α := {v | G.degree v = G.maxDegree}
    (G.indepNum : ℝ) + ⌈Real.sqrt (distMaxSet G M : ℝ)⌉ ≤ b G := by
  intro M
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, distMaxSet G M ≤ k * k ∧ (G.indepNum : ℝ) + k ≤ b G := by
    by_cases h0 : distMaxSet G M = 0
    · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
      refine ⟨0, by omega, ?_⟩
      have := gain G I ∅ hI (by simp) (by simp)
      simpa using this
    obtain ⟨u, v, hu, hv, huv⟩ := hex G M h0
    have hu' : G.degree u = G.maxDegree := hu
    have hv' : G.degree v = G.maxDegree := hv
    rw [← huv]
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    by_cases h23 : G.dist u v = 2 ∨ G.dist u v = 3
    · exact ⟨2, by omega, two_case G h I hI u v hu' hv' (by omega)⟩
    by_cases h56 : G.dist u v = 5 ∨ G.dist u v = 6
    · exact ⟨3, by omega, three_case G h I hI u v hu' hv' (by omega)⟩
    obtain ⟨s, hs1, hs2⟩ := core17 G h u v
    refine ⟨s, ?_, hs2⟩
    rcases Nat.lt_or_ge (G.dist u v) 9 with hlt | hge
    · rcases Nat.lt_or_ge s 3 with h' | h'
      · interval_cases s <;> omega
      · have : 3 * 3 ≤ s * s := Nat.mul_le_mul h' h'
        omega
    · have : 3 * s ≤ s * s := Nat.mul_le_mul (by omega) le_rfl
      omega
  have h1 := ceil_sqrt_le _ _ hk1
  have h2 : ((⌈Real.sqrt (distMaxSet G M : ℝ)⌉ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
  linarith

end WrittenOnTheWallII.GraphConjecture18

#print axioms WrittenOnTheWallII.GraphConjecture18.conjecture18
