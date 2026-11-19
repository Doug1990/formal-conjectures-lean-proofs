import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean
and Independence.lean). -/
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

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture13

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Nontrivial α] in
lemma b_ge (G : SimpleGraph α) (S : Finset α) (c : α → Fin 2)
    (hc : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y) : (S.card : ℝ) ≤ b G := by
  have hbip : (G.induce (S : Set α)).IsBipartite :=
    (induce_isBipartite_iff_exists_coloring G S).2 ⟨c, hc⟩
  unfold b largestInducedBipartiteSubgraphSize
  have hmem : S.card ∈
      { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n } := ⟨S, hbip, rfl⟩
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n } :=
    ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact_mod_cast le_csSup hbdd hmem

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
/-- An independent set of size `l(v)` inside `N(v)`. -/
lemma nbhd_indep (G : SimpleGraph α) (v : α) : ∃ I : Finset α, I.card = indepNeighborsCard G v ∧
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

theorem conjecture13 (G : SimpleGraph α) (h : G.Connected) :
    letI maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.diam : ℝ) + (maxL : ℝ) - 1 ≤ b G := by
  classical
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1
    (Finset.max'_mem (Finset.univ.image (fun v => indepNeighborsCard G v)) (by simp))
  obtain ⟨I, hIc, hIv, hIind⟩ := nbhd_indep G v
  obtain ⟨u, w, huw⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u w
  set d := G.diam with hd
  have hdist : ∀ k ≤ d, G.dist u (p.getVert k) = k := by
    intro k hk
    have h1 : G.dist u (p.getVert k) ≤ k := by
      have := SimpleGraph.dist_le (p.take k)
      rw [Walk.take_length] at this
      exact this.trans inf_le_left
    have h2 : G.dist (p.getVert k) w ≤ d - k := by
      have := SimpleGraph.dist_le (p.drop k)
      rw [Walk.drop_length, hp, huw] at this
      exact this
    have h3 := h.dist_triangle (u := u) (v := p.getVert k) (w := w)
    omega
  have hadj : ∀ x y, G.Adj x y → G.dist u y ≤ G.dist u x + 1 := by
    intro x y hxy
    have := h.dist_triangle (u := u) (v := x) (w := y)
    rw [dist_eq_one_iff_adj.mpr hxy] at this
    exact this
  set k := G.dist u v with hk
  set F := (Finset.range (d + 1)).filter (fun i => i + 2 ≤ k ∨ k + 2 ≤ i) with hF
  set T := F.image p.getVert with hT
  have hFd : ∀ i ∈ F, i ≤ d ∧ (i + 2 ≤ k ∨ k + 2 ≤ i) := by
    intro i hi
    rw [hF, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨by omega, hi.2⟩
  have hinj : Set.InjOn p.getVert F := by
    intro i hi j hj hij
    have a := hdist i (hFd i hi).1
    have b := hdist j (hFd j hj).1
    rw [hij] at a
    omega
  have hTcard : T.card = F.card := Finset.card_image_of_injOn hinj
  have hFcard : d + 1 ≤ F.card + 3 := by
    have hsub : Finset.range (d + 1) ⊆ F ∪ {k - 1, k, k + 1} := by
      intro i hi
      rw [Finset.mem_union]
      by_cases h' : i + 2 ≤ k ∨ k + 2 ≤ i
      · left; rw [hF, Finset.mem_filter]; exact ⟨hi, h'⟩
      · right; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le F ({k - 1, k, k + 1} : Finset ℕ)
    have h3 : ({k - 1, k, k + 1} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_range] at h1
    omega
  have hTmem : ∀ y ∈ T, ∃ i, (i + 2 ≤ k ∨ k + 2 ≤ i) ∧ G.dist u y = i := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨i, (hFd i hi).2, hdist i (hFd i hi).1⟩
  have hInear : ∀ a ∈ I, G.dist u a ≤ k + 1 ∧ k ≤ G.dist u a + 1 := by
    intro a ha
    exact ⟨hadj v a (hIv a ha), hadj a v (hIv a ha).symm⟩
  have hvI : v ∉ I := fun h' => (hIv v h').ne rfl
  have hvT : v ∉ T := by
    intro h'
    obtain ⟨i, hi, hi'⟩ := hTmem v h'
    rw [← hk] at hi'
    omega
  have hIT : Disjoint I T := by
    rw [Finset.disjoint_left]
    intro a ha haT
    obtain ⟨i, hi, hi'⟩ := hTmem a haT
    have := hInear a ha
    omega
  set S := insert v (I ∪ T) with hS
  have hScard : S.card = 1 + I.card + T.card := by
    rw [hS, Finset.card_insert_of_notMem (by
      rw [Finset.mem_union]; rintro (h' | h'); exact hvI h'; exact hvT h'),
      Finset.card_union_of_disjoint hIT]
    omega
  let f : α → ℕ := fun x => if x = v then k else if x ∈ I then k + 1 else G.dist u x
  have hmemS : ∀ x ∈ S, x = v ∨ (x ≠ v ∧ x ∈ I) ∨ (x ≠ v ∧ x ∉ I ∧ x ∈ T) := by
    intro x hx
    rw [hS, Finset.mem_insert, Finset.mem_union] at hx
    by_cases h1 : x = v
    · exact Or.inl h1
    by_cases h2 : x ∈ I
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    rcases hx with h' | h' | h'
    · exact absurd h' h1
    · exact absurd h' h2
    · exact Or.inr (Or.inr ⟨h1, h2, h'⟩)
  have hcol : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → f x % 2 ≠ f y % 2 := by
    intro x hx y hy hxy
    have hxy1 := hadj x y hxy
    have hxy2 := hadj y x hxy.symm
    rcases hmemS x hx with rfl | ⟨hx1, hx2⟩ | ⟨hx1, hx2, hx3⟩ <;>
      rcases hmemS y hy with rfl | ⟨hy1, hy2⟩ | ⟨hy1, hy2, hy3⟩
    · exact absurd hxy (G.loopless.irrefl _)
    · simp only [f, if_pos rfl, if_neg hy1, if_pos hy2]; omega
    · simp only [f, if_pos rfl, if_neg hy1, if_neg hy2]
      obtain ⟨i, hi, hi'⟩ := hTmem y hy3
      omega
    · simp only [f, if_pos rfl, if_neg hx1, if_pos hx2]; omega
    · exact absurd hxy (hIind x hx2 y hy2)
    · simp only [f, if_neg hx1, if_pos hx2, if_neg hy1, if_neg hy2]
      obtain ⟨i, hi, hi'⟩ := hTmem y hy3
      have := hInear x hx2
      omega
    · simp only [f, if_pos rfl, if_neg hx1, if_neg hx2]
      obtain ⟨i, hi, hi'⟩ := hTmem x hx3
      omega
    · simp only [f, if_neg hx1, if_pos hy2, if_neg hy1, if_neg hx2]
      obtain ⟨i, hi, hi'⟩ := hTmem x hx3
      have := hInear y hy2
      omega
    · simp only [f, if_neg hx1, if_neg hy1, if_neg hy2, if_neg hx2]
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx3
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy3
      have a := hdist i (hFd i hi).1
      have b := hdist j (hFd j hj).1
      have hne : i ≠ j := fun hij => hxy.ne (by rw [hij])
      omega
  have hb := b_ge G S (fun x => ⟨f x % 2, Nat.mod_lt _ (by norm_num)⟩) (by
    intro x hx y hy hxy heq
    exact hcol x hx y hy hxy (Fin.mk.inj_iff.1 heq))
  rw [hScard, hTcard] at hb
  push_cast at hb
  have hFr : ((d : ℕ) : ℝ) + 1 ≤ (F.card : ℝ) + 3 := by exact_mod_cast hFcard
  rw [← hv, ← hIc]
  linarith

end WrittenOnTheWallII.GraphConjecture13

#print axioms WrittenOnTheWallII.GraphConjecture13.conjecture13
