import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean). -/
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

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture17

open SimpleGraph

/-- Greedy lemma: on indices `0..n`, if `P` never holds at two consecutive indices, there is a
set `S` of indices avoiding `P`, with gaps ≥ 2, and `n ≤ 3 |S|`. -/
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

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture17 (G : SimpleGraph α) (h : G.Connected) :
    (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  set d := G.diam with hd
  have hdist : ∀ k ≤ d, G.dist u (p.getVert k) = k := by
    intro k hk
    have h1 : G.dist u (p.getVert k) ≤ k := by
      have := SimpleGraph.dist_le (p.take k)
      rw [Walk.take_length] at this
      exact this.trans inf_le_left
    have h2 : G.dist (p.getVert k) v ≤ d - k := by
      have := SimpleGraph.dist_le (p.drop k)
      rw [Walk.drop_length, hp, huv] at this
      exact this
    have h3 := h.dist_triangle (u := u) (v := p.getVert k) (w := v)
    omega
  have hadj : ∀ x y, G.Adj x y → G.dist u y ≤ G.dist u x + 1 := by
    intro x y hxy
    have := h.dist_triangle (u := u) (v := x) (w := y)
    rw [dist_eq_one_iff_adj.mpr hxy] at this
    exact this
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨S, hS1, hS2, hS3⟩ := comb d (fun i => p.getVert i ∈ I) (by
    intro i hi ⟨h1, h2⟩
    have hl : i < p.length := by rw [hp, huv]; exact hi
    exact hI.isIndepSet h1 h2 (p.adj_getVert_succ hl).ne (p.adj_getVert_succ hl))
  set T := S.image p.getVert with hT
  have hinj : Set.InjOn p.getVert S := by
    intro i hi j hj hij
    have a := hdist i (hS1 i hi).1
    have b := hdist j (hS1 j hj).1
    rw [hij] at a
    omega
  have hTcard : T.card = S.card := Finset.card_image_of_injOn hinj
  have hdisj : Disjoint I T := by
    rw [Finset.disjoint_left]
    intro x hxI hxT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hxT
    exact (hS1 i hi).2 hxI
  have hTind : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    have a := hdist i (hS1 i hi).1
    have b := hdist j (hS1 j hj).1
    rcases lt_trichotomy i j with hij | hij | hij
    · have := hS2 i hi j hj hij
      have := hadj _ _ hxy
      omega
    · subst hij; exact hxy.ne rfl
    · have := hS2 j hj i hi hij
      have := hadj _ _ hxy.symm
      omega
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
      exact absurd hxy (hTind x hxT y hyT)
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
  have hc : ⌈(d : ℝ) / 3⌉ ≤ (S.card : ℤ) := by
    rw [Int.ceil_le, div_le_iff₀ (by norm_num)]
    have : d ≤ S.card * 3 := by omega
    exact_mod_cast this
  have hc' : ((⌈(d : ℝ) / 3⌉ : ℤ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hc
  rw [hcard] at hb
  push_cast at hb
  rw [hI.card_eq, hTcard] at hb
  linarith

end WrittenOnTheWallII.GraphConjecture17

#print axioms WrittenOnTheWallII.GraphConjecture17.conjecture17
