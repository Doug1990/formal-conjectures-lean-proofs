import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

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

namespace WrittenOnTheWallII.GraphConjecture20

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
/-- Cauchy–Schwarz in the form `|S|² ≤ (Σ 1/w)(Σ w)`, via a tangent-line bound. -/
lemma cs (S : Finset α) (w : α → ℝ) (hw : ∀ v ∈ S, 0 < w v) :
    (S.card : ℝ) ^ 2 ≤ (∑ v ∈ S, 1 / w v) * ∑ v ∈ S, w v := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hW : 0 < ∑ v ∈ S, w v := Finset.sum_pos hw hne
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ v ∈ S, w v := ⟨_, rfl⟩
  rw [← hWd] at hW ⊢
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (S.card : ℝ) / W := ⟨_, rfl⟩
  have key : ∀ v ∈ S, 2 * t - t ^ 2 * w v ≤ 1 / w v := by
    intro v hv
    have := hw v hv
    rw [le_div_iff₀ this]
    nlinarith [sq_nonneg (1 - t * w v)]
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hWd, Finset.sum_const,
    nsmul_eq_mul] at hs
  have e : 2 * ((S.card : ℝ) * t) - t ^ 2 * W = (S.card : ℝ) ^ 2 / W := by
    rw [ht]; field_simp; ring
  have : (S.card : ℝ) ^ 2 / W ≤ ∑ v ∈ S, 1 / w v := by linarith
  rwa [div_le_iff₀ hW] at this

omit [Fintype α] [Nontrivial α] in
/-- Caro–Wei greedy: a maximal independent `I ⊆ S` with `Σ_{v ∈ S} 1/(d_S(v)+1) ≤ |I|`. -/
lemma caroWei (G : SimpleGraph α) [DecidableRel G.Adj] (n : ℕ) :
    ∀ S : Finset α, S.card = n → ∃ I ⊆ S, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      (∀ u ∈ S, u ∉ I → ∃ w ∈ I, G.Adj u w) ∧
      ∑ v ∈ S, (1 : ℝ) / ((S.filter (G.Adj v)).card + 1) ≤ I.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun u => (S.filter (G.Adj u)).card) hne
  obtain ⟨N, hN⟩ : ∃ N, N = insert v (S.filter (G.Adj v)) := ⟨_, rfl⟩
  have hNS : N ⊆ S := hN ▸ Finset.insert_subset hv (Finset.filter_subset _ _)
  have hTlt : (S \ N).card < n := by
    rw [← hS]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hNS ⟨v, hN ▸ Finset.mem_insert_self _ _⟩)
  have memT : ∀ x, x ∈ S \ N ↔ x ∈ S ∧ x ≠ v ∧ ¬ G.Adj v x := by
    intro x
    rw [Finset.mem_sdiff, hN, Finset.mem_insert, Finset.mem_filter]
    tauto
  obtain ⟨J, hJT, hJind, hJdom, hJsum⟩ := ih _ hTlt (S \ N) rfl
  have hvJ : v ∉ J := fun h => ((memT v).1 (hJT h)).2.1 rfl
  refine ⟨insert v J, ?_, ?_, ?_, ?_⟩
  · exact Finset.insert_subset hv (hJT.trans Finset.sdiff_subset)
  · intro a ha c hc hac
    rw [Finset.mem_insert] at ha hc
    rcases ha with rfl | ha <;> rcases hc with rfl | hc
    · exact hac.ne rfl
    · exact ((memT c).1 (hJT hc)).2.2 hac
    · exact ((memT a).1 (hJT ha)).2.2 hac.symm
    · exact hJind a ha c hc hac
  · intro u hu huI
    by_cases huv : G.Adj u v
    · exact ⟨v, Finset.mem_insert_self _ _, huv⟩
    · have huT : u ∈ S \ N := (memT u).2 ⟨hu, fun h => huI (h ▸ Finset.mem_insert_self _ _),
        fun h => huv h.symm⟩
      obtain ⟨w, hw, huw⟩ := hJdom u huT (fun h => huI (Finset.mem_insert_of_mem h))
      exact ⟨w, Finset.mem_insert_of_mem hw, huw⟩
  · rw [Finset.card_insert_of_notMem hvJ]
    have h1 := Finset.sum_sdiff hNS (f := fun x => (1 : ℝ) / ((S.filter (G.Adj x)).card + 1))
    have hvN : v ∉ S.filter (G.Adj v) := fun h => (Finset.mem_filter.1 h).2.ne rfl
    have hcardN : (N.card : ℝ) = (S.filter (G.Adj v)).card + 1 := by
      rw [hN, Finset.card_insert_of_notMem hvN]; push_cast; ring
    have h2 : ∑ x ∈ N, (1 : ℝ) / ((S.filter (G.Adj x)).card + 1) ≤ 1 := by
      calc ∑ x ∈ N, (1 : ℝ) / ((S.filter (G.Adj x)).card + 1)
          ≤ ∑ x ∈ N, (1 : ℝ) / ((S.filter (G.Adj v)).card + 1) := by
            apply Finset.sum_le_sum
            intro x hx
            apply one_div_le_one_div_of_le (by positivity)
            have := hmin x (hNS hx)
            exact_mod_cast Nat.add_le_add_right this 1
        _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul, ← hcardN]
            have : (0 : ℝ) < N.card := by rw [hcardN]; positivity
            field_simp
    have h3 : ∑ x ∈ S \ N, (1 : ℝ) / ((S.filter (G.Adj x)).card + 1) ≤
        ∑ x ∈ S \ N, (1 : ℝ) / (((S \ N).filter (G.Adj x)).card + 1) := by
      apply Finset.sum_le_sum
      intro x _
      apply one_div_le_one_div_of_le (by positivity)
      have : ((S \ N).filter (G.Adj x)).card ≤ (S.filter (G.Adj x)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      exact_mod_cast Nat.add_le_add_right this 1
    push_cast
    linarith

/-- The final real inequality. -/
lemma arith (n c k a x y : ℝ) (hn : 0 < n) (hax : a + x = n) (hx : 0 ≤ x) (ha0 : 0 ≤ a)
    (ha : n ^ 2 ≤ a * (c + n)) (hy : x ^ 2 ≤ y * (c - x)) (hy0 : 0 ≤ y) (hk : 2 ≤ k)
    (hc1 : k * n ≤ c) (hc2 : c < (k + 1) * n) : n ≤ k * (a + y) := by
  have ha' : a = n - x := by linarith
  subst ha'
  have hc0 : 0 < c := by nlinarith
  have hcx : 0 < c - x := by nlinarith
  have L0 : c ^ 2 * y * (c - x) ≥ (2 * n * c * x - n ^ 2 * (c - x)) * (c - x) := by
    nlinarith [sq_nonneg (c * x - n * (c - x)), mul_le_mul_of_nonneg_left hy (sq_nonneg c)]
  have L1 : c ^ 2 * y ≥ 2 * n * c * x - n ^ 2 * (c - x) := le_of_mul_le_mul_right L0 hcx
  have M : c ^ 2 * ((n - x) + y) ≥ c ^ 2 * n - n ^ 2 * c + x * (2 * n * c + n ^ 2 - c ^ 2) := by
    nlinarith [L1]
  rcases le_or_gt 0 (2 * n * c + n ^ 2 - c ^ 2) with hQ | hQ
  · have hM : c ^ 2 * ((n - x) + y) ≥ c * n * (c - n) := by nlinarith [mul_nonneg hx hQ]
    have h3 : 0 ≤ (k - 1) * c - k * n := by nlinarith
    have h4 : 0 ≤ c * n * ((k - 1) * c - k * n) := mul_nonneg (mul_nonneg hc0.le hn.le) h3
    have h5 := mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ k)
    have h2 : c ^ 2 * n ≤ c ^ 2 * (k * ((n - x) + y)) := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  · have hxb : x * (c + n) ≤ n * c := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left M (by positivity : (0 : ℝ) ≤ c + n)
    have h6 := mul_le_mul_of_nonpos_left hxb hQ.le
    have h7 : (c + n) * ((n - x) + y) * c ^ 2 ≥ 2 * n ^ 2 * c ^ 2 := by nlinarith
    have h8 : 2 * n ^ 2 ≤ (c + n) * ((n - x) + y) :=
      le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < c ^ 2)
    have h9 : (c + n) * ((n - x) + y) ≤ (2 * k * n) * ((n - x) + y) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have h10 : (2 * n) * n ≤ (2 * n) * (k * ((n - x) + y)) := by nlinarith
    exact le_of_mul_le_mul_left h10 (by linarith)

theorem conjecture20 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let deg_avg : ℝ := (∑ v : α, (G.degree v : ℝ)) / (Fintype.card α : ℝ)
    (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤ (b G : ℝ) := by
  intro deg_avg
  have hb0 : (0 : ℝ) ≤ b G := by
    have := b_ge G ∅ (fun _ => 0) (by simp)
    simpa using this
  have hn2 : 1 < Fintype.card α := Fintype.one_lt_card
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast (by omega : 0 < Fintype.card α)
  obtain ⟨n, hnd⟩ : ∃ n : ℝ, n = Fintype.card α := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ v : α, (G.degree v : ℝ) := ⟨_, rfl⟩
  have hdeg : deg_avg = D / n := by rw [hD, hnd]
  rw [hdeg, ← hnd]
  rw [← hnd] at hn
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = ⌊D / n⌋ := ⟨_, rfl⟩
  rw [← hK]
  have hK1 : (K : ℝ) * n ≤ D := by
    have := Int.floor_le (D / n); rw [← hK, le_div_iff₀ hn] at this; exact this
  have hK2 : D < ((K : ℝ) + 1) * n := by
    have := Int.lt_floor_add_one (D / n); rw [← hK, div_lt_iff₀ hn] at this; exact this
  have hDnat : D = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
    rw [hD, ← G.sum_degrees_eq_twice_card_edges]; push_cast; rfl
  by_cases hk0 : K ≤ 0
  · have : (K : ℝ) ≤ 0 := by exact_mod_cast hk0
    exact le_trans (div_nonpos_of_nonneg_of_nonpos hn.le this) hb0
  by_cases hk1 : K = 1
  · -- the graph is a tree, hence bipartite
    subst hk1
    have hE : G.edgeFinset.card < Fintype.card α := by
      have h' : ((2 * G.edgeFinset.card : ℕ) : ℝ) < ((2 * Fintype.card α : ℕ) : ℝ) := by
        rw [← hDnat]; push_cast; rw [← hnd]; push_cast at hK2; linarith
      have := Nat.cast_lt.1 h'
      omega
    have hconn := h.card_vert_le_card_edgeSet_add_one
    have e1 : Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, edgeFinset_card]
    have e2 : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
    have hT : G.IsTree := isTree_iff_connected_and_card.2 ⟨h, by omega⟩
    obtain ⟨c⟩ := hT.colorable_two
    have := b_ge G Finset.univ c (fun x _ y _ hxy => c.valid hxy)
    rw [Finset.card_univ, ← hnd] at this
    simpa using this
  have hk2 : (2 : ℝ) ≤ K := by
    have : (2 : ℤ) ≤ K := by omega
    exact_mod_cast this
  -- phase 1
  obtain ⟨I, -, hIind, hIdom, hIsum⟩ := caroWei G _ Finset.univ rfl
  have hW1 : ∑ v, (((Finset.univ.filter (G.Adj v)).card : ℝ) + 1) ≤ D + n := by
    rw [Finset.sum_add_distrib, hD, hnd]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : ∀ v ∈ (Finset.univ : Finset α),
        (((Finset.univ.filter (G.Adj v)).card : ℝ)) ≤ (G.degree v : ℝ) := by
      intro v _
      rw [← card_neighborFinset_eq_degree]
      exact_mod_cast Finset.card_le_card (fun w hw => by
        rw [mem_neighborFinset]; exact (Finset.mem_filter.1 hw).2)
    linarith [Finset.sum_le_sum this]
  have hcs1 := cs Finset.univ (fun v => (((Finset.univ.filter (G.Adj v)).card : ℝ) + 1))
    (fun v _ => by positivity)
  rw [Finset.card_univ, ← hnd] at hcs1
  have hsum1nn : (0 : ℝ) ≤ ∑ v, (1 : ℝ) / (((Finset.univ.filter (G.Adj v)).card : ℝ) + 1) :=
    Finset.sum_nonneg (fun v _ => by positivity)
  have hW1nn : (0 : ℝ) ≤ ∑ v, (((Finset.univ.filter (G.Adj v)).card : ℝ) + 1) :=
    Finset.sum_nonneg (fun v _ => by positivity)
  have hA : n ^ 2 ≤ (I.card : ℝ) * (D + n) := by
    calc n ^ 2 ≤ _ := hcs1
      _ ≤ (I.card : ℝ) * ∑ v, (((Finset.univ.filter (G.Adj v)).card : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hIsum hW1nn
      _ ≤ _ := mul_le_mul_of_nonneg_left hW1 (by positivity)
  -- phase 2
  obtain ⟨S', hS'⟩ : ∃ S', S' = Finset.univ \ I := ⟨_, rfl⟩
  obtain ⟨J, hJS, hJind, -, hJsum⟩ := caroWei G _ S' rfl
  have memS' : ∀ v, v ∈ S' ↔ v ∉ I := by intro v; rw [hS']; simp
  have hcardx : (S'.card : ℝ) + I.card = n := by
    rw [hnd, hS']; exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
  have hdeg2 : ∀ v ∈ S', (((S'.filter (G.Adj v)).card : ℝ) + 1) ≤ (G.degree v : ℝ) := by
    intro v hv
    obtain ⟨w, hwI, hvw⟩ := hIdom v (Finset.mem_univ v) ((memS' v).1 hv)
    have hw : w ∉ S'.filter (G.Adj v) := fun hh =>
      (memS' w).1 (Finset.mem_filter.1 hh).1 hwI
    have hsub : insert w (S'.filter (G.Adj v)) ⊆ G.neighborFinset v := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rw [mem_neighborFinset]
      rcases hz with rfl | hz
      · exact hvw
      · exact (Finset.mem_filter.1 hz).2
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hw, card_neighborFinset_eq_degree] at this
    exact_mod_cast this
  have hdegI : (S'.card : ℝ) ≤ ∑ u ∈ I, (G.degree u : ℝ) := by
    have hsub : S' ⊆ I.biUnion (fun u => G.neighborFinset u) := by
      intro v hv
      obtain ⟨w, hwI, hvw⟩ := hIdom v (Finset.mem_univ v) ((memS' v).1 hv)
      exact Finset.mem_biUnion.2 ⟨w, hwI, (mem_neighborFinset _ _ _).2 hvw.symm⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    simp only [card_neighborFinset_eq_degree] at h1
    exact_mod_cast h1
  have hsplit : D = ∑ v ∈ S', (G.degree v : ℝ) + ∑ u ∈ I, (G.degree u : ℝ) := by
    rw [hD, hS']; exact (Finset.sum_sdiff (Finset.subset_univ I)).symm
  have hW2 : ∑ v ∈ S', (((S'.filter (G.Adj v)).card : ℝ) + 1) ≤ D - S'.card := by
    have := Finset.sum_le_sum hdeg2
    linarith
  have hcs2 := cs S' (fun v => (((S'.filter (G.Adj v)).card : ℝ) + 1))
    (fun v _ => by positivity)
  have hW2nn : (0 : ℝ) ≤ ∑ v ∈ S', (((S'.filter (G.Adj v)).card : ℝ) + 1) :=
    Finset.sum_nonneg (fun v _ => by positivity)
  have hB : (S'.card : ℝ) ^ 2 ≤ (J.card : ℝ) * (D - S'.card) := by
    calc (S'.card : ℝ) ^ 2 ≤ _ := hcs2
      _ ≤ (J.card : ℝ) * ∑ v ∈ S', (((S'.filter (G.Adj v)).card : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hJsum hW2nn
      _ ≤ _ := mul_le_mul_of_nonneg_left hW2 (by positivity)
  -- the bipartite set I ∪ J
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro u hu hJ
    exact (memS' u).1 (hJS hJ) hu
  have hbIJ : ((I ∪ J).card : ℝ) ≤ b G := by
    apply b_ge G (I ∪ J) (fun u => if u ∈ I then 0 else 1)
    intro x hx y hy hxy
    rw [Finset.mem_union] at hx hy
    by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I <;> simp only [hxI, hyI, if_true, if_false]
    · exact fun _ => hIind x hxI y hyI hxy
    · decide
    · decide
    · have hxJ : x ∈ J := hx.resolve_left hxI
      have hyJ : y ∈ J := hy.resolve_left hyI
      exact fun _ => hJind x hxJ y hyJ hxy
  rw [Finset.card_union_of_disjoint hdisj] at hbIJ
  push_cast at hbIJ
  rw [div_le_iff₀ (by linarith)]
  have := arith n D K I.card S'.card J.card hn (by linarith) (by positivity) (by positivity)
    hA hB (by positivity) hk2 hK1 hK2
  nlinarith [mul_le_mul_of_nonneg_left hbIJ (by linarith : (0 : ℝ) ≤ K)]

end WrittenOnTheWallII.GraphConjecture20

#print axioms WrittenOnTheWallII.GraphConjecture20.conjecture20
