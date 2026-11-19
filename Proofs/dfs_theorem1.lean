import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

-- Proof of SimpleGraph.theorem1 (Paper/DegreeSequencesTriangleFree.lean:254).
-- Definitions from FormalConjecturesForMathlib are restated verbatim (targeted imports only).

open Finset

namespace DfsSeq
variable (D : ℕ → ℕ) (N : ℕ)

lemma chain (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) :
    ∀ m i, i + 2 * m < N → D i + m ≤ D (i + 2 * m) := by
  intro m
  induction m with
  | zero => intro i _; simp
  | succ m ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := hstep (i + 2 * m) (by omega)
    have e : i + 2 * (m + 1) = i + 2 * m + 2 := by ring
    rw [e]; omega

lemma chain_strict (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) (m i j : ℕ)
    (hi : i + 2 * m < N) (hj : j < m) (hbad : D (i + 2 * j) + 2 ≤ D (i + 2 * j + 2)) :
    D i + m + 1 ≤ D (i + 2 * m) := by
  have h1 := chain D N hstep j i (by omega)
  have h2 := chain D N hstep (m - j - 1) (i + 2 * j + 2) (by omega)
  have e : i + 2 * j + 2 + 2 * (m - j - 1) = i + 2 * m := by omega
  rw [e] at h2
  omega

lemma pair (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) (b m : ℕ) (h : b + 2 * m ≤ N) :
    ∑ i ∈ Finset.range b, D i + b * m ≤ ∑ i ∈ Finset.range b, D (2 * m + i) := by
  have hc : ∑ _i ∈ Finset.range b, m = b * m := by simp
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have := chain D N hstep m i (by omega)
  rw [show 2 * m + i = i + 2 * m by ring]
  exact this

lemma pair_strict (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) (b m : ℕ) (h : b + 2 * m ≤ N)
    (k i j : ℕ) (hk : k = i + 2 * j) (hib : i < b) (hjm : j < m)
    (hbad : D k + 2 ≤ D (k + 2)) :
    ∑ i ∈ Finset.range b, D i + b * m < ∑ i ∈ Finset.range b, D (2 * m + i) := by
  subst hk
  have hc : ∑ _i ∈ Finset.range b, m = b * m := by simp
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i' hi'
    rw [Finset.mem_range] at hi'
    have := chain D N hstep m i' (by omega)
    rw [show 2 * m + i' = i' + 2 * m by ring]
    exact this
  · refine ⟨i, Finset.mem_range.2 hib, ?_⟩
    have := chain_strict D N hstep m i j (by omega) hjm hbad
    rw [show 2 * m + i = i + 2 * m by ring]
    omega

open Classical in
lemma seq_main (hN : 2 ≤ N) (hmono : ∀ i j, i ≤ j → j < N → D i ≤ D j)
    (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) (hpos : 1 ≤ D 0) :
    ∑ i ∈ Finset.range (N / 2), D i + 2 * ((N - N / 2) * (N - N / 2) / 4)
      + (if N % 4 = 1 ∨ ∃ k, k + 2 < N ∧ D k + 2 ≤ D (k + 2) then 1 else 0)
      ≤ ∑ i ∈ Finset.Ico (N / 2) N, D i := by
  rw [Finset.sum_Ico_eq_sum_range]
  obtain ⟨n, hn⟩ : ∃ n, N = 4 * n ∨ N = 4 * n + 1 ∨ N = 4 * n + 2 ∨ N = 4 * n + 3 :=
    ⟨N / 4, by omega⟩
  rcases hn with hn | hn | hn | hn
  · -- N = 4n
    have e1 : N / 2 = 2 * n := by omega
    have e2 : N - 2 * n = 2 * n := by omega
    have e3 : 2 * n * (2 * n) / 4 = n * n := by
      rw [show 2 * n * (2 * n) = 4 * (n * n) by ring]; omega
    rw [e1, e2, e3]
    have hp := pair D N hstep (2 * n) n (by omega)
    have r1 : 2 * n * n = 2 * (n * n) := by ring
    split_ifs with hb
    · rcases hb with hb | ⟨k, hk, hbad⟩
      · omega
      · have hs : ∑ i ∈ Finset.range (2 * n), D i + 2 * n * n <
            ∑ i ∈ Finset.range (2 * n), D (2 * n + i) := by
          by_cases hk2 : k < 2 * n
          · exact pair_strict D N hstep (2 * n) n (by omega) k k 0 (by ring) hk2
              (by omega) hbad
          · exact pair_strict D N hstep (2 * n) n (by omega) k (k - 2 * (n - 1)) (n - 1)
              (by omega) (by omega) (by omega) hbad
        omega
    · omega
  · -- N = 4n+1
    have e1 : N / 2 = 2 * n := by omega
    have e2 : N - 2 * n = 2 * n + 1 := by omega
    have e3 : (2 * n + 1) * (2 * n + 1) / 4 = n * n + n := by
      rw [show (2 * n + 1) * (2 * n + 1) = 4 * (n * n + n) + 1 by ring]; omega
    rw [e1, e2, e3, Finset.sum_range_succ]
    have hp := pair D N hstep (2 * n) n (by omega)
    have hl := chain D N hstep (2 * n) 0 (by omega)
    rw [show 0 + 2 * (2 * n) = 2 * n + 2 * n by ring] at hl
    have r1 : 2 * n * n = 2 * (n * n) := by ring
    rw [if_pos (Or.inl (by omega))]
    omega
  · -- N = 4n+2
    have e1 : N / 2 = 2 * n + 1 := by omega
    have e2 : N - (2 * n + 1) = 2 * n + 1 := by omega
    have e3 : (2 * n + 1) * (2 * n + 1) / 4 = n * n + n := by
      rw [show (2 * n + 1) * (2 * n + 1) = 4 * (n * n + n) + 1 by ring]; omega
    rw [e1, e2, e3, Finset.sum_range_succ' (fun k => D (2 * n + 1 + k)),
      Finset.sum_range_succ D (2 * n)]
    have hsh : ∑ i ∈ Finset.range (2 * n), D (2 * n + 1 + (i + 1)) =
        ∑ i ∈ Finset.range (2 * n), D (2 * (n + 1) + i) :=
      Finset.sum_congr rfl (fun i _ => by congr 1; ring)
    rw [hsh]
    have hp := pair D N hstep (2 * n) (n + 1) (by omega)
    have hm := hmono (2 * n) (2 * n + 1 + 0) (by omega) (by omega)
    have r1 : 2 * n * (n + 1) = 2 * (n * n + n) := by ring
    split_ifs with hb
    · rcases hb with hb | ⟨k, hk, hbad⟩
      · omega
      · have hs : ∑ i ∈ Finset.range (2 * n), D i + 2 * n * (n + 1) <
            ∑ i ∈ Finset.range (2 * n), D (2 * (n + 1) + i) := by
          by_cases hk2 : k < 2 * n
          · exact pair_strict D N hstep (2 * n) (n + 1) (by omega) k k 0 (by ring) hk2
              (by omega) hbad
          · exact pair_strict D N hstep (2 * n) (n + 1) (by omega) k (k - 2 * n) n
              (by omega) (by omega) (by omega) hbad
        omega
    · omega
  · -- N = 4n+3
    have e1 : N / 2 = 2 * n + 1 := by omega
    have e2 : N - (2 * n + 1) = 2 * n + 2 := by omega
    have e3 : (2 * n + 2) * (2 * n + 2) / 4 = n * n + 2 * n + 1 := by
      rw [show (2 * n + 2) * (2 * n + 2) = 4 * (n * n + 2 * n + 1) by ring]; omega
    rw [e1, e2, e3, Finset.sum_range_succ' (fun k => D (2 * n + 1 + k))]
    have hsh : ∑ i ∈ Finset.range (2 * n + 1), D (2 * n + 1 + (i + 1)) =
        ∑ i ∈ Finset.range (2 * n + 1), D (2 * (n + 1) + i) :=
      Finset.sum_congr rfl (fun i _ => by congr 1; ring)
    rw [hsh]
    have hp := pair D N hstep (2 * n + 1) (n + 1) (by omega)
    have hl := chain D N hstep n 1 (by omega)
    have hm := hmono 0 1 (by omega) (by omega)
    rw [show 1 + 2 * n = 2 * n + 1 + 0 by ring] at hl
    have r1 : (2 * n + 1) * (n + 1) = 2 * (n * n) + 3 * n + 1 := by ring
    split_ifs with hb
    · rcases hb with hb | ⟨k, hk, hbad⟩
      · omega
      · have hs : ∑ i ∈ Finset.range (2 * n + 1), D i + (2 * n + 1) * (n + 1) <
            ∑ i ∈ Finset.range (2 * n + 1), D (2 * (n + 1) + i) := by
          by_cases hk2 : k < 2 * n + 1
          · exact pair_strict D N hstep (2 * n + 1) (n + 1) (by omega) k k 0 (by ring) hk2
              (by omega) hbad
          · exact pair_strict D N hstep (2 * n + 1) (n + 1) (by omega) k (k - 2 * n) n
              (by omega) (by omega) (by omega) hbad
        omega
    · omega

lemma low_bound (hN : 2 ≤ N) (hmono : ∀ i j, i ≤ j → j < N → D i ≤ D j)
    (hstep : ∀ k, k + 2 < N → D k + 1 ≤ D (k + 2)) :
    D 0 + (N / 2 - 1) / 2 ≤ D (N / 2 - 1) := by
  rcases Nat.even_or_odd (N / 2 - 1) with ⟨c, hc⟩ | ⟨c, hc⟩
  · have := chain D N hstep c 0 (by omega)
    rw [show 0 + 2 * c = N / 2 - 1 by omega] at this
    omega
  · have := chain D N hstep c 1 (by omega)
    rw [show 1 + 2 * c = N / 2 - 1 by omega] at this
    have hm := hmono 0 1 (by omega) (by omega)
    omega

end DfsSeq

namespace DfsGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
lemma mantel {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (cf : H.CliqueFree 3) :
    #H.edgeFinset ≤ #(SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset := by
  obtain ⟨J, _, j⟩ := SimpleGraph.exists_isTuranMaximal (V := V) (r := 2) Nat.two_pos
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [← g.card_edgeFinset_eq]
  exact j.2 cf
lemma iso_of_max {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (cf : H.CliqueFree 3)
    (h : #(SimpleGraph.turanGraph (Fintype.card V) 2).edgeFinset ≤ #H.edgeFinset) :
    Nonempty (H ≃g SimpleGraph.turanGraph (Fintype.card V) 2) := by
  have hT : H.IsTuranMaximal 2 := by
    unfold SimpleGraph.IsTuranMaximal SimpleGraph.IsExtremal
    refine ⟨cf, ?_⟩
    intro H' _ cf'
    exact (mantel H' cf').trans h
  exact hT.nonempty_iso_turanGraph
lemma turan_adj {n : ℕ} (a b : Fin n) :
    (SimpleGraph.turanGraph n 2).Adj a b ↔ a.val % 2 ≠ b.val % 2 := by
  rw [SimpleGraph.turanGraph_adj]
lemma tur_bound (t s : ℕ) (h : t = s) :
    4 * #(SimpleGraph.turanGraph t 2).edgeFinset ≤ s * s := by
  subst h
  have h2 : 2 * 2 * #(SimpleGraph.turanGraph t 2).edgeFinset ≤ (2 - 1) * t ^ 2 :=
    SimpleGraph.mul_card_edgeFinset_turanGraph_le
  rw [show (2:ℕ) - 1 = 1 from rfl, one_mul, sq] at h2
  omega
lemma deg_split (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α) :
    ∑ v ∈ T, G.degree v = ∑ v ∈ T, #{w ∈ T | G.Adj v w} + ∑ v ∈ T, #{w ∈ Tᶜ | G.Adj v w} := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl]
    tauto
  · refine Finset.disjoint_left.2 (fun a h1 h2 => ?_)
    simp only [mem_filter, mem_compl] at h1 h2
    exact h2.1 h1.1
lemma cross (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α) :
    ∑ v ∈ T, #{w ∈ Tᶜ | G.Adj v w} = ∑ w ∈ Tᶜ, #{v ∈ T | G.Adj v w} :=
  Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s := T) (t := Tᶜ)
open Classical in
lemma cross_le (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α) :
    ∑ w ∈ Tᶜ, #{v ∈ T | G.Adj v w}
      + (if ∃ w1 ∈ Tᶜ, ∃ w2 ∈ Tᶜ, G.Adj w1 w2 then 1 else 0)
      ≤ ∑ w ∈ Tᶜ, G.degree w := by
  have hsub : ∀ w, ({v ∈ T | G.Adj v w} : Finset α) ⊆ G.neighborFinset w := by
    intro w v hv
    simp only [mem_filter] at hv
    rw [SimpleGraph.mem_neighborFinset]
    exact hv.2.symm
  split_ifs with h
  · obtain ⟨w1, hw1, w2, hw2, hadj⟩ := h
    have : ∑ w ∈ Tᶜ, #{v ∈ T | G.Adj v w} < ∑ w ∈ Tᶜ, G.degree w := by
      apply Finset.sum_lt_sum
      · intro w _
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card (hsub w)
      · refine ⟨w1, hw1, ?_⟩
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (hsub w1)]
        refine ⟨w2, (SimpleGraph.mem_neighborFinset _ _ _).2 hadj, ?_⟩
        simp only [mem_filter, not_and]
        intro h2
        exact absurd h2 (mem_compl.1 hw2)
    omega
  · simp only [add_zero]
    apply Finset.sum_le_sum
    intro w _
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (hsub w)
lemma inner (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α)
    [DecidableRel (G.comap (Function.Embedding.subtype (· ∈ T))).Adj] :
    ∑ v ∈ T, #{w ∈ T | G.Adj v w} =
      2 * #(G.comap (Function.Embedding.subtype (· ∈ T))).edgeFinset := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, ← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  conv_rhs => rw [← Finset.card_map (Function.Embedding.subtype (· ∈ T))]
  congr 1
  ext w
  rw [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hw, ha⟩
    exact ⟨⟨w, hw⟩, (SimpleGraph.mem_neighborFinset _ _ _).2 ha, rfl⟩
  · rintro ⟨⟨x, hx⟩, hmem, rfl⟩
    exact ⟨hx, (SimpleGraph.mem_neighborFinset
      (G.comap (Function.Embedding.subtype (· ∈ T))) v ⟨x, hx⟩).1 hmem⟩
omit [DecidableEq α] in
lemma sum_pos {N : ℕ} (e : Fin N ≃ α) (P : ℕ → Prop) [DecidablePred P] (φ : ℕ → ℕ) :
    ∑ v ∈ univ.filter (fun v => P (e.symm v).val), φ (e.symm v).val
      = ∑ i ∈ (range N).filter P, φ i := by
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if P i then φ i else 0)]
  exact Equiv.sum_comp e.symm (fun i : Fin N => if P i.val then φ i.val else 0)
lemma mult_le (L : List ℕ) : ((L.map fun d => L.count d).max?).getD 0 ≤ L.length := by
  cases h : (L.map fun d => L.count d).max? with
  | none => simp
  | some a =>
    have := List.max?_mem h
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 this
    simpa using List.count_le_length
end DfsGraph

namespace DegreeSequencesTriangleFree

def IsCompactSequenceOn (d : ℕ → ℕ) (S : Set ℕ) : Prop :=
  ∀ k ∈ S, d (k + 2) = d k + 1

end DegreeSequencesTriangleFree

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

def HasCompactdegreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  DegreeSequencesTriangleFree.IsCompactSequenceOn (fun k => (degreeSequence G).getD k 0) {k | k + 2 < Fintype.card α}

noncomputable def ord (G : SimpleGraph α) [DecidableRel G.Adj] : Fin (Fintype.card α) ≃ α :=
  (Tuple.sort (fun i => G.degree ((Fintype.equivFin α).symm i))).trans
    (Fintype.equivFin α).symm

omit [DecidableEq α] in
lemma ord_mono (G : SimpleGraph α) [DecidableRel G.Adj] :
    Monotone (fun i => G.degree (ord G i)) := by
  intro a b h
  exact Tuple.monotone_sort (fun i => G.degree ((Fintype.equivFin α).symm i)) h

lemma seq_eq (G : SimpleGraph α) [DecidableRel G.Adj] :
    degreeSequence G = List.ofFn (fun i => G.degree (ord G i)) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact ord_mono G hij.le
  · rw [← Multiset.coe_eq_coe, degreeSequence, Multiset.sort_eq, ← Fin.univ_val_map]
    have h1 : (Finset.univ.val.map (ord G)) = (Finset.univ : Finset α).val := by
      have := congrArg Finset.val (Finset.map_univ_equiv (ord G))
      simpa using this
    rw [show (fun i => G.degree (ord G i)) = (fun v => G.degree v) ∘ (ord G) from rfl,
      ← Multiset.map_map, h1]

lemma D_eq (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) (hk : k < Fintype.card α) :
    (degreeSequence G).getD k 0 = G.degree (ord G ⟨k, hk⟩) := by
  rw [seq_eq G]
  simp [List.getD_eq_getElem?_getD, hk]

lemma no_three (G : SimpleGraph α) [DecidableRel G.Adj] (h₂ : degreeSequenceMultiplicity G ≤ 2)
    (k : ℕ) (hk : k + 2 < Fintype.card α) :
    G.degree (ord G ⟨k, by omega⟩) ≠ G.degree (ord G ⟨k + 2, hk⟩) := by
  intro heq
  have hm1 : G.degree (ord G ⟨k, by omega⟩) ≤ G.degree (ord G ⟨k + 1, by omega⟩) :=
    ord_mono G (Fin.mk_le_mk.2 (by omega))
  have hm2 : G.degree (ord G ⟨k + 1, by omega⟩) ≤ G.degree (ord G ⟨k + 2, hk⟩) :=
    ord_mono G (Fin.mk_le_mk.2 (by omega))
  have h3 : 2 < #(univ.filter fun i => G.degree (ord G ⟨k, by omega⟩) = G.degree (ord G i)) := by
    rw [Finset.two_lt_card]
    refine ⟨⟨k, by omega⟩, by simp, ⟨k + 1, by omega⟩, by simp; omega, ⟨k + 2, hk⟩,
      by simp; omega, ?_, ?_, ?_⟩ <;> simp [Fin.ext_iff]
  have hc : (degreeSequence G).count (G.degree (ord G ⟨k, by omega⟩)) =
      #(univ.filter fun i => G.degree (ord G ⟨k, by omega⟩) = G.degree (ord G i)) := by
    rw [seq_eq G, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map]
    rfl
  have hmem : (degreeSequence G).count (G.degree (ord G ⟨k, by omega⟩)) ∈
      (degreeSequence G).map (fun d => (degreeSequence G).count d) := by
    apply List.mem_map_of_mem
    rw [← List.count_pos_iff]
    omega
  have := List.le_max?_getD_of_mem (k := 0) hmem
  have hmul : degreeSequenceMultiplicity G =
      ((degreeSequence G).map fun d => (degreeSequence G).count d).max?.getD 0 := rfl
  omega

theorem theorem1 (G : SimpleGraph α) (h_conn: G.Connected) [DecidableRel G.Adj]
    (h₁ : G.CliqueFree 3) (h₂ : degreeSequenceMultiplicity G = 2) :
    G.IsBipartite ∧ G.minDegree = 1 ∧ HasCompactdegreeSequence G := by
  have hmul : degreeSequenceMultiplicity G =
      ((degreeSequence G).map fun d => (degreeSequence G).count d).max?.getD 0 := rfl
  have hlen : (degreeSequence G).length = Fintype.card α := by
    rw [seq_eq G, List.length_ofFn]
  have hN2 : 2 ≤ Fintype.card α := by
    have := DfsGraph.mult_le (degreeSequence G)
    omega
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hdeg : ∀ v, 0 < G.degree v := fun v => h_conn.preconnected.degree_pos_of_nontrivial v
  let D : ℕ → ℕ := fun k => (degreeSequence G).getD k 0
  have hD : ∀ k (hk : k < Fintype.card α), D k = G.degree (ord G ⟨k, hk⟩) :=
    fun k hk => D_eq G k hk
  have hmono : ∀ i j, i ≤ j → j < Fintype.card α → D i ≤ D j := by
    intro i j hij hj
    rw [hD i (by omega), hD j hj]
    exact ord_mono G (Fin.mk_le_mk.2 hij)
  have hstep : ∀ k, k + 2 < Fintype.card α → D k + 1 ≤ D (k + 2) := by
    intro k hk
    have h3 := no_three G (by omega) k hk
    have hm := hmono k (k + 2) (by omega) hk
    rw [hD k (by omega), hD (k + 2) hk] at hm ⊢
    omega
  have hpos : 1 ≤ D 0 := by rw [hD 0 (by omega)]; exact hdeg _
  have hseq := DfsSeq.seq_main D (Fintype.card α) hN2 hmono hstep hpos
  have hlow := DfsSeq.low_bound D (Fintype.card α) hN2 hmono hstep
  obtain ⟨T, hT⟩ : ∃ T : Finset α,
      T = univ.filter (fun v => Fintype.card α / 2 ≤ ((ord G).symm v).val) := ⟨_, rfl⟩
  have hTc : Tᶜ = univ.filter (fun v => ((ord G).symm v).val < Fintype.card α / 2) := by
    rw [hT]; ext v; simp
  have hdv : ∀ v, D ((ord G).symm v).val = G.degree v := by
    intro v; rw [hD _ ((ord G).symm v).isLt]
    exact congrArg (fun x => G.degree x) ((ord G).apply_symm_apply v)
  have hST : ∑ v ∈ T, G.degree v = ∑ i ∈ Ico (Fintype.card α / 2) (Fintype.card α), D i := by
    have h := DfsGraph.sum_pos (ord G) (fun i => Fintype.card α / 2 ≤ i) D
    rw [show (range (Fintype.card α)).filter (fun i => Fintype.card α / 2 ≤ i) =
        Ico (Fintype.card α / 2) (Fintype.card α) by
      ext i; simp only [mem_filter, mem_range, mem_Ico]; constructor <;> intro h <;> omega] at h
    rw [hT, ← h]
    exact Finset.sum_congr rfl (fun v _ => (hdv v).symm)
  have hSB : ∑ v ∈ Tᶜ, G.degree v = ∑ i ∈ range (Fintype.card α / 2), D i := by
    have h := DfsGraph.sum_pos (ord G) (fun i => i < Fintype.card α / 2) D
    rw [show (range (Fintype.card α)).filter (fun i => i < Fintype.card α / 2) =
        range (Fintype.card α / 2) by
      ext i; simp only [mem_filter, mem_range]; constructor <;> intro h <;> omega] at h
    rw [hTc, ← h]
    exact Finset.sum_congr rfl (fun v _ => (hdv v).symm)
  have hcardT : #T = Fintype.card α - Fintype.card α / 2 := by
    have h := DfsGraph.sum_pos (ord G) (fun i => Fintype.card α / 2 ≤ i) (fun _ => 1)
    rw [show (range (Fintype.card α)).filter (fun i => Fintype.card α / 2 ≤ i) =
        Ico (Fintype.card α / 2) (Fintype.card α) by
      ext i; simp only [mem_filter, mem_range, mem_Ico]; constructor <;> intro h <;> omega] at h
    rw [hT]
    simpa using h
  letI instH : DecidableRel (G.comap (Function.Embedding.subtype (· ∈ T))).Adj :=
    fun a b => inferInstanceAs (Decidable (G.Adj a.1 b.1))
  have hsplit := DfsGraph.deg_split G T
  have hcross := DfsGraph.cross G T
  have hcl := DfsGraph.cross_le G T
  have hin := DfsGraph.inner G T
  have hcfH : (G.comap (Function.Embedding.subtype (· ∈ T))).CliqueFree 3 :=
    h₁.comap (SimpleGraph.Embedding.comap _ G).isContained
  have hman := DfsGraph.mantel _ hcfH
  have hcardV : Fintype.card {x // x ∈ T} = Fintype.card α - Fintype.card α / 2 := by
    rw [Fintype.card_coe, hcardT]
  have hM := DfsGraph.tur_bound _ _ hcardV
  have hI1 : ¬ (Fintype.card α % 4 = 1 ∨
      ∃ k, k + 2 < Fintype.card α ∧ D k + 2 ≤ D (k + 2)) := by
    intro hc; rw [if_pos hc] at hseq; omega
  have hI2 : ¬ ∃ w1 ∈ Tᶜ, ∃ w2 ∈ Tᶜ, G.Adj w1 w2 := by
    intro hc; rw [if_pos hc] at hcl; omega
  have hEM : #(turanGraph (Fintype.card {x // x ∈ T}) 2).edgeFinset ≤
      #(G.comap (Function.Embedding.subtype (· ∈ T))).edgeFinset := by
    rw [if_neg hI1] at hseq; rw [if_neg hI2] at hcl; omega
  obtain ⟨φ⟩ := DfsGraph.iso_of_max _ hcfH hEM
  -- compactness
  have hcomp : HasCompactdegreeSequence G := by
    unfold HasCompactdegreeSequence DegreeSequencesTriangleFree.IsCompactSequenceOn
    intro k hk
    have hk' : k + 2 < Fintype.card α := hk
    have h1 := hstep k hk'
    have h2 : ¬ D k + 2 ≤ D (k + 2) := fun h => hI1 (Or.inr ⟨k, hk', h⟩)
    show D (k + 2) = D k + 1
    omega
  -- colouring
  have hindep : ∀ u w, u ∉ T → G.Adj u w → w ∈ T := by
    intro u w hu hadj
    by_contra hw
    exact hI2 ⟨u, mem_compl.2 hu, w, mem_compl.2 hw, hadj⟩
  let par : α → ℕ := fun v => if hv : v ∈ T then (φ ⟨v, hv⟩).val % 2 else 0
  have hpar_lt : ∀ v, par v < 2 := by
    intro v; simp only [par]; split_ifs <;> omega
  have hadjT : ∀ v w (hv : v ∈ T) (hw : w ∈ T), G.Adj v w → par v ≠ par w := by
    intro v w hv hw hadj
    have h1 : (G.comap (Function.Embedding.subtype (· ∈ T))).Adj ⟨v, hv⟩ ⟨w, hw⟩ := hadj
    have h2 := φ.map_rel_iff.2 h1
    rw [DfsGraph.turan_adj] at h2
    simp only [par, dif_pos hv, dif_pos hw]
    exact h2
  have hnadjT : ∀ v w (hv : v ∈ T) (hw : w ∈ T), ¬ G.Adj v w → par v = par w := by
    intro v w hv hw hadj
    have h1 : ¬ (G.comap (Function.Embedding.subtype (· ∈ T))).Adj ⟨v, hv⟩ ⟨w, hw⟩ := hadj
    have h2 : ¬ (turanGraph (Fintype.card {x // x ∈ T}) 2).Adj (φ ⟨v, hv⟩) (φ ⟨w, hw⟩) :=
      fun h => h1 (φ.map_rel_iff.1 h)
    rw [DfsGraph.turan_adj] at h2
    simp only [par, dif_pos hv, dif_pos hw]
    omega
  have hnbr : ∀ u w1 w2 (h1 : w1 ∈ T) (h2 : w2 ∈ T), G.Adj u w1 → G.Adj u w2 →
      par w1 = par w2 := by
    intro u w1 w2 h1 h2 a1 a2
    apply hnadjT w1 w2 h1 h2
    intro a12
    exact h₁ {u, w1, w2} (is3Clique_triple_iff.2 ⟨a1, a2, a12⟩)
  let c : α → ℕ := fun v => if v ∈ T then par v else
    (if h : ∃ w, G.Adj v w then 1 - par h.choose else 0)
  have hc_lt : ∀ v, c v < 2 := by
    intro v; simp only [c]; split_ifs <;> first | exact hpar_lt v | omega
  have hcB : ∀ u w, u ∉ T → G.Adj u w → c u = 1 - par w := by
    intro u w hu hadj
    have hex : ∃ w, G.Adj u w := ⟨w, hadj⟩
    have hw : w ∈ T := hindep u w hu hadj
    have hch := hex.choose_spec
    have hchT : hex.choose ∈ T := hindep u _ hu hch
    have := hnbr u _ _ hchT hw hch hadj
    simp only [c, if_neg hu, dif_pos hex]
    rw [this]
  have hvalid : ∀ v w, G.Adj v w → c v ≠ c w := by
    intro v w hadj
    by_cases hv : v ∈ T <;> by_cases hw : w ∈ T
    · have := hadjT v w hv hw hadj
      simp only [c, if_pos hv, if_pos hw]; exact this
    · rw [hcB w v hw hadj.symm]
      have := hpar_lt v
      simp only [c, if_pos hv]; omega
    · rw [hcB v w hv hadj]
      have := hpar_lt w
      simp only [c, if_pos hw]; omega
    · exact absurd (hindep v w hv hadj) hw
  have hbip : G.IsBipartite := by
    let C : G.Coloring (Fin 2) := SimpleGraph.Coloring.mk (fun v => ⟨c v, hc_lt v⟩)
      (fun {v w} hadj h => hvalid v w hadj (congrArg Fin.val h))
    simpa using C.colorable
  -- minimum degree
  have hu_lt : Fintype.card α / 2 - 1 < Fintype.card α := by omega
  have huT : ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩ ∉ T := by
    rw [hT]; simp; omega
  have hdu : G.degree (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩) ≤
      (Fintype.card {x // x ∈ T} + 1) / 2 := by
    rw [← card_neighborFinset_eq_degree]
    by_cases hne : (G.neighborFinset (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩)).Nonempty
    · let f : α → ℕ := fun w => if hw : w ∈ T then (φ ⟨w, hw⟩).val / 2 else 0
      calc #(G.neighborFinset (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩))
          ≤ #(range ((Fintype.card {x // x ∈ T} + 1) / 2)) := by
            apply Finset.card_le_card_of_injOn f
            · intro w hw
              have hw' : G.Adj (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩) w := by simpa using hw
              have hwT := hindep _ w huT hw'
              have hlt := (φ ⟨w, hwT⟩).isLt
              simp only [Finset.mem_coe, Finset.mem_range, f, dif_pos hwT]
              omega
            · intro w1 hw1 w2 hw2 heq
              have a1 : G.Adj (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩) w1 := by simpa using hw1
              have a2 : G.Adj (ord G ⟨Fintype.card α / 2 - 1, hu_lt⟩) w2 := by simpa using hw2
              have h1T := hindep _ w1 huT a1
              have h2T := hindep _ w2 huT a2
              have hp := hnbr _ w1 w2 h1T h2T a1 a2
              simp only [f, dif_pos h1T, dif_pos h2T] at heq
              simp only [par, dif_pos h1T, dif_pos h2T] at hp
              have hval : (φ ⟨w1, h1T⟩).val = (φ ⟨w2, h2T⟩).val := by omega
              have := φ.injective (Fin.ext hval)
              exact congrArg Subtype.val this
        _ = (Fintype.card {x // x ∈ T} + 1) / 2 := card_range _
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hD0 : D 0 ≤ 1 := by
    have := hD (Fintype.card α / 2 - 1) hu_lt
    omega
  have hmin : G.minDegree = 1 := by
    apply le_antisymm
    · have := G.minDegree_le_degree (ord G ⟨0, by omega⟩)
      rw [← hD 0 (by omega)] at this
      omega
    · exact SimpleGraph.le_minDegree_of_forall_le_degree (G := G) 1 hdeg
  exact ⟨hbip, hmin, hcomp⟩

end SimpleGraph

#print axioms SimpleGraph.theorem1
