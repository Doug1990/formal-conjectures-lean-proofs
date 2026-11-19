import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open SimpleGraph

namespace Erdos1008

namespace FK

lemma of_cycle {V : Type} (H : SimpleGraph V) (a b c d : V) (hab : H.Adj a b)
    (hbc : H.Adj b c) (hcd : H.Adj c d) (hda : H.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    cycleGraph 4 ⊑ H := by
  refine ⟨⟨⟨![a, b, c, d], ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd h (by decide)
      | exact hab | exact hab.symm | exact hbc | exact hbc.symm
      | exact hcd | exact hcd.symm | exact hda | exact hda.symm
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd h hab.ne | exact absurd h hab.ne.symm
      | exact absurd h hbc.ne | exact absurd h hbc.ne.symm
      | exact absurd h hcd.ne | exact absurd h hcd.ne.symm
      | exact absurd h hda.ne | exact absurd h hda.ne.symm
      | exact absurd h hac | exact absurd h hac.symm
      | exact absurd h hbd | exact absurd h hbd.symm

lemma arith (d : ℕ) : 2 * d ≤ 2 + (d * d - d) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    all_goals decide
  · have h2 : 3 * d ≤ d * d := Nat.mul_le_mul_right d h
    generalize d * d = p at *
    omega

lemma choose2 (n : ℕ) : 2 * n.choose 2 = n * n - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.mul_add, ih]
    have h1 := Nat.le_mul_self k
    have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [h2]
    generalize k * k = p at *
    omega

lemma part1 (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin (n ^ 2))).edgeSet.ncard = n ^ 3 := by
  rw [Set.ncard_def, encard_edgeSet_completeBipartiteGraph, ENat.card_eq_coe_fintype_card,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin, Fintype.card_fin, ← Nat.cast_mul,
    ENat.toNat_natCast]
  ring

lemma part2 (n : ℕ) : ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n ^ 2)),
    n ^ 2 + n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H := by
  intro H hH hlt
  classical
  by_contra hfree
  have hleft : ∀ r x, H.Adj (Sum.inr r) x → ∃ l, x = Sum.inl l := by
    intro r x hx
    have := hH hx
    cases x with
    | inl l => exact ⟨l, rfl⟩
    | inr r' => simp at this
  have hE : H.edgeSet.ncard ≤ ∑ r, (H.neighborFinset (Sum.inr r)).card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    calc H.edgeFinset.card
        ≤ (Finset.univ.biUnion (fun r => H.incidenceFinset (Sum.inr r))).card := by
          apply Finset.card_le_card
          intro e he
          revert he
          refine Sym2.ind (fun x y => ?_) e
          intro he
          rw [mem_edgeFinset] at he
          have hxy : H.Adj x y := he
          have hA := hH hxy
          rw [Finset.mem_biUnion]
          cases x with
          | inl l =>
            cases y with
            | inl l' => simp at hA
            | inr r =>
              exact ⟨r, Finset.mem_univ _, (mem_incidenceFinset _ _ _).2
                (Set.mem_sep he (Sym2.mem_mk_right _ _))⟩
          | inr r =>
            cases y with
            | inl l' =>
              exact ⟨r, Finset.mem_univ _, (mem_incidenceFinset _ _ _).2
                (Set.mem_sep he (Sym2.mem_mk_left _ _))⟩
            | inr r' => simp at hA
      _ ≤ ∑ r, (H.incidenceFinset (Sum.inr r)).card := Finset.card_biUnion_le
      _ = ∑ r, (H.neighborFinset (Sum.inr r)).card := Finset.sum_congr rfl (fun r _ => by
          rw [card_incidenceFinset_eq_degree, card_neighborFinset_eq_degree])
  have hdisj : ((Finset.univ : Finset (Fin (n ^ 2))) : Set (Fin (n ^ 2))).PairwiseDisjoint
      (fun r => (H.neighborFinset (Sum.inr r)).offDiag) := by
    intro r _ r' _ hrr'
    change Disjoint (H.neighborFinset (Sum.inr r)).offDiag
      (H.neighborFinset (Sum.inr r')).offDiag
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_offDiag, mem_neighborFinset, mem_neighborFinset] at hp hp'
    exact hfree (of_cycle H p.1 (Sum.inr r) p.2 (Sum.inr r') hp.1.symm hp.2.1 hp'.2.1.symm
      hp'.1 hp.2.2 (fun h => hrr' (Sum.inr_injective h)))
  have hsub : ∀ r, (H.neighborFinset (Sum.inr r)).offDiag ⊆
      (Finset.univ.map (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin (n ^ 2))).offDiag := by
    intro r p hp
    rw [Finset.mem_offDiag] at hp ⊢
    have hm : ∀ x, x ∈ H.neighborFinset (Sum.inr r) →
        x ∈ Finset.univ.map (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin (n ^ 2)) := by
      intro x hx
      rw [mem_neighborFinset] at hx
      obtain ⟨l, rfl⟩ := hleft r x hx
      exact Finset.mem_map_of_mem _ (Finset.mem_univ l)
    exact ⟨hm _ hp.1, hm _ hp.2.1, hp.2.2⟩
  have hsum : ∑ r, ((H.neighborFinset (Sum.inr r)).card * (H.neighborFinset (Sum.inr r)).card
      - (H.neighborFinset (Sum.inr r)).card) ≤ n * n - n := by
    have := Finset.card_le_card (Finset.biUnion_subset.2 (fun r (_ : r ∈ Finset.univ) => hsub r))
    rw [Finset.card_biUnion hdisj] at this
    simpa only [Finset.offDiag_card, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      using this
  have h2 : 2 * ∑ r, (H.neighborFinset (Sum.inr r)).card ≤ 2 * n ^ 2 + (n * n - n) := by
    rw [Finset.mul_sum]
    calc ∑ r, 2 * (H.neighborFinset (Sum.inr r)).card
        ≤ ∑ r, (2 + ((H.neighborFinset (Sum.inr r)).card * (H.neighborFinset (Sum.inr r)).card
            - (H.neighborFinset (Sum.inr r)).card)) :=
          Finset.sum_le_sum (fun r _ => arith _)
      _ = 2 * n ^ 2 + ∑ r, ((H.neighborFinset (Sum.inr r)).card *
            (H.neighborFinset (Sum.inr r)).card - (H.neighborFinset (Sum.inr r)).card) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, mul_comm]
      _ ≤ 2 * n ^ 2 + (n * n - n) := Nat.add_le_add_left hsum _
  have hc := choose2 n
  linarith

end FK

theorem erdos_1008.variants.folkman (n : ℕ) :
    ((completeBipartiteGraph (Fin n) (Fin (n ^ 2))).edgeSet.ncard = n ^ 3) ∧
      ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n ^ 2)),
        n ^ 2 + n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H :=
  ⟨FK.part1 n, FK.part2 n⟩

end Erdos1008

#print axioms Erdos1008.erdos_1008.variants.folkman
