import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open SimpleGraph

namespace Erdos1008

namespace LB

lemma free_of {V : Type} (H : SimpleGraph V)
    (h : ∀ a b c d : V, H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a →
      a ≠ c → b ≠ d → False) : (cycleGraph 4).Free H := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → H.Adj (f i) (f j) :=
    fun i j hij => f.toHom.map_adj hij
  exact h (f 0) (f 1) (f 2) (f 3) (hadj 0 1 (by decide)) (hadj 1 2 (by decide))
    (hadj 2 3 (by decide)) (hadj 3 0 (by decide))
    (fun e => absurd (f.injective e) (by decide)) (fun e => absurd (f.injective e) (by decide))

lemma key (m t : ℕ) (h : m ≤ 2 * (t * t)) : (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) ≤ t := by
  rw [← Real.sqrt_eq_rpow]
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (m : ℝ) ≤ (2 * t) ^ 2 := by
    have h0 : (m : ℝ) ≤ 2 * (t * t) := by exact_mod_cast h
    have e : ((2 : ℝ) * t) ^ 2 = 4 * (t * t) := by ring
    rw [e]
    linarith [mul_self_nonneg (t : ℝ)]
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by linarith)] at h2
  linarith

lemma exists_matching {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) :
    ∃ M ⊆ E, (∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f) ∧
      ∀ e ∈ E, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f := by
  classical
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (E.powerset.filter (fun M => ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f))
    Finset.card ⟨∅, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  refine ⟨M, hM.1, hM.2, fun e he => ?_⟩
  by_contra hne
  have hne' : ∀ f ∈ M, ∀ x, x ∈ e → x ∉ f :=
    fun f hf x hxe hxf => hne ⟨f, hf, x, hxe, hxf⟩
  have heM : e ∉ M := fun h => hne' e h _ (Sym2.out_fst_mem e) (Sym2.out_fst_mem e)
  have hins : insert e M ∈ E.powerset.filter
      (fun M => ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset he hM.1, ?_⟩
    intro e1 he1 f1 hf1 x hx1 hx2
    rw [Finset.mem_insert] at he1 hf1
    rcases he1 with rfl | he1 <;> rcases hf1 with rfl | hf1
    · rfl
    · exact absurd hx2 (hne' f1 hf1 x hx1)
    · exact absurd hx1 (hne' e1 he1 x hx2)
    · exact hM.2 e1 he1 f1 hf1 x hx1 hx2
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem heM] at this
  omega

lemma two_le {V : Type} [Fintype V] [DecidableEq V] (f : Sym2 V) :
    (Finset.univ.filter (· ∈ f)).card ≤ 2 := by
  refine Sym2.ind (fun a b => ?_) f
  have hsub : Finset.univ.filter (· ∈ s(a, b)) ⊆ {a, b} := by
    intro x hx
    rw [Finset.mem_filter, Sym2.mem_iff] at hx
    rcases hx.2 with rfl | rfl <;> simp
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le a {b}).trans (by simp))

lemma count {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hcov : ∀ e ∈ G.edgeFinset, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f) :
    G.edgeFinset.card ≤ 2 * M.card * G.maxDegree := by
  set T := Finset.univ.filter (fun x => ∃ f ∈ M, x ∈ f) with hTdef
  have hT : T.card ≤ 2 * M.card := by
    have hsub : T ⊆ M.biUnion (fun f => Finset.univ.filter (· ∈ f)) := by
      intro x hx
      rw [hTdef, Finset.mem_filter] at hx
      obtain ⟨f, hf, hxf⟩ := hx.2
      exact Finset.mem_biUnion.2 ⟨f, hf, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxf⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ f ∈ M, (Finset.univ.filter (· ∈ f)).card ≤ M.card • 2 :=
          Finset.sum_le_card_nsmul _ _ _ (fun f _ => two_le f)
      _ = 2 * M.card := by rw [smul_eq_mul, mul_comm]
  have hE : G.edgeFinset ⊆ T.biUnion (fun x => G.incidenceFinset x) := by
    intro e he
    obtain ⟨f, hf, x, hxe, hxf⟩ := hcov e he
    refine Finset.mem_biUnion.2 ⟨x, ?_, ?_⟩
    · rw [hTdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, f, hf, hxf⟩
    · rw [mem_incidenceFinset]
      exact Set.mem_sep (G.mem_edgeFinset.1 he) hxe
  calc G.edgeFinset.card ≤ (T.biUnion (fun x => G.incidenceFinset x)).card :=
        Finset.card_le_card hE
    _ ≤ ∑ x ∈ T, (G.incidenceFinset x).card := Finset.card_biUnion_le
    _ = ∑ x ∈ T, G.degree x := Finset.sum_congr rfl (fun x _ => card_incidenceFinset_eq_degree G x)
    _ ≤ T.card • G.maxDegree := Finset.sum_le_card_nsmul _ _ _ (fun x _ => G.degree_le_maxDegree x)
    _ ≤ 2 * M.card * G.maxDegree := by
        rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hT

lemma star_le {V : Type} (G : SimpleGraph V) (v : V) : fromEdgeSet (G.incidenceSet v) ≤ G := by
  intro x y h
  rw [fromEdgeSet_adj, mk'_mem_incidenceSet_iff] at h
  exact h.1.1

lemma star_free {V : Type} (G : SimpleGraph V) (v : V) :
    (cycleGraph 4).Free (fromEdgeSet (G.incidenceSet v)) := by
  apply free_of
  intro a b c d hab hbc hcd hda hac hbd
  rw [fromEdgeSet_adj, mk'_mem_incidenceSet_iff] at hab hcd hbc hda
  obtain ⟨⟨_, h0⟩, _⟩ := hab
  obtain ⟨⟨_, h2⟩, _⟩ := hcd
  have hbc' := hbc.2
  have hda' := hda.2
  rcases h0 with h | h <;> rcases h2 with h' | h'
  · exact hac (h.symm.trans h')
  · exact hda' (h'.symm.trans h)
  · exact hbc' (h.symm.trans h')
  · exact hbd (h.symm.trans h')

lemma star_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (fromEdgeSet (G.incidenceSet v)).edgeSet.ncard = G.degree v := by
  rw [edgeSet_fromEdgeSet]
  have : G.incidenceSet v \ Sym2.diagSet = G.incidenceSet v := by
    ext e
    simp only [Set.mem_sdiff, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, G.not_isDiag_of_mem_edgeSet (G.incidenceSet_subset v h)⟩⟩
  rw [this, ← coe_incidenceFinset, Set.ncard_coe_finset, card_incidenceFinset_eq_degree]

lemma match_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : M ⊆ G.edgeFinset) :
    fromEdgeSet (M : Set (Sym2 V)) ≤ G := by
  intro x y h
  rw [fromEdgeSet_adj] at h
  exact G.mem_edgeSet.1 (G.mem_edgeFinset.1 (hM (Finset.mem_coe.1 h.1)))

lemma match_free {V : Type} (M : Finset (Sym2 V))
    (hP : ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f) :
    (cycleGraph 4).Free (fromEdgeSet (M : Set (Sym2 V))) := by
  apply free_of
  intro a b c d hab hbc _ _ hac _
  rw [fromEdgeSet_adj] at hab hbc
  have := hP _ (Finset.mem_coe.1 hab.1) _ (Finset.mem_coe.1 hbc.1) b
    (Sym2.mem_mk_right a b) (Sym2.mem_mk_left b c)
  rcases Sym2.eq_iff.1 this with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hab.2 h1
  · exact hac h1

lemma match_card {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : M ⊆ G.edgeFinset) :
    (fromEdgeSet (M : Set (Sym2 V))).edgeSet.ncard = M.card := by
  rw [edgeSet_fromEdgeSet]
  have : (M : Set (Sym2 V)) \ Sym2.diagSet = M := by
    ext e
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.1 (hM h))⟩⟩
  rw [this, Set.ncard_coe_finset]

end LB

theorem erdos_1008.variants.lower_bound :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (1 / 2 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  refine ⟨1 / 2, by norm_num, fun V _ G => ?_⟩
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨G, le_rfl, fun ⟨f⟩ => isEmptyElim (f 0), LB.key _ _ ?_⟩
    have := Nat.le_mul_self G.edgeSet.ncard
    linarith
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    obtain ⟨M, hMsub, hP, hcov⟩ := LB.exists_matching G.edgeFinset
    have hcount := LB.count G M hcov
    have hm : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← coe_edgeFinset, Set.ncard_coe_finset]
    rcases le_total M.card (G.degree v) with hle | hle
    · refine ⟨fromEdgeSet (G.incidenceSet v), LB.star_le G v, LB.star_free G v, ?_⟩
      rw [LB.star_card]
      apply LB.key
      rw [hm]
      calc G.edgeFinset.card ≤ 2 * M.card * G.maxDegree := hcount
        _ ≤ 2 * (G.degree v * G.degree v) := by
          rw [hv, Nat.mul_assoc]
          exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hle)
    · refine ⟨fromEdgeSet (M : Set (Sym2 V)), LB.match_le G M hMsub, LB.match_free M hP, ?_⟩
      rw [LB.match_card G M hMsub]
      apply LB.key
      rw [hm]
      calc G.edgeFinset.card ≤ 2 * M.card * G.maxDegree := hcount
        _ ≤ 2 * (M.card * M.card) := by
          rw [hv, Nat.mul_assoc]
          exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hle)

end Erdos1008

#print axioms Erdos1008.erdos_1008.variants.lower_bound
