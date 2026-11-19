import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
Independence.lean and Induced.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

noncomputable abbrev l_avg (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture58

open SimpleGraph Finset

/-! Counterexample: `K_{3,3}` on `{0,1,2} | {3,4,5}`, and a clique on
`Q = {0,3} ∪ {6,…,60}` (a `K_55` glued onto the edge `0–3`).
`b ≥ 6`, `f ≤ 5`, `Σ l(v) ≤ 73`, `n = 61`, so `b / l_avg > 5`. -/

def adjF (i j : Fin 61) : Prop :=
  (i.val < 3 ∧ 3 ≤ j.val ∧ j.val < 6) ∨ (j.val < 3 ∧ 3 ≤ i.val ∧ i.val < 6) ∨
  ((i.val = 0 ∨ i.val = 3 ∨ 6 ≤ i.val) ∧ (j.val = 0 ∨ j.val = 3 ∨ 6 ≤ j.val) ∧ i.val ≠ j.val)

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

def G : SimpleGraph (Fin 61) where
  Adj := adjF
  symm := ⟨fun x y h => by unfold adjF at *; omega⟩
  loopless := ⟨fun x h => by unfold adjF at h; omega⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma connected : G.Connected := by
  have A : ∀ i j : Fin 61, adjF i j → G.Reachable i j := fun i j h => Adj.reachable h
  have hR : ∀ i : Fin 61, G.Reachable 0 i := by
    intro i
    by_cases h0 : i.val = 0
    · obtain rfl : i = 0 := Fin.ext h0
      exact Reachable.refl _
    · by_cases h12 : i.val = 1 ∨ i.val = 2
      · exact (A 0 3 (by decide)).trans (A 3 i (by unfold adjF; simp; omega))
      · exact A 0 i (by unfold adjF; simp; omega)
  rw [connected_iff]
  exact ⟨fun u v => (hR u).symm.trans (hR v), ⟨0⟩⟩

/-! ### `b G ≥ 6` -/

def col (i : Fin 61) : Fin 2 := if i.val < 3 then 0 else 1

lemma col_ok : ∀ i j : Fin 61, i.val < 6 → j.val < 6 → adjF i j → col i ≠ col j := by
  intro i j hi hj h
  unfold adjF at h
  unfold col
  split_ifs <;> first | decide | (exfalso; omega)

def S6 : Finset (Fin 61) := univ.filter (fun i : Fin 61 => i.val < 6)

lemma mem_S6 (i : Fin 61) (h : i ∈ S6) : i.val < 6 := (mem_filter.1 h).2

lemma b_ge : (6 : ℝ) ≤ b G := by
  have hbip : (G.induce (S6 : Set (Fin 61))).IsBipartite := by
    refine ⟨Coloring.mk (fun x => col x.1) ?_⟩
    intro x y hxy
    exact col_ok _ _ (mem_S6 _ (mem_coe.1 x.2)) (mem_S6 _ (mem_coe.1 y.2)) hxy
  have hcard : S6.card = 6 := by decide
  unfold b largestInducedBipartiteSubgraphSize
  have : 6 ≤ sSup { n | ∃ s : Finset (Fin 61),
      (G.induce (s : Set _)).IsBipartite ∧ s.card = n } := by
    apply le_csSup
    · refine ⟨Fintype.card (Fin 61), ?_⟩
      rintro _ ⟨t, -, rfl⟩
      exact card_le_univ t
    · exact ⟨S6, hbip, hcard⟩
  exact_mod_cast this

/-! ### Largest induced forest `≤ 5` -/

lemma del_adj {W : Type*} {H : SimpleGraph W} {a b x y : W} (h : H.Adj x y)
    (h1 : ¬ (x = a ∧ y = b)) (h2 : ¬ (x = b ∧ y = a)) :
    (H.deleteEdges {s(a, b)}).Adj x y := by
  rw [deleteEdges_adj]
  refine ⟨h, ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

lemma not_acyc_tri {W : Type*} (H : SimpleGraph W) {a b c : W} (hab : H.Adj a b)
    (hbc : H.Adj b c) (hca : H.Adj c a) : ¬ H.IsAcyclic := by
  intro h
  rw [isAcyclic_iff_forall_adj_isBridge] at h
  have hb := h hab
  rw [isBridge_iff] at hb
  apply hb
  have hcb : c ≠ b := fun e => H.loopless.irrefl b (e ▸ hbc)
  have hca' : c ≠ a := H.ne_of_adj hca
  have hab' : a ≠ b := H.ne_of_adj hab
  have e1 : (H.deleteEdges {s(a, b)}).Adj a c :=
    del_adj hca.symm (fun ⟨_, e⟩ => hcb e) (fun ⟨e, _⟩ => hab' e)
  have e2 : (H.deleteEdges {s(a, b)}).Adj c b :=
    del_adj hbc.symm (fun ⟨e, _⟩ => hca' e) (fun ⟨e, _⟩ => hcb e)
  exact e1.reachable.trans e2.reachable

lemma not_acyc_c4 {W : Type*} (H : SimpleGraph W) {a b c d : W} (hab : H.Adj a b)
    (hbc : H.Adj b c) (hcd : H.Adj c d) (hda : H.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ H.IsAcyclic := by
  intro h
  rw [isAcyclic_iff_forall_adj_isBridge] at h
  have hb := h hab
  rw [isBridge_iff] at hb
  apply hb
  have hab' : a ≠ b := H.ne_of_adj hab
  have hda' : d ≠ a := H.ne_of_adj hda
  have e1 : (H.deleteEdges {s(a, b)}).Adj a d :=
    del_adj hda.symm (fun ⟨_, e⟩ => hbd e.symm) (fun ⟨e, _⟩ => hab' e)
  have e2 : (H.deleteEdges {s(a, b)}).Adj d c :=
    del_adj hcd.symm (fun ⟨e, _⟩ => hda' e) (fun ⟨e, _⟩ => hbd e.symm)
  have e3 : (H.deleteEdges {s(a, b)}).Adj c b :=
    del_adj hbc.symm (fun ⟨e, _⟩ => hac e.symm) (fun ⟨e1, e2⟩ => hac (e1.trans e2).symm)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)

def Qp (i : Fin 61) : Prop := i.val = 0 ∨ i.val = 3 ∨ 6 ≤ i.val

instance : DecidablePred Qp := fun i => by unfold Qp; infer_instance

lemma Q_clique : ∀ i j : Fin 61, Qp i → Qp j → i ≠ j → adjF i j := by
  intro i j hi hj hij
  have : i.val ≠ j.val := fun e => hij (Fin.ext e)
  unfold Qp at hi hj
  unfold adjF
  omega

lemma card_nQ : (univ.filter (fun i : Fin 61 => ¬ Qp i)).card = 4 := by decide

lemma forest_le : G.largestInducedForestSize ≤ 5 := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro _ ⟨s, hs, rfl⟩
  by_contra hlt
  push Not at hlt
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) Qp
  have adjI : ∀ i j : Fin 61, (hi : i ∈ s) → (hj : j ∈ s) → adjF i j →
      (G.induce (s : Set _)).Adj ⟨i, hi⟩ ⟨j, hj⟩ := fun i j _ _ h => h
  have hsub : s.filter (fun i => ¬ Qp i) ⊆ univ.filter (fun i : Fin 61 => ¬ Qp i) := by
    intro z hz
    rw [mem_filter] at hz ⊢
    exact ⟨mem_univ _, hz.2⟩
  have hle := card_le_card hsub
  rw [card_nQ] at hle
  by_cases h4 : (s.filter (fun i => ¬ Qp i)).card = 4
  · have heq := eq_of_subset_of_card_le hsub (by rw [card_nQ, h4])
    have mem : ∀ v : Fin 61, ¬ Qp v → v ∈ s := by
      intro v hv
      have : v ∈ univ.filter (fun i : Fin 61 => ¬ Qp i) := mem_filter.2 ⟨mem_univ _, hv⟩
      rw [← heq, mem_filter] at this
      exact this.1
    have m1 := mem 1 (by decide)
    have m2 := mem 2 (by decide)
    have m4 := mem 4 (by decide)
    have m5 := mem 5 (by decide)
    exact not_acyc_c4 _ (adjI 1 4 m1 m4 (by decide)) (adjI 4 2 m4 m2 (by decide))
      (adjI 2 5 m2 m5 (by decide)) (adjI 5 1 m5 m1 (by decide))
      (by intro e; have := congrArg Subtype.val e; simp at this)
      (by intro e; have := congrArg Subtype.val e; simp at this) hs
  · have h3 : 2 < (s.filter Qp).card := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h3
    rw [mem_filter] at ha hb hc
    exact not_acyc_tri _ (adjI a b ha.1 hb.1 (Q_clique a b ha.2 hb.2 hab))
      (adjI b c hb.1 hc.1 (Q_clique b c hb.2 hc.2 hbc))
      (adjI c a hc.1 ha.1 (Q_clique c a hc.2 ha.2 hac.symm)) hs

/-! ### `Σ l(v) ≤ 73` -/

def kv (i : Fin 61) : ℕ := if 6 ≤ i.val then 1 else 3

lemma kv_sum : ∑ i : Fin 61, kv i = 73 := by decide

/-- Clique cover of `N(v)` with `kv v` cliques: index of the clique containing `x`. -/
def g (v x : Fin 61) : ℕ :=
  if (v.val = 0 ∨ v.val = 3 ∨ 6 ≤ v.val) ∧ (x.val = 0 ∨ x.val = 3 ∨ 6 ≤ x.val) then 0
  else x.val % 3

lemma g_lt : ∀ v x : Fin 61, adjF v x → g v x < kv v := by
  intro v x h
  unfold adjF at h
  unfold g kv
  split_ifs <;> omega

lemma g_clique : ∀ v x y : Fin 61, adjF v x → adjF v y → x ≠ y → g v x = g v y →
    adjF x y := by
  intro v x y h1 h2 hxy hg
  have : x.val ≠ y.val := fun e => hxy (Fin.ext e)
  unfold adjF at h1 h2 ⊢
  unfold g at hg
  split_ifs at hg <;> omega

lemma indepNum_induce_le {W : Type*} [Fintype W] (H : SimpleGraph W) (S : Set W) (k : ℕ)
    (h : ∀ t : Finset W, (↑t ⊆ S) → H.IsIndepSet (t : Set W) → t.card ≤ k) :
    (H.induce S).indepNum ≤ k := by
  obtain ⟨s, hs⟩ := (H.induce S).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  rw [← card_map (Function.Embedding.subtype _)]
  apply h
  · intro x hx
    rw [mem_coe, mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    rw [mem_coe, mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun e => hxy (by rw [e])
    exact hs.isIndepSet (mem_coe.2 hx') (mem_coe.2 hy') hne

lemma inc_le (v : Fin 61) : indepNeighborsCard G v ≤ kv v := by
  unfold indepNeighborsCard
  apply indepNum_induce_le
  intro t hsub hind
  have hadj : ∀ i ∈ t, adjF v i := fun i hi => hsub hi
  have hle := Finset.card_le_card_of_injOn (g v) (t := range (kv v))
    (s := t) (fun i hi => mem_coe.2 (mem_range.2 (g_lt _ _ (hadj i hi)))) ?_
  · rw [card_range] at hle
    exact hle
  · intro x hx y hy hg
    by_contra e
    have hxy := g_clique _ x y (hadj x hx) (hadj y hy) e hg
    exact hind (mem_coe.2 hx) (mem_coe.2 hy) e hxy

lemma inc_pos : 1 ≤ indepNeighborsCard G 0 := by
  unfold indepNeighborsCard
  have h3 : (3 : Fin 61) ∈ G.neighborSet 0 := by
    show adjF 0 3
    decide
  have := SimpleGraph.IsIndepSet.card_le_indepNum (G := G.induce (G.neighborSet 0))
    (t := {⟨3, h3⟩}) (by rw [Finset.coe_singleton]; exact Set.pairwise_singleton _ _)
  simpa using this

lemma l_le : G.l_avg ≤ 73 / 61 := by
  unfold l_avg averageIndepNeighbors indepNeighbors
  have h1 : ∑ v : Fin 61, indepNeighborsCard G v ≤ ∑ v : Fin 61, kv v :=
    sum_le_sum (fun v _ => inc_le v)
  have h3 : ((∑ v : Fin 61, indepNeighborsCard G v : ℕ) : ℝ) ≤ 73 := by
    exact_mod_cast h1.trans kv_sum.le
  rw [Nat.cast_sum] at h3
  rw [Fintype.card_fin, div_le_iff₀ (by norm_num)]
  have e : (73 : ℝ) / 61 * ((61 : ℕ) : ℝ) = 73 := by norm_num
  rw [e]
  exact h3

lemma l_pos : 0 < G.l_avg := by
  unfold l_avg averageIndepNeighbors indepNeighbors
  apply div_pos _ (by norm_num)
  have h0 : ((1 : ℕ) : ℝ) ≤ (indepNeighborsCard G 0 : ℝ) := by exact_mod_cast inc_pos
  have := Finset.single_le_sum (f := fun v => (indepNeighborsCard G v : ℝ))
    (fun v _ => Nat.cast_nonneg _) (mem_univ (0 : Fin 61))
  push_cast at h0
  linarith

theorem conjecture58 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      Nat.ceil (G.b / G.l_avg) ≤ G.largestInducedForestSize := by
  intro h
  have H := h (Fin 61) G connected
  have hf := forest_le
  have hb := b_ge
  have hl := l_le
  have hl0 := l_pos
  have h5 : ((5 : ℕ) : ℝ) < G.b / G.l_avg := by
    rw [lt_div_iff₀ hl0]
    push_cast
    linarith
  have := Nat.lt_ceil.2 h5
  omega

end WrittenOnTheWallII.GraphConjecture58

#print axioms WrittenOnTheWallII.GraphConjecture58.conjecture58
