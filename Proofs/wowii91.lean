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

noncomputable abbrev l (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph

universe u

namespace WrittenOnTheWallII.GraphConjecture91

open SimpleGraph Finset

/-- Edge list of the counterexample (graph6 `JBza_CB?wF_`). -/
def E : List (ℕ × ℕ) := [(0,4),(0,5),(1,4),(1,5),(2,4),(2,5),(1,3),(2,3),(1,6),(3,6),
  (6,7),(6,8),(6,9),(6,10),(7,8),(7,9),(7,10),(8,9),(8,10),(9,10)]

def adjF (i j : Fin 11) : Prop := (i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_irrefl : ∀ i : Fin 11, ¬ adjF i i := by decide

/-- The counterexample graph on `ULift (Fin 11)`. -/
def G' : SimpleGraph (ULift.{u} (Fin 11)) where
  Adj x y := adjF x.down y.down
  symm := ⟨fun x y h => by unfold adjF at *; exact h.symm⟩
  loopless := ⟨fun x h => adjF_irrefl x.down h⟩

instance : DecidableRel (G'.{u}).Adj := fun x y =>
  inferInstanceAs (Decidable (adjF x.down y.down))

lemma G'_adj (x y : ULift.{u} (Fin 11)) : G'.Adj x y ↔ adjF x.down y.down := Iff.rfl

lemma card_V : Fintype.card (ULift.{u} (Fin 11)) = 11 := by simp

/-! ### Connectivity -/

lemma connected : (G'.{u}).Connected := by
  have A : ∀ i j : Fin 11, adjF i j → G'.{u}.Reachable (ULift.up i) (ULift.up j) :=
    fun i j h => Adj.reachable h
  have hR : ∀ i : Fin 11, G'.{u}.Reachable (ULift.up 0) (ULift.up i) := by
    have r4 := A 0 4 (by decide)
    have r1 := r4.trans (A 4 1 (by decide))
    have r6 := r1.trans (A 1 6 (by decide))
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact r1
    · exact r4.trans (A 4 2 (by decide))
    · exact r1.trans (A 1 3 (by decide))
    · exact r4
    · exact A 0 5 (by decide)
    · exact r6
    · exact r6.trans (A 6 7 (by decide))
    · exact r6.trans (A 6 8 (by decide))
    · exact r6.trans (A 6 9 (by decide))
    · exact r6.trans (A 6 10 (by decide))
  rw [connected_iff]
  exact ⟨fun u v => (hR u.down).symm.trans (hR v.down), ⟨ULift.up 0⟩⟩

/-! ### `b G' ≥ 8` -/

def S8 : Finset (Fin 11) := {0, 1, 2, 3, 4, 5, 7, 8}

def col (i : Fin 11) : Fin 2 := if i.val ∈ [0, 1, 2, 7] then 0 else 1

lemma col_ok : ∀ i j : Fin 11, i ∈ S8 → j ∈ S8 → adjF i j → col i ≠ col j := by decide

lemma b_ge : (8 : ℝ) ≤ b G'.{u} := by
  set s : Finset (ULift.{u} (Fin 11)) := S8.map Equiv.ulift.symm.toEmbedding with hs
  have hmem : ∀ x : ULift.{u} (Fin 11), x ∈ s ↔ x.down ∈ S8 := by
    intro x
    rw [hs, Finset.mem_map_equiv]
    rfl
  have hbip : (G'.{u}.induce (s : Set (ULift.{u} (Fin 11)))).IsBipartite := by
    refine ⟨Coloring.mk (fun x => col x.1.down) ?_⟩
    intro x y hxy
    exact col_ok _ _ ((hmem _).1 x.2) ((hmem _).1 y.2) hxy
  have hcard : s.card = 8 := by rw [hs, card_map]; rfl
  unfold b largestInducedBipartiteSubgraphSize
  have : 8 ≤ sSup { n | ∃ s : Finset (ULift.{u} (Fin 11)),
      (G'.{u}.induce (s : Set _)).IsBipartite ∧ s.card = n } := by
    apply le_csSup
    · refine ⟨Fintype.card (ULift.{u} (Fin 11)), ?_⟩
      rintro _ ⟨t, -, rfl⟩
      exact card_le_univ t
    · exact ⟨s, hbip, hcard⟩
  exact_mod_cast this

/-! ### Largest induced forest `≤ 6` -/

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

lemma K_clique : ∀ i j : Fin 11, 6 ≤ i.val → 6 ≤ j.val → i ≠ j → adjF i j := by decide

lemma card_A : (univ.filter (fun i : Fin 11 => i.val < 6)).card = 6 := by decide

lemma forest_le : G'.{u}.largestInducedForestSize ≤ 6 := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro _ ⟨s, hs, rfl⟩
  by_contra hlt
  push Not at hlt
  set t : Finset (Fin 11) := s.map Equiv.ulift.toEmbedding with ht
  have hmem : ∀ i : Fin 11, i ∈ t ↔ ULift.up i ∈ s := by
    intro i
    rw [ht, Finset.mem_map_equiv]
    rfl
  have htc : t.card = s.card := by rw [ht, card_map]
  have hsplit := Finset.card_filter_add_card_filter_not (s := t) (fun i : Fin 11 => i.val < 6)
  have adjI : ∀ i j : Fin 11, (hi : i ∈ t) → (hj : j ∈ t) → adjF i j →
      (G'.{u}.induce (s : Set _)).Adj ⟨ULift.up i, (hmem i).1 hi⟩ ⟨ULift.up j, (hmem j).1 hj⟩ :=
    fun i j _ _ h => h
  by_cases h5 : 5 ≤ (t.filter (fun i : Fin 11 => i.val < 6)).card
  · have hp : ∀ x y : Fin 11, x.val < 6 → y.val < 6 → x ≠ y → x ∉ t → y ∉ t → False := by
      intro x y hx hy hxy hxt hyt
      have hsub : t.filter (fun i : Fin 11 => i.val < 6) ⊆
          ((univ.filter (fun i : Fin 11 => i.val < 6)).erase x).erase y := by
        intro z hz
        rw [mem_filter] at hz
        rw [mem_erase, mem_erase, mem_filter]
        refine ⟨fun e => hyt (e ▸ hz.1), fun e => hxt (e ▸ hz.1), mem_univ _, hz.2⟩
      have c1 := card_le_card hsub
      have hxA : x ∈ univ.filter (fun i : Fin 11 => i.val < 6) := mem_filter.2 ⟨mem_univ _, hx⟩
      rw [card_erase_of_mem (mem_erase.2 ⟨hxy.symm, mem_filter.2 ⟨mem_univ _, hy⟩⟩),
        card_erase_of_mem hxA, card_A] at c1
      omega
    have mem : ∀ m v : Fin 11, m.val < 6 → v.val < 6 → v ≠ m → m ∉ t → v ∈ t := by
      intro m v hm hv hvm hmt
      by_contra hvt
      exact hp m v hm hv (Ne.symm hvm) hmt hvt
    have c4 : ∀ a b c d : Fin 11, (ha : a ∈ t) → (hb : b ∈ t) → (hc : c ∈ t) → (hd : d ∈ t) →
        (adjF a b ∧ adjF b c ∧ adjF c d ∧ adjF d a ∧ a ≠ c ∧ b ≠ d) → False := by
      intro a b c d ha hb hc hd ⟨h1, h2, h3, h4, hac, hbd⟩
      exact not_acyc_c4 _ (adjI a b ha hb h1) (adjI b c hb hc h2) (adjI c d hc hd h3)
        (adjI d a hd ha h4) (fun e => hac (congrArg (fun z => z.1.down) e))
        (fun e => hbd (congrArg (fun z => z.1.down) e)) hs
    by_cases m1 : (1 : Fin 11) ∈ t
    · by_cases m4 : (4 : Fin 11) ∈ t
      · by_cases m2 : (2 : Fin 11) ∈ t
        · by_cases m5 : (5 : Fin 11) ∈ t
          · exact c4 1 4 2 5 m1 m4 m2 m5 (by decide)
          · exact c4 1 3 2 4 m1 (mem 5 3 (by decide) (by decide) (by decide) m5) m2 m4
              (by decide)
        · exact c4 0 4 1 5 (mem 2 0 (by decide) (by decide) (by decide) m2) m4 m1
            (mem 2 5 (by decide) (by decide) (by decide) m2) (by decide)
      · exact c4 1 3 2 5 m1 (mem 4 3 (by decide) (by decide) (by decide) m4)
          (mem 4 2 (by decide) (by decide) (by decide) m4)
          (mem 4 5 (by decide) (by decide) (by decide) m4) (by decide)
    · exact c4 0 4 2 5 (mem 1 0 (by decide) (by decide) (by decide) m1)
        (mem 1 4 (by decide) (by decide) (by decide) m1)
        (mem 1 2 (by decide) (by decide) (by decide) m1)
        (mem 1 5 (by decide) (by decide) (by decide) m1) (by decide)
  · have h3 : 2 < (t.filter (fun i : Fin 11 => ¬ i.val < 6)).card := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h3
    rw [mem_filter] at ha hb hc
    have K := fun x y (hx : ¬ x.val < 6) (hy : ¬ y.val < 6) (hxy : x ≠ y) =>
      K_clique x y (by omega) (by omega) hxy
    exact not_acyc_tri _ (adjI a b ha.1 hb.1 (K a b ha.2 hb.2 hab))
      (adjI b c hb.1 hc.1 (K b c hb.2 hc.2 hbc)) (adjI c a hc.1 ha.1 (K c a hc.2 ha.2 hac.symm)) hs

/-! ### `l G' ≤ 2` -/

def kv (i : Fin 11) : ℕ := [2, 3, 3, 2, 3, 3, 2, 1, 1, 1, 1].getD i.val 0

lemma kv_sum : ∑ i : Fin 11, kv i = 22 := by decide

/-- Clique cover of `N(v)` with `kv v` cliques: index of the clique containing `x`. -/
def g (v x : Fin 11) : ℕ :=
  match v.val with
  | 0 => x.val - 4
  | 1 => if x.val = 6 then 0 else x.val - 3
  | 2 => x.val - 3
  | 3 => if x.val = 2 then 1 else 0
  | 4 => x.val
  | 5 => x.val
  | 6 => if x.val < 6 then 0 else 1
  | _ => 0

lemma g_lt : ∀ v x : Fin 11, adjF v x → g v x < kv v := by decide

set_option maxRecDepth 100000 in
lemma g_clique : ∀ v x y : Fin 11, adjF v x → adjF v y → x ≠ y → g v x = g v y →
    adjF x y := by decide

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

lemma inc_le (v : ULift.{u} (Fin 11)) : indepNeighborsCard G'.{u} v ≤ kv v.down := by
  unfold indepNeighborsCard
  apply indepNum_induce_le
  intro t hsub hind
  set t' : Finset (Fin 11) := t.map Equiv.ulift.toEmbedding with ht
  have hmem : ∀ i : Fin 11, i ∈ t' ↔ ULift.up i ∈ t := by
    intro i
    rw [ht, Finset.mem_map_equiv]
    rfl
  rw [← card_map Equiv.ulift.toEmbedding]
  have hadj : ∀ i ∈ t', adjF v.down i := fun i hi => hsub ((hmem i).1 hi)
  have hle := Finset.card_le_card_of_injOn (g v.down) (t := range (kv v.down))
    (s := t') (fun i hi => mem_coe.2 (mem_range.2 (g_lt _ _ (hadj i hi)))) ?_
  · rw [card_range] at hle
    exact hle
  · intro x hx y hy hg
    by_contra e
    have hxy := g_clique _ x y (hadj x hx) (hadj y hy) e hg
    exact hind (mem_coe.2 ((hmem x).1 hx)) (mem_coe.2 ((hmem y).1 hy))
      (fun h => e (congrArg ULift.down h)) hxy

lemma l_le : l G'.{u} ≤ 2 := by
  unfold l averageIndepNeighbors indepNeighbors
  rw [card_V]
  have h1 : ∑ v : ULift.{u} (Fin 11), indepNeighborsCard G'.{u} v ≤
      ∑ v : ULift.{u} (Fin 11), kv v.down := sum_le_sum (fun v _ => inc_le v)
  have h2 : ∑ v : ULift.{u} (Fin 11), kv v.down = 22 := by
    rw [← kv_sum]
    exact Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)
  have h3 : ((∑ v : ULift.{u} (Fin 11), indepNeighborsCard G'.{u} v : ℕ) : ℝ) ≤ 22 := by
    exact_mod_cast h1.trans h2.le
  have h4 := h3
  rw [Nat.cast_sum] at h4
  have h11 : ((11 : ℕ) : ℝ) = 11 := by norm_num
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma l_nonneg : 0 ≤ l G'.{u} := by
  unfold l averageIndepNeighbors
  apply div_nonneg
  · apply Finset.sum_nonneg; intro v _; exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

theorem conjecture91 :
    ¬ ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        b G ≤ 1 + (G.largestInducedForestSize : ℝ) * ⌈l G⌉ / 2 := by
  intro h
  have H := h G' connected
  have hb := b_ge
  have hf : ((G'.largestInducedForestSize : ℕ) : ℝ) ≤ 6 := by exact_mod_cast forest_le
  have hf0 : (0 : ℝ) ≤ ((G'.largestInducedForestSize : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc : ⌈l G'⌉ ≤ 2 := Int.ceil_le.2 (by exact_mod_cast l_le)
  have hc0 : 0 ≤ ⌈l G'⌉ := Int.ceil_nonneg l_nonneg
  have hc' : ((⌈l G'⌉ : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hc
  have hc0' : (0 : ℝ) ≤ ((⌈l G'⌉ : ℤ) : ℝ) := by exact_mod_cast hc0
  have hprod : ((G'.largestInducedForestSize : ℕ) : ℝ) * ((⌈l G'⌉ : ℤ) : ℝ) ≤ 12 := by
    nlinarith
  linarith

end WrittenOnTheWallII.GraphConjecture91

#print axioms WrittenOnTheWallII.GraphConjecture91.conjecture91
