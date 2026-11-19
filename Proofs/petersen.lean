import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

namespace SimpleGraph

variable {V : Type*}

/-- `G` is bridgeless if none of its edges is a bridge (restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cycle.lean). -/
def IsBridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

end SimpleGraph

open SimpleGraph Finset

namespace BergeFulkersonConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **cubic** if every vertex has degree `3`. -/
def IsCubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

namespace P

lemma even_inner (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    Even (univ.filter (fun p : V × V => p.1 ∈ C ∧ p.2 ∈ C ∧ G.Adj p.1 p.2)).card := by
  let e := Fintype.equivFin V
  set A := univ.filter (fun p : V × V => p.1 ∈ C ∧ p.2 ∈ C ∧ G.Adj p.1 p.2) with hA
  set L := A.filter (fun p => e p.1 < e p.2) with hL
  have hR : A.filter (fun p => ¬ e p.1 < e p.2) = L.image Prod.swap := by
    ext ⟨a, b⟩
    simp only [hA, hL, mem_filter, mem_univ, true_and, mem_image, Prod.exists, Prod.swap_prod_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, hlt⟩
      have hne : e a ≠ e b := fun h => hab.ne (e.injective h)
      exact ⟨b, a, ⟨⟨hb, ha, hab.symm⟩, lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)⟩, rfl, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy, hxy⟩, hlt⟩, rfl, rfl⟩
      exact ⟨⟨hy, hx, hxy.symm⟩, not_lt.mpr hlt.le⟩
  have h0 := card_filter_add_card_filter_not (s := A) (p := fun p => e p.1 < e p.2)
  rw [hR, card_image_of_injective _ Prod.swap_injective] at h0
  exact ⟨L.card, h0.symm⟩

lemma card_T (G : SimpleGraph V) [DecidableRel G.Adj] (hc : IsCubic G) (C : Finset V) :
    (univ.filter (fun p : V × V => p.1 ∈ C ∧ G.Adj p.1 p.2)).card = 3 * C.card := by
  rw [card_filter, Fintype.sum_prod_type]
  have h : ∀ x : V, (∑ y : V, if x ∈ C ∧ G.Adj x y then 1 else 0) = if x ∈ C then 3 else 0 := by
    intro x
    by_cases hx : x ∈ C
    · simp only [hx, true_and, if_true]
      have := hc x
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter] at this
      rw [← this, card_filter]
    · simp [hx]
  simp only [h]
  rw [sum_ite_mem, univ_inter, sum_const, smul_eq_mul, mul_comm]

/-- Edges leaving an odd vertex set of a cubic bridgeless graph: at least 3. -/
lemma three_le (G : SimpleGraph V) [DecidableRel G.Adj] (hc : IsCubic G)
    (hb : G.IsBridgeless) (C : Finset V) (hodd : Odd C.card) :
    3 ≤ (univ.filter (fun p : V × V => p.1 ∈ C ∧ p.2 ∉ C ∧ G.Adj p.1 p.2)).card := by
  set B := univ.filter (fun p : V × V => p.1 ∈ C ∧ p.2 ∉ C ∧ G.Adj p.1 p.2) with hB
  set A := univ.filter (fun p : V × V => p.1 ∈ C ∧ p.2 ∈ C ∧ G.Adj p.1 p.2) with hA
  set T := univ.filter (fun p : V × V => p.1 ∈ C ∧ G.Adj p.1 p.2) with hT
  have hsplit := card_filter_add_card_filter_not (s := T) (p := fun p => p.2 ∈ C)
  have h1 : T.filter (fun p => p.2 ∈ C) = A := by
    ext p; simp only [hT, hA, mem_filter, mem_univ, true_and]; tauto
  have h2 : T.filter (fun p => ¬ p.2 ∈ C) = B := by
    ext p; simp only [hT, hB, mem_filter, mem_univ, true_and]; tauto
  rw [h1, h2, hT, card_T G hc C] at hsplit
  have hA2 : Even A.card := even_inner G C
  obtain ⟨a, ha⟩ := hA2
  obtain ⟨k, hk⟩ := hodd
  have hne : B.card ≠ 1 := by
    intro h1
    obtain ⟨⟨x, y⟩, hxy⟩ := card_eq_one.mp h1
    have hmem : (x, y) ∈ B := by rw [hxy]; exact mem_singleton_self _
    simp only [hB, mem_filter, mem_univ, true_and] at hmem
    obtain ⟨hx, hy, hadj⟩ := hmem
    have hnb := hb s(x, y) hadj
    rw [isBridge_iff, not_not] at hnb
    obtain ⟨p⟩ := hnb
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (C : Set V) hx hy
    have hdadj := d.adj
    rw [deleteEdges_adj] at hdadj
    have hdB : (d.fst, d.snd) ∈ B := by
      simp only [hB, mem_filter, mem_univ, true_and]
      exact ⟨hd1, hd2, hdadj.1⟩
    rw [hxy, mem_singleton, Prod.mk.injEq] at hdB
    apply hdadj.2
    rw [hdB.1, hdB.2]
    exact Set.mem_singleton _
  omega

section comp

variable (G : SimpleGraph V) (u : Set V)

open Classical in
/-- The vertex set (in `V`) of a connected component of `G - u`. -/
noncomputable def Cf (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) : Finset V :=
  univ.filter (fun v => ∃ h : v ∈ ((⊤ : G.Subgraph).deleteVerts u).verts,
    ((⊤ : G.Subgraph).deleteVerts u).coe.connectedComponentMk ⟨v, h⟩ = c)

omit [DecidableEq V] in
lemma mem_Cf {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} {v : V} :
    v ∈ Cf G u c ↔ ∃ h : v ∈ ((⊤ : G.Subgraph).deleteVerts u).verts,
      ((⊤ : G.Subgraph).deleteVerts u).coe.connectedComponentMk ⟨v, h⟩ = c := by
  simp only [Cf, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
lemma card_Cf (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) :
    (Cf G u c).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective c.supp Subtype.val_injective]
  congr 1
  ext v
  rw [Finset.mem_coe, mem_Cf]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨⟨v, h⟩, (ConnectedComponent.mem_supp_iff _ _).mpr hc, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, (ConnectedComponent.mem_supp_iff _ _).mp hw⟩

omit [DecidableEq V] in
lemma closure {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} {v w : V}
    (hv : v ∈ Cf G u c) (hadj : G.Adj v w) (hw : w ∉ Cf G u c) : w ∈ u := by
  by_contra hwu
  obtain ⟨h, rfl⟩ := (mem_Cf G u).mp hv
  apply hw
  have hvu : v ∉ u := by simpa using h
  have hw' : w ∈ ((⊤ : G.Subgraph).deleteVerts u).verts := by simp [hwu]
  rw [mem_Cf]
  refine ⟨hw', ?_⟩
  refine (ConnectedComponent.connectedComponentMk_eq_of_adj ?_).symm
  simp [Subgraph.coe_adj, hvu, hwu, hadj]

omit [DecidableEq V] in
lemma disj {c d : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (Cf G u c) (Cf G u d) := by
  rw [Finset.disjoint_left]
  intro v hc hd
  obtain ⟨h, rfl⟩ := (mem_Cf G u).mp hc
  obtain ⟨h', rfl⟩ := (mem_Cf G u).mp hd
  exact hcd rfl

end comp

end P

/-- **Petersen's theorem (1891): every bridgeless cubic graph has a perfect matching.** -/
theorem berge_fulkerson_conjecture.variants.petersen
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : IsCubic G) (hbridgeless : G.IsBridgeless) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rw [tutte]
  intro u hu
  unfold IsTutteViolator at hu
  set H := ((⊤ : G.Subgraph).deleteVerts u).coe with hH
  have hOf : H.oddComponents.Finite := Set.toFinite _
  have huf : u.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hOf, Set.ncard_eq_toFinset_card _ huf] at hu
  set OF := hOf.toFinset with hOF
  set uF := huf.toFinset with huF
  let B : H.ConnectedComponent → Finset (V × V) := fun c =>
    univ.filter (fun p : V × V => p.1 ∈ P.Cf G u c ∧ p.2 ∉ P.Cf G u c ∧ G.Adj p.1 p.2)
  set D := univ.filter (fun p : V × V => p.1 ∈ uF ∧ G.Adj p.1 p.2) with hD
  have hDc : D.card = 3 * uF.card := P.card_T G hcubic uF
  have hsub : OF.biUnion B ⊆ D.image Prod.swap := by
    intro p hp
    rw [mem_biUnion] at hp
    obtain ⟨c, -, hpc⟩ := hp
    simp only [B, mem_filter, mem_univ, true_and] at hpc
    rw [mem_image]
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [hD, huF, mem_filter, mem_univ, true_and, Set.Finite.mem_toFinset]
    exact ⟨P.closure G u hpc.1 hpc.2.2 hpc.2.1, hpc.2.2.symm⟩
  have hcard : (OF.biUnion B).card = ∑ c ∈ OF, (B c).card := by
    apply card_biUnion
    intro c _ d _ hcd
    show Disjoint (B c) (B d)
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [B, mem_filter, mem_univ, true_and] at hp hq
    exact Finset.disjoint_left.mp (P.disj G u hcd) hp.1 hq.1
  have hlow : 3 * OF.card ≤ ∑ c ∈ OF, (B c).card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro c hc
    apply P.three_le G hcubic hbridgeless
    rw [P.card_Cf]
    have hc' : c ∈ H.oddComponents := (Set.Finite.mem_toFinset hOf).mp hc
    exact hc'
  have hle := card_le_card hsub
  rw [card_image_of_injective _ Prod.swap_injective, hDc, hcard] at hle
  omega

end BergeFulkersonConjecture

#print axioms BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.petersen
