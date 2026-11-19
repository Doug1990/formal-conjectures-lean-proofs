import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! WOWII 438b. Definitions restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean. -/

namespace SimpleGraph
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Edges of `G` whose two endpoints lie in `S`. -/
def internalEdges (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) :
    Finset (Sym2 α) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ S

/-- A vertex set is 2-independent when its induced graph has maximum degree
at most one. -/
def IsTwoIndependent (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v ∈ S, (S.filter fun w => G.Adj v w).card ≤ 1

/-- Maximum cardinality of an independent subset contained in `B`. -/
noncomputable def indepNumOn (G : SimpleGraph α) [DecidableRel G.Adj]
    (B : Finset α) : ℕ :=
  by
    classical
    exact (B.powerset.filter fun (A : Finset α) => G.IsIndepSet (A : Set α)).sup card

/-- Maximum cardinality of a 2-independent vertex set. -/
noncomputable def alphaTwo (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  by
    classical
    exact (Finset.univ.powerset.filter fun S => IsTwoIndependent G S).sup card

/-- The set of vertices of degree at most two. -/
def lowDegreeLayer (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter fun v => G.degree v ≤ 2

end SimpleGraph

namespace W438

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices outside `H` get larger keys; keys are injective. -/
noncomputable def key (H : Finset V) (x : V) : ℕ :=
  (if x ∈ H then 0 else Fintype.card V) + (Fintype.equivFin V x : ℕ)

lemma key_inj (H : Finset V) {x y : V} (h : key H x = key H y) : x = y := by
  unfold key at h
  have hx := (Fintype.equivFin V x).isLt
  have hy := (Fintype.equivFin V y).isLt
  have : (Fintype.equivFin V x : ℕ) = Fintype.equivFin V y := by
    split_ifs at h <;> omega
  exact (Fintype.equivFin V).injective (Fin.ext this)

lemma key_H (H : Finset V) {x y : V} (hx : x ∈ H) (h : key H y < key H x) : y ∈ H := by
  by_contra hy
  unfold key at h
  rw [if_pos hx, if_neg hy] at h
  have := (Fintype.equivFin V x).isLt
  omega

omit [Fintype V] [DecidableEq V] in
lemma partner_unique {S : Finset V} (hS : IsTwoIndependent G S) {x y z : V} (hx : x ∈ S)
    (hy : y ∈ S) (hz : z ∈ S) (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z :=
  Finset.card_le_one.1 (hS x hx) y (Finset.mem_filter.2 ⟨hy, hxy⟩) z
    (Finset.mem_filter.2 ⟨hz, hxz⟩)

/-- The removed endpoints: one per edge of `G[S]`, the one with the larger key. -/
noncomputable def remv (H S : Finset V) : Finset V :=
  S.filter (fun x => ∃ y ∈ S, G.Adj x y ∧ key H y < key H x)

lemma mem_remv (H S : Finset V) (x : V) :
    x ∈ remv G H S ↔ x ∈ S ∧ ∃ y ∈ S, G.Adj x y ∧ key H y < key H x := by
  unfold remv
  rw [Finset.mem_filter]

lemma bound (H S : Finset V) (hS : IsTwoIndependent G S) :
    S.card ≤ G.indepNum + indepNumOn G (univ \ H) + (internalEdges G H).card := by
  have hRS : remv G H S ⊆ S := fun x hx => ((mem_remv G H S x).1 hx).1
  -- the kept part is independent
  have h1 : (S \ remv G H S).card ≤ G.indepNum := by
    apply IsIndepSet.card_le_indepNum
    intro x hx y hy hxy hadj
    have hx' := Finset.mem_sdiff.1 hx
    have hy' := Finset.mem_sdiff.1 hy
    rcases Nat.lt_or_gt_of_ne (fun e => hxy (key_inj H e)) with h | h
    · exact hy'.2 ((mem_remv G H S y).2 ⟨hy'.1, x, hx'.1, hadj.symm, h⟩)
    · exact hx'.2 ((mem_remv G H S x).2 ⟨hx'.1, y, hy'.1, hadj, h⟩)
  -- the removed part is independent
  have hRind : ∀ x ∈ remv G H S, ∀ z ∈ remv G H S, ¬ G.Adj x z := by
    intro x hx z hz hxz
    obtain ⟨hxS, y, hyS, hxy, hk⟩ := (mem_remv G H S x).1 hx
    obtain ⟨hzS, w, hwS, hzw, hk'⟩ := (mem_remv G H S z).1 hz
    have e1 : y = z := partner_unique G hS hxS hyS hzS hxy hxz
    have e2 : w = x := partner_unique G hS hzS hwS hxS hzw hxz.symm
    rw [e1] at hk
    rw [e2] at hk'
    omega
  have h2 : (remv G H S \ H).card ≤ indepNumOn G (univ \ H) := by
    unfold indepNumOn
    apply Finset.le_sup (f := Finset.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hx).2⟩
    · intro x hx z hz _ hxz
      exact hRind x (Finset.mem_sdiff.1 hx).1 z (Finset.mem_sdiff.1 hz).1 hxz
  have h3 : (remv G H S ∩ H).card ≤ (internalEdges G H).card := by
    let f : V → Sym2 V := fun x =>
      if h : ∃ y ∈ S, G.Adj x y ∧ key H y < key H x then s(x, h.choose) else s(x, x)
    have hf : ∀ x ∈ remv G H S, ∃ y ∈ S, G.Adj x y ∧ key H y < key H x ∧ f x = s(x, y) := by
      intro x hx
      have hex := ((mem_remv G H S x).1 hx).2
      obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      refine ⟨hex.choose, h1, h2, h3, ?_⟩
      simp only [f]
      rw [dif_pos hex]
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hx' := Finset.mem_inter.1 hx
      obtain ⟨y, _, hxy, hk, hfx⟩ := hf x hx'.1
      rw [Finset.mem_coe, hfx]
      unfold internalEdges
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨hxy, ?_⟩
      intro z hz
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact hx'.2
      · exact key_H H hx'.2 hk
    · intro a ha b hb hab
      obtain ⟨ya, _, _, hka, hfa⟩ := hf a (Finset.mem_inter.1 ha).1
      obtain ⟨yb, _, _, hkb, hfb⟩ := hf b (Finset.mem_inter.1 hb).1
      rw [hfa, hfb, Sym2.eq_iff] at hab
      rcases hab with ⟨e, _⟩ | ⟨e1, e2⟩
      · exact e
      · rw [e1] at hka
        rw [← e2] at hkb
        omega
  have c1 := Finset.card_sdiff_add_card_inter S (remv G H S)
  have c2 := Finset.card_sdiff_add_card_inter (remv G H S) H
  rw [Finset.inter_eq_right.2 hRS] at c1
  omega

lemma mem_filter_gen {β : Type*} (s : Finset β) (p : β → Prop) (i : DecidablePred p) (x : β)
    (h : x ∈ @Finset.filter _ p i s) : p x :=
  (Finset.mem_filter.1 h).2

end W438

namespace WrittenOnTheWallII.GraphConjecture438b

open SimpleGraph Finset

theorem conjecture438b :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      alphaTwo G ≤ G.indepNum +
        indepNumOn G (Finset.univ \ lowDegreeLayer G) +
        (internalEdges G (lowDegreeLayer G)).card := by
  intro V _ _ G _ _ _
  unfold alphaTwo
  apply Finset.sup_le
  intro S hS
  exact W438.bound G _ S (W438.mem_filter_gen _ _ _ S hS)

end WrittenOnTheWallII.GraphConjecture438b

#print axioms WrittenOnTheWallII.GraphConjecture438b.conjecture438b
