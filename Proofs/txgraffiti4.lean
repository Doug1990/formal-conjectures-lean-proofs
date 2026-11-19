import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.Ring.Rat

/-! Local restatement of the definitions used by
`FormalConjectures/Arxiv/2507.17780/4.lean` (from FormalConjecturesForMathlib). -/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  G.IsEdgeMatching M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ G.IsEdgeMatching (insert e M)

noncomputable def saturationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsMaximalEdgeMatching M ∧ M.card = n}

def harmonicIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (2 : ℚ) / ((G.degree u : ℚ) + (G.degree v : ℚ)),
      fun u v => by simp only [add_comm]⟩

end SimpleGraph

open SimpleGraph

namespace Arxiv.«2507.17780»

def friendshipF4 : SimpleGraph (Fin 9) := fromEdgeSet {
  s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(0, 7), s(0, 8),
  s(1, 2), s(3, 4), s(5, 6), s(7, 8) }

instance : DecidableRel friendshipF4.Adj := by unfold friendshipF4; infer_instance

/-- The twelve edges as a `Finset`. -/
def E12 : Finset (Sym2 (Fin 9)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(0, 7), s(0, 8),
   s(1, 2), s(3, 4), s(5, 6), s(7, 8)}

/-- The four rim edges. -/
def R : Finset (Sym2 (Fin 9)) := {s(1, 2), s(3, 4), s(5, 6), s(7, 8)}

lemma mem_E12 {e : Sym2 (Fin 9)} (h : e ∈ friendshipF4.edgeSet) : e ∈ E12 := by
  unfold friendshipF4 at h
  rw [edgeSet_fromEdgeSet] at h
  have h1 := h.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  simp only [E12, Finset.mem_insert, Finset.mem_singleton]
  exact h1

lemma R_edge {r : Sym2 (Fin 9)} (hr : r ∈ R) : r ∈ friendshipF4.edgeSet := by
  simp only [R, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> (rw [mem_edgeSet]; decide)

lemma D : ∀ r ∈ R, ∀ e ∈ E12, e ≠ r → (∀ u : Fin 9, u ∈ r → e ≠ s(0, u)) →
    ∀ v : Fin 9, ¬ (v ∈ r ∧ v ∈ e) := by
  decide +kernel

lemma Dmax : ∀ e ∈ E12, e ∉ R → ∃ e₂ ∈ R, e ≠ e₂ ∧ ∃ v : Fin 9, v ∈ e ∧ v ∈ e₂ := by
  decide +kernel

lemma R_pair : ∀ e₁ ∈ R, ∀ e₂ ∈ R, e₁ = e₂ ∨ ∀ v : Fin 9, ¬ (v ∈ e₁ ∧ v ∈ e₂) := by
  decide +kernel

lemma tri (M : Finset (Sym2 (Fin 9))) (hM : friendshipF4.IsMaximalEdgeMatching M)
    (r : Sym2 (Fin 9)) (hr : r ∈ R) (h0 : ∀ u : Fin 9, u ∈ r → s(0, u) ∉ M) : r ∈ M := by
  by_contra hrM
  apply hM.2 r (R_edge hr) hrM
  have key : ∀ e ∈ M, e = r ∨ ∀ v : Fin 9, ¬ (v ∈ r ∧ v ∈ e) := by
    intro e he
    by_cases her : e = r
    · exact Or.inl her
    · right
      refine D r hr e (mem_E12 (hM.1.1 e he)) her ?_
      intro u hu heu
      exact h0 u hu (heu ▸ he)
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with h | h
    · rw [h]; exact R_edge hr
    · exact hM.1.1 e h
  · intro e₁ he₁ e₂ he₂
    rcases Finset.mem_insert.1 he₁ with h1 | h1 <;>
      rcases Finset.mem_insert.1 he₂ with h2 | h2
    · left; rw [h1, h2]
    · rcases key e₂ h2 with h | h
      · left; rw [h1, h]
      · right; rw [h1]; exact h
    · rcases key e₁ h1 with h | h
      · left; rw [h2, h]
      · right; rw [h2]; intro v hv; exact h v ⟨hv.2, hv.1⟩
    · exact hM.1.2 e₁ h1 e₂ h2

lemma spoke_uniq (M : Finset (Sym2 (Fin 9))) (hM : friendshipF4.IsEdgeMatching M)
    (v w : Fin 9) (hv : s(0, v) ∈ M) (hw : s(0, w) ∈ M) : v = w := by
  rcases hM.2 _ hv _ hw with h | h
  · exact Sym2.congr_right.1 h
  · exact absurd ⟨Sym2.mem_mk_left 0 v, Sym2.mem_mk_left 0 w⟩ (h 0)

lemma card_T : ∀ v : Fin 9, v ≠ 0 →
    (insert s(0, v) (R.filter (fun r => v ∉ r))).card = 4 := by
  decide +kernel

lemma card_R : R.card = 4 := by decide +kernel

lemma four_le (M : Finset (Sym2 (Fin 9))) (hM : friendshipF4.IsMaximalEdgeMatching M) :
    4 ≤ M.card := by
  by_cases hs : ∃ v : Fin 9, s(0, v) ∈ M
  · obtain ⟨v, hv⟩ := hs
    have hv0 : v ≠ 0 := by
      intro h
      subst h
      exact absurd ((mem_edgeSet _).1 (hM.1.1 _ hv)) (by decide)
    have hT : insert s(0, v) (R.filter (fun r => v ∉ r)) ⊆ M := by
      intro e he
      rcases Finset.mem_insert.1 he with h | h
      · rw [h]; exact hv
      · obtain ⟨hr, hvr⟩ := Finset.mem_filter.1 h
        apply tri M hM e hr
        intro u hu hu0
        have := spoke_uniq M hM.1 u v hu0 hv
        subst this
        exact hvr hu
    calc 4 = (insert s(0, v) (R.filter (fun r => v ∉ r))).card := (card_T v hv0).symm
      _ ≤ M.card := Finset.card_le_card hT
  · have hs' : ∀ u : Fin 9, s(0, u) ∉ M := fun u h => hs ⟨u, h⟩
    have hR : R ⊆ M := fun r hr => tri M hM r hr (fun u _ => hs' u)
    calc 4 = R.card := card_R.symm
      _ ≤ M.card := Finset.card_le_card hR

lemma R_max : friendshipF4.IsMaximalEdgeMatching R := by
  refine ⟨⟨fun e he => R_edge he, R_pair⟩, fun e he heR h => ?_⟩
  obtain ⟨e₂, he₂, hne, v, hv1, hv2⟩ := Dmax e (mem_E12 he) heR
  rcases h.2 e (Finset.mem_insert_self _ _) e₂ (Finset.mem_insert_of_mem he₂) with h' | h'
  · exact hne h'
  · exact h' v ⟨hv1, hv2⟩

lemma sat_ge : 4 ≤ friendshipF4.saturationNumber :=
  le_csInf ⟨4, R, R_max, card_R⟩ (by rintro n ⟨M, hM, rfl⟩; exact four_le M hM)

lemma harm : friendshipF4.harmonicIndex = 18 / 5 := by decide +kernel

lemma conn : friendshipF4.Connected := by
  have adj0 : ∀ v : Fin 9, v ≠ 0 → friendshipF4.Adj 0 v := by decide
  have r0 : ∀ v, friendshipF4.Reachable 0 v := fun v => by
    by_cases hv : v = 0
    · rw [hv]
    · exact (adj0 v hv).reachable
  exact ⟨fun u v => (r0 u).symm.trans (r0 v)⟩

theorem tx_graffiti_conjecture_4 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (_hConn : G.Connected),
      (G.saturationNumber : ℚ) ≤ G.harmonicIndex := by
  intro h
  have key := h (Fin 9) friendshipF4 conn
  rw [harm] at key
  have h4 : (4 : ℚ) ≤ (friendshipF4.saturationNumber : ℚ) := by exact_mod_cast sat_ge
  have h5 : (4 : ℚ) ≤ 18 / 5 := le_trans h4 key
  exact absurd h5 (by decide +kernel)

end Arxiv.«2507.17780»

#print axioms Arxiv.«2507.17780».tx_graffiti_conjecture_4
