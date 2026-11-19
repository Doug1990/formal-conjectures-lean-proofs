import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset

namespace SimpleGraph

/-- Copied verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean -/
abbrev PetersenVertex : Type := {s : Finset (Fin 5) // s.card = 2}

def petersenGraph : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have hc := s.2
    rw [disjoint_self.mp h] at hc
    simp at hc⟩

instance : DecidableRel petersenGraph.Adj := fun s t =>
  inferInstanceAs (Decidable (Disjoint s.1 t.1))

end SimpleGraph

open SimpleGraph

namespace WrittenOnTheWallII.Test

abbrev PetersenGraph : SimpleGraph PetersenVertex := petersenGraph

lemma card_le_five (s : Finset (Fin 5)) : s.card ≤ 5 := by
  simpa using Finset.card_le_univ s

lemma three_le_card_union (x y : PetersenVertex) (h : x ≠ y) : 3 ≤ (x.1 ∪ y.1).card := by
  by_contra hlt
  have hlt' : (x.1 ∪ y.1).card ≤ 2 := by omega
  have hx : x.1 = x.1 ∪ y.1 :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [x.2]; exact hlt')
  have hy : y.1 = x.1 ∪ y.1 :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [y.2]; exact hlt')
  exact h (Subtype.ext (hx.trans hy.symm))

lemma no_triangle (a b c : PetersenVertex) (hab : Disjoint a.1 b.1) (hbc : Disjoint b.1 c.1)
    (hca : Disjoint c.1 a.1) : False := by
  have h1 := Finset.card_union_of_disjoint hab
  have h2 := Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨hca.symm, hbc⟩ : Disjoint (a.1 ∪ b.1) c.1)
  have h3 := card_le_five (a.1 ∪ b.1 ∪ c.1)
  rw [a.2, b.2] at h1
  rw [h1, c.2] at h2
  omega

lemma no_square (a b c d : PetersenVertex) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : Disjoint a.1 b.1) (hbc : Disjoint b.1 c.1) (hcd : Disjoint c.1 d.1)
    (hda : Disjoint d.1 a.1) : False := by
  have hdisj : Disjoint (a.1 ∪ c.1) (b.1 ∪ d.1) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hab, hda.symm⟩, ⟨hbc.symm, hcd⟩⟩
  have h1 := Finset.card_union_of_disjoint hdisj
  have h2 := card_le_five ((a.1 ∪ c.1) ∪ (b.1 ∪ d.1))
  have h3 := three_le_card_union a c hac
  have h4 := three_le_card_union b d hbd
  omega

lemma no_short_cycle {n : ℕ} (h3 : 3 ≤ n) (h4 : n ≤ 4)
    (f : Copy (cycleGraph n) PetersenGraph) : False := by
  rcases (by omega : n = 3 ∨ n = 4) with rfl | rfl
  · exact no_triangle (f.toHom 0) (f.toHom 1) (f.toHom 2)
      (f.toHom.map_adj (show (cycleGraph 3).Adj 0 1 by decide))
      (f.toHom.map_adj (show (cycleGraph 3).Adj 1 2 by decide))
      (f.toHom.map_adj (show (cycleGraph 3).Adj 2 0 by decide))
  · exact no_square (f.toHom 0) (f.toHom 1) (f.toHom 2) (f.toHom 3)
      (fun h => absurd (f.injective h) (by decide))
      (fun h => absurd (f.injective h) (by decide))
      (f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide))
      (f.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide))
      (f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide))
      (f.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide))

def v01 : PetersenVertex := ⟨{0, 1}, by decide⟩
def v23 : PetersenVertex := ⟨{2, 3}, by decide⟩
def v04 : PetersenVertex := ⟨{0, 4}, by decide⟩
def v12 : PetersenVertex := ⟨{1, 2}, by decide⟩
def v34 : PetersenVertex := ⟨{3, 4}, by decide⟩

theorem petersen_girth : PetersenGraph.girth = 5 := by
  have hcyc : (Walk.cons (show PetersenGraph.Adj v01 v23 by decide)
      (Walk.cons (show PetersenGraph.Adj v23 v04 by decide)
      (Walk.cons (show PetersenGraph.Adj v04 v12 by decide)
      (Walk.cons (show PetersenGraph.Adj v12 v34 by decide)
      (Walk.cons (show PetersenGraph.Adj v34 v01 by decide) Walk.nil))))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  have hup : PetersenGraph.egirth ≤ 5 := by
    simpa using egirth_le_length hcyc
  have hlow : 5 ≤ PetersenGraph.egirth := by
    rw [le_egirth]
    intro a w hw
    by_contra hlt
    have hlt' : w.length < 5 := by
      have : (w.length : ℕ∞) < 5 := lt_of_not_ge hlt
      exact_mod_cast this
    have h3 := hw.three_le_length
    obtain ⟨f⟩ := (cycleGraph_isContained_iff (G := PetersenGraph) (n := w.length) (by omega)).mpr
      ⟨a, w, hw, rfl⟩
    exact no_short_cycle h3 (by omega) f
  have : PetersenGraph.egirth = 5 := le_antisymm hup hlow
  simp [girth, this]

end WrittenOnTheWallII.Test

#print axioms WrittenOnTheWallII.Test.petersen_girth
