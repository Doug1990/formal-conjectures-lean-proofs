import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

open Finset

namespace Erdos1033

namespace TH

/-- K_{14,9} on {0..13} ∪ {14..22} plus the perfect matching {2i, 2i+1} inside {0..13}. -/
def adj (x y : Fin 23) : Prop :=
  (x.val < 14 ∧ 14 ≤ y.val) ∨ (14 ≤ x.val ∧ y.val < 14) ∨
    (x.val < 14 ∧ y.val < 14 ∧ x.val / 2 = y.val / 2 ∧ x.val ≠ y.val)

instance (x y : Fin 23) : Decidable (adj x y) := by unfold adj; infer_instance

def G : SimpleGraph (Fin 23) where
  Adj := adj
  symm := ⟨fun x y h => by unfold adj at *; omega⟩
  loopless := ⟨fun x h => by unfold adj at h; omega⟩

instance : DecidableRel G.Adj := fun x y => (inferInstance : Decidable (adj x y))

lemma deg (v : Fin 23) : G.degree v = if v.val < 14 then 10 else 14 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  revert v
  decide

lemma edges : 2 * #G.edgeFinset = 266 := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [deg]
  decide

end TH

theorem erdos_1033.variants.three_halves :
    ¬ ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], n ^ 2 < 4 * #G.edgeFinset →
      ∃ t, G.IsNClique 3 t ∧ 3 * n ≤ 2 * ∑ v ∈ t, G.degree v := by
  intro h
  obtain ⟨t, ht, hsum⟩ := h 23 TH.G (by have := TH.edges; omega)
  obtain ⟨a, b, c, h1, h2, h3, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hab : a ≠ b := TH.G.ne_of_adj h1
  have hac : a ≠ c := TH.G.ne_of_adj h2
  have hbc : b ≠ c := TH.G.ne_of_adj h3
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hsum
  rw [TH.deg, TH.deg, TH.deg] at hsum
  change TH.adj a b at h1
  change TH.adj a c at h2
  change TH.adj b c at h3
  unfold TH.adj at h1 h2 h3
  split_ifs at hsum <;> omega

end Erdos1033

#print axioms Erdos1033.erdos_1033.variants.three_halves
