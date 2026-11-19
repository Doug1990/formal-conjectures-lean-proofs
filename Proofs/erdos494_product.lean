import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos494

noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

namespace PM

def e : ℤ ↪ ℂ := ⟨(Int.cast : ℤ → ℂ), Int.cast_injective⟩

lemma prod_cast (S : Finset ℤ) (k : ℕ) :
    prodMultiset (S.map e) k =
      ((S.powersetCard k).val.map (fun t => t.prod id)).map (Int.cast : ℤ → ℂ) := by
  unfold prodMultiset
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map, Multiset.map_map]
  congr 1
  funext t
  simp [Finset.prod_map, e]

end PM

theorem erdos_494.variants.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  refine ⟨({0, 1, 2, 3} : Finset ℤ).map PM.e, ({0, -1, -2, 3} : Finset ℤ).map PM.e, ?_, ?_, ?_⟩
  · simp only [Finset.card_map]
    decide
  · rw [PM.prod_cast, PM.prod_cast]
    congr 1
  · intro h
    have := Finset.map_injective PM.e h
    revert this
    decide

end Erdos494

#print axioms Erdos494.erdos_494.variants.product
