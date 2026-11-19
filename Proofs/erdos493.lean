import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace Erdos493

theorem erdos_493 :
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  refine ⟨2, 0, fun n hn => ⟨![2, n + 2], ?_, ?_⟩⟩
  · rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> omega
  · simp [Fin.prod_univ_two, Fin.sum_univ_two]
    ring

end Erdos493

#print axioms Erdos493.erdos_493
