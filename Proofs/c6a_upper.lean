import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

namespace Constant6a

noncomputable def C6a : ℝ :=
  sSup {c : ℝ | ∀ (A : Finset (Finset ℕ)), A ≠ {∅} →
    (∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A) → ∃ i, c * #A ≤ #{x ∈ A | i ∈ x}}

theorem c6a_upper_bound : C6a ≤ 1 / 2 := by
  unfold C6a
  apply csSup_le
  · exact ⟨0, fun A _ _ => ⟨0, by simp⟩⟩
  · intro c hc
    have hne : ({∅, {0}} : Finset (Finset ℕ)) ≠ {∅} := by decide
    have huc : ∀ᵉ (X ∈ ({∅, {0}} : Finset (Finset ℕ))) (Y ∈ ({∅, {0}} : Finset (Finset ℕ))),
        X ∪ Y ∈ ({∅, {0}} : Finset (Finset ℕ)) := by decide
    obtain ⟨i, hi⟩ := hc {∅, {0}} hne huc
    have h2 : #({∅, {0}} : Finset (Finset ℕ)) = 2 := Finset.card_pair (by decide)
    have h1 : #({x ∈ ({∅, {0}} : Finset (Finset ℕ)) | i ∈ x}) ≤ 1 := by
      calc #({x ∈ ({∅, {0}} : Finset (Finset ℕ)) | i ∈ x})
          ≤ #({{0}} : Finset (Finset ℕ)) := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with ⟨rfl | rfl, h⟩
            · simp at h
            · exact Finset.mem_singleton_self _
        _ = 1 := Finset.card_singleton _
    rw [h2] at hi
    have h1' : ((#({x ∈ ({∅, {0}} : Finset (Finset ℕ)) | i ∈ x}) : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast h1
    push_cast at hi
    linarith

end Constant6a

#print axioms Constant6a.c6a_upper_bound
