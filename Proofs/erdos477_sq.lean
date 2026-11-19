import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open Polynomial Set

namespace Erdos477

theorem erdos_477.variants.S_sq :
    letI f := X ^ 2
    ∀ A : Set ℤ, ∃ z, ¬ ∃! a ∈ A ×ˢ (Set.range f.eval), z = a.1 + a.2 := by
  intro A
  by_contra h
  have h' : ∀ z, ∃! a ∈ A ×ˢ (Set.range (X ^ 2 : ℤ[X]).eval), z = a.1 + a.2 := fun z => by
    by_contra hz; exact h ⟨z, hz⟩
  have hr : ∀ j : ℤ, j ^ 2 ∈ Set.range (X ^ 2 : ℤ[X]).eval := fun j =>
    ⟨j, by show eval j (X ^ 2 : ℤ[X]) = j ^ 2; rw [eval_pow, eval_X]⟩
  have key : ∀ a ∈ A, ∀ a' ∈ A, ∀ k k' : ℤ, a + k ^ 2 = a' + k' ^ 2 → a = a' := by
    intro a ha a' ha' k k' e
    have := (h' (a + k ^ 2)).unique ⟨Set.mk_mem_prod ha (hr k), rfl⟩
      ⟨Set.mk_mem_prod ha' (hr k'), e⟩
    exact congrArg Prod.fst this
  have mod4 : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → (a - a') % 4 = 2 := by
    intro a ha a' ha' hne
    by_contra hm
    rcases (by omega : (a - a') % 2 = 1 ∨ (a - a') % 4 = 0) with h1 | h1
    · obtain ⟨k, hk⟩ : ∃ k, a - a' = 2 * k + 1 := ⟨(a - a') / 2, by omega⟩
      exact hne (key a ha a' ha' k (k + 1) (by linear_combination hk))
    · obtain ⟨k, hk⟩ : ∃ k, a - a' = 4 * k := ⟨(a - a') / 4, by omega⟩
      exact hne (key a ha a' ha' (k - 1) (k + 1) (by linear_combination hk))
  have lower : ∀ z, ∃ a ∈ A, a ≤ z := by
    intro z
    obtain ⟨x, ⟨hx, hz⟩, -⟩ := h' z
    obtain ⟨j, hj⟩ := hx.2
    change eval j (X ^ 2 : ℤ[X]) = x.2 at hj
    rw [eval_pow, eval_X] at hj
    refine ⟨x.1, hx.1, ?_⟩
    nlinarith [sq_nonneg j]
  obtain ⟨a0, ha0, -⟩ := lower 0
  obtain ⟨a1, ha1, h1⟩ := lower (a0 - 1)
  obtain ⟨a2, ha2, h2⟩ := lower (a1 - 1)
  have e1 := mod4 a1 ha1 a0 ha0 (by omega)
  have e2 := mod4 a2 ha2 a0 ha0 (by omega)
  have e3 := mod4 a2 ha2 a1 ha1 (by omega)
  omega

end Erdos477

#print axioms Erdos477.erdos_477.variants.S_sq
