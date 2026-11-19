import Mathlib.Data.List.Infix
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.Fin

namespace Erdos231

/-- Restated from ErdosProblems/231.lean. -/
def ContainsAbelianSquare {α : Type*} (S : List α) : Prop :=
  ∃ x y : List α, x ≠ [] ∧ x.Perm y ∧ x ++ y <:+: S

/-- Copied verbatim from ErdosProblems/231.lean (category API, proved upstream). -/
theorem containsAbelianSquare_iff {α : Type*} (S : List α) :
    ContainsAbelianSquare S ↔ ∃ i < S.length, ∃ L < S.length, 0 < L ∧ i + 2 * L ≤ S.length ∧
      ((S.drop i).take L).Perm ((S.drop (i + L)).take L) := by
  constructor
  · rintro ⟨x, y, hx, hxy, s, t, hS⟩
    have hlen : x.length = y.length := hxy.length_eq
    have hxpos : 0 < x.length := List.length_pos_of_ne_nil hx
    refine ⟨s.length, ?_, x.length, ?_, hxpos, ?_, ?_⟩
    · rw [← hS]; simp; omega
    · rw [← hS]; simp; omega
    · rw [← hS]; simp; omega
    · have h1 : (S.drop s.length).take x.length = x := by
        rw [← hS, List.append_assoc, List.drop_left, List.append_assoc, List.take_left]
      have h2 : (S.drop (s.length + x.length)).take x.length = y := by
        rw [← hS, ← List.length_append, show s ++ (x ++ y) ++ t = (s ++ x) ++ (y ++ t) by
          simp only [List.append_assoc], List.drop_left, List.take_left' hlen.symm]
      rw [h1, h2]
      exact hxy
  · rintro ⟨i, -, L, -, hL, hle, hperm⟩
    refine ⟨(S.drop i).take L, (S.drop (i + L)).take L, ?_, hperm, ?_⟩
    · intro h
      have := congrArg List.length h
      simp only [List.length_take, List.length_drop, List.length_nil] at this
      omega
    · have : (S.drop i).take L ++ (S.drop (i + L)).take L = (S.drop i).take (L + L) := by
        rw [List.take_add, List.drop_drop]
      rw [this]
      exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

instance {α : Type*} [DecidableEq α] (S : List α) : Decidable (ContainsAbelianSquare S) :=
  decidable_of_iff _ (containsAbelianSquare_iff S).symm

lemma no_sq_010 : ¬ ContainsAbelianSquare ([0, 1, 0] : List (Fin 2)) := by
  decide +kernel

theorem erdos_231 :
    ¬ ∀ k : ℕ, 2 ≤ k → ∀ S : List (Fin k), S.length = 2 ^ k - 1 → ContainsAbelianSquare S := by
  intro h
  exact no_sq_010 (h 2 le_rfl _ rfl)

end Erdos231

#print axioms Erdos231.erdos_231
