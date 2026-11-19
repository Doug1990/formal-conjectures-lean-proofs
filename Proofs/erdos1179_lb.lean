import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
noncomputable def repCount (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S ↦ ∑ x ∈ S, x = g).card

def IsBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(repCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

theorem erdos_1179.variants.lower_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ A : Finset G, IsBalanced ε A → Fintype.card G ≤ 2 ^ A.card := by
  classical
  intro ε _ hε1 A hA
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have hx : (0 : ℝ) < 2 ^ A.card / Fintype.card G := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast hG
    positivity
  have hsub : (univ : Finset G) ⊆ A.powerset.image (fun S => ∑ x ∈ S, x) := by
    intro g _
    have hg := hA g
    have hne : repCount A g ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hx] at hg
      nlinarith
    obtain ⟨S, hS⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    simp only [Finset.mem_filter] at hS
    rw [Finset.mem_image]
    refine ⟨S, ?_, ?_⟩
    · convert hS.1
    · convert hS.2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := A.powerset) (f := fun S => ∑ x ∈ S, x)
  rw [Finset.card_powerset] at h2
  rw [Finset.card_univ] at h1
  omega

end Erdos1179

#print axioms Erdos1179.erdos_1179.variants.lower_bound
