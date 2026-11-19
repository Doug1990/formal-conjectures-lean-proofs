import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter

namespace Green24

noncomputable def max013AffineTranslates (n : ℕ) : ℕ :=
  sSup { k |
    ∃ A : Finset ℤ,
      A.card = n ∧
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
  }

namespace variants

noncomputable def gamma : ℝ :=
  limsup (fun n : ℕ => (max013AffineTranslates n : ℝ) / ((n : ℝ)^2)) atTop

lemma bdd (n : ℕ) : BddAbove { k |
    ∃ A : Finset ℤ,
      A.card = n ∧
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card } := by
  refine ⟨n ^ 2, ?_⟩
  rintro k ⟨A, hA, rfl⟩
  apply le_trans (Finset.card_filter_le _ _)
  rw [Finset.card_product, hA, pow_two]

lemma le_max (n : ℕ) : max013AffineTranslates n ≤ n ^ 2 := by
  apply csSup_le
  · exact ⟨_, ⟨(Finset.range n).image (fun a : ℕ => (a : ℤ)), by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range], rfl⟩⟩
  · rintro k ⟨A, hA, rfl⟩
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_product, hA, pow_two]

lemma key (m : ℕ) : 12 * m ^ 2 ≤ max013AffineTranslates (12 * m) := by
  set A : Finset ℤ := (Finset.range (12 * m)).image (fun a : ℕ => (a : ℤ)) with hAdef
  have hA : A.card = 12 * m := by
    rw [hAdef, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have memA : ∀ a : ℕ, a < 12 * m → (a : ℤ) ∈ A := fun a ha =>
    Finset.mem_image.2 ⟨a, Finset.mem_range.2 ha, rfl⟩
  have hc : 12 * m ^ 2 ≤
      ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card := by
    have hs : ((Finset.range (6 * m)) ×ˢ (Finset.range (2 * m))).card = 12 * m ^ 2 := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range]; ring
    rw [← hs]
    refine Finset.card_le_card_of_injOn
      (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.1 : ℤ) + p.2 + 1)) (fun p hp => ?_) ?_
    · obtain ⟨a, j⟩ := p
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      obtain ⟨ha, hj⟩ := hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨memA a (by omega), ?_⟩, ?_, ?_⟩
      · have := memA (a + j + 1) (by omega)
        push_cast at this
        exact this
      · intro h
        have : ((a : ℤ) + j + 1) = a := h.symm
        omega
      · have := memA (a + 3 * j + 3) (by omega)
        push_cast at this
        convert this using 1
        ring
    · rintro ⟨a, j⟩ _ ⟨b, k⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hab : a = b := by exact_mod_cast h1
      subst hab
      have : (j : ℤ) = k := by linarith
      simp only [Prod.mk.injEq, true_and]
      exact_mod_cast this
  exact le_trans hc (le_csSup (bdd _) ⟨A, hA, rfl⟩)

theorem lower_HL : gamma ≥ 1/12 := by
  unfold gamma
  apply le_limsup_of_frequently_le
  · rw [frequently_atTop]
    intro a
    refine ⟨12 * (a + 1), by omega, ?_⟩
    have hk := key (a + 1)
    have hk' : ((12 * (a + 1) ^ 2 : ℕ) : ℝ) ≤ (max013AffineTranslates (12 * (a + 1)) : ℝ) := by
      exact_mod_cast hk
    have hpos : (0 : ℝ) < ((12 * (a + 1) : ℕ) : ℝ) ^ 2 :=
      pow_pos (by exact_mod_cast (show 0 < 12 * (a + 1) by omega)) 2
    rw [le_div_iff₀ hpos]
    push_cast at hk' ⊢
    nlinarith [hk']
  · refine isBoundedUnder_of ⟨1, fun n => ?_⟩
    have h1 : (max013AffineTranslates n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast le_max n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      rw [div_le_one hpos]
      exact h1

end variants

end Green24

#print axioms Green24.variants.lower_HL
