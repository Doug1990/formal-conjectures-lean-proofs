import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Erdos317
open Finset
open Filter

lemma claim2_inequality : ∀ᶠ n in atTop,
    ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs ≥ 1 / (Icc 1 n).lcm id := by
  refine Filter.Eventually.of_forall ?_
  intro n δ hδ hne
  set L := (Icc 1 n).lcm id with hL
  have hLpos : 0 < L := by
    apply Nat.pos_of_ne_zero
    rw [hL, Ne, Finset.lcm_eq_zero_iff]
    simp
  have hLq : (0 : ℚ) < L := by exact_mod_cast hLpos
  have hterm : ∀ k : Fin n, ∃ z : ℤ, (L : ℚ) * ((δ k : ℚ) / (k + 1)) = z := by
    intro k
    have hmem : (k : ℕ) + 1 ∈ Icc 1 n := by
      rw [Finset.mem_Icc]; have := k.isLt; omega
    obtain ⟨m, hm⟩ : (k : ℕ) + 1 ∣ L := Finset.dvd_lcm (f := id) hmem
    have hk0 : ((k : ℕ) : ℚ) + 1 ≠ 0 := by
      have : (0 : ℚ) ≤ (k : ℕ) := Nat.cast_nonneg _
      exact ne_of_gt (by linarith)
    have key : (L : ℚ) * ((δ k : ℚ) / (k + 1)) = δ k * m := by
      rw [hm]; push_cast; field_simp
    have hd : δ k ∈ ({-1, 0, 1} : Set ℚ) := hδ ⟨k, Set.mem_univ _, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℤ, δ k = e := by
      rcases hd with h | h | h
      · exact ⟨-1, by rw [h]; simp⟩
      · exact ⟨0, by rw [h]; simp⟩
      · exact ⟨1, by rw [h]; simp⟩
    exact ⟨e * m, by rw [key, he]; push_cast; ring⟩
  choose z hz using hterm
  have hsum : (L : ℚ) * ∑ k, (δ k : ℚ) / (k + 1) = ((∑ k, z k : ℤ) : ℚ) := by
    rw [Finset.mul_sum]; push_cast
    exact Finset.sum_congr rfl (fun k _ => hz k)
  set S := ∑ k, (δ k : ℚ) / (k + 1) with hS
  have hS0 : S ≠ 0 := fun h => hne (by rw [h, abs_zero])
  have hz0 : (∑ k, z k) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hsum
    rcases mul_eq_zero.1 hsum with h1 | h1
    · exact (ne_of_gt hLq) h1
    · exact hS0 h1
  have h1 : (1 : ℚ) ≤ |((∑ k, z k : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
  rw [ge_iff_le, div_le_iff₀ hLq]
  calc (1 : ℚ) ≤ |((∑ k, z k : ℤ) : ℚ)| := h1
    _ = |(L : ℚ) * S| := by rw [hsum]
    _ = |S| * L := by rw [abs_mul, abs_of_pos hLq, mul_comm]

end Erdos317

#print axioms Erdos317.claim2_inequality
