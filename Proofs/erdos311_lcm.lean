import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

namespace Erdos311

open Finset

noncomputable def delta (N : ℕ) : ℝ :=
  sInf {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

theorem delta_ge_inv_lcm (N : ℕ) : 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N := by
  set L := (Icc 1 N).lcm id with hL
  have hLpos : 0 < L := Nat.pos_of_ne_zero (by
    rw [hL, Ne, Finset.lcm_eq_zero_iff]
    simp)
  have key : ∀ A ⊆ Icc 1 N, ∃ m : ℤ, (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = m := by
    intro A hA
    refine ⟨(L : ℤ) - ∑ n ∈ A, ((L / n : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_sum, Int.cast_natCast, mul_sub, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' := Finset.mem_Icc.1 (hA hn)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hdvd : n ∣ L := Finset.dvd_lcm (hA hn)
    rw [Int.cast_natCast, Nat.cast_div hdvd hn0, mul_one_div]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  unfold delta
  apply le_csInf
  · exact ⟨1, one_ne_zero, ∅, Finset.empty_subset _, by simp⟩
  · rintro x ⟨hx, A, hA, rfl⟩
    obtain ⟨m, hm⟩ := key A hA
    have h1 : |1 - ∑ n ∈ A, (1 : ℝ) / n| = |(m : ℝ)| / L := by
      rw [← hm, abs_mul, abs_of_pos hLr]
      exact (mul_div_cancel_left₀ _ hLr.ne').symm
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hx
      rw [h1]
      simp
    have h2 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    rw [h1]
    gcongr

end Erdos311

#print axioms Erdos311.delta_ge_inv_lcm
