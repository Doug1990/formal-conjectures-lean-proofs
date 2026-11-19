import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped Nat

namespace Erdos1063

/-- Partial fractions: `∑ (-1)^i C(m,i)/(y+i) = m!/∏ (y+i)`. -/
lemma pf : ∀ (m : ℕ) (y : ℚ), (∀ i ≤ m, y + i ≠ 0) →
    ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) / (y + i) =
      (m ! : ℚ) / ∏ i ∈ range (m + 1), (y + i)
  | 0, y, h => by simp
  | m + 1, y, h => by
    have h0 : ∀ i ≤ m, y + i ≠ 0 := fun i hi => h i (by omega)
    have h1 : ∀ i ≤ m, (y + 1) + i ≠ 0 := fun i hi => by
      have := h (i + 1) (by omega)
      push_cast at this
      rwa [show y + 1 + (i : ℚ) = y + ((i : ℚ) + 1) by ring]
    have ih0 := pf m y h0
    have ih1 := pf m (y + 1) h1
    have L : ∑ i ∈ range (m + 1 + 1), (-1 : ℚ) ^ i * ((m + 1).choose i : ℚ) / (y + i) =
        ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) / (y + i) -
        ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) / ((y + 1) + i) := by
      have hA := Finset.sum_range_succ'
        (fun i => (-1 : ℚ) ^ i * (m.choose i : ℚ) / (y + i)) (m + 1)
      have hA2 := Finset.sum_range_succ
        (fun i => (-1 : ℚ) ^ i * (m.choose i : ℚ) / (y + i)) (m + 1)
      rw [Finset.sum_range_succ']
      have e : ∀ i ∈ range (m + 1),
          (-1 : ℚ) ^ (i + 1) * ((m + 1).choose (i + 1) : ℚ) / (y + ((i + 1 : ℕ) : ℚ)) =
          (-1 : ℚ) ^ (i + 1) * (m.choose (i + 1) : ℚ) / (y + ((i + 1 : ℕ) : ℚ)) -
          (-1 : ℚ) ^ i * (m.choose i : ℚ) / ((y + 1) + i) := by
        intro i _
        rw [Nat.choose_succ_succ', Nat.cast_add]
        rw [show y + ((i + 1 : ℕ) : ℚ) = (y + 1) + i by push_cast; ring]
        ring
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib]
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_div, add_zero] at hA2
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero,
        one_mul] at hA ⊢
      linarith
    have hP0 : ∏ i ∈ range (m + 1), (y + i) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => h0 i (by simp at hi; omega)
    have hP1 : ∏ i ∈ range (m + 1), ((y + 1) + i) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => h1 i (by simp at hi; omega)
    have R1 : ∏ i ∈ range (m + 1 + 1), (y + i) =
        (∏ i ∈ range (m + 1), (y + i)) * (y + ((m + 1 : ℕ) : ℚ)) := Finset.prod_range_succ _ _
    have R2 : ∏ i ∈ range (m + 1 + 1), (y + i) =
        (∏ i ∈ range (m + 1), ((y + 1) + i)) * y := by
      rw [Finset.prod_range_succ']
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
      · simp
    have hym : y + ((m + 1 : ℕ) : ℚ) ≠ 0 := h (m + 1) le_rfl
    have R3 : (∏ i ∈ range (m + 1), (y + i)) * (y + ((m + 1 : ℕ) : ℚ)) =
        (∏ i ∈ range (m + 1), ((y + 1) + i)) * y := by rw [← R1, R2]
    rw [L, ih0, ih1, R1]
    generalize ∏ i ∈ range (m + 1), (y + i) = P at *
    generalize ∏ i ∈ range (m + 1), ((y + 1) + i) = Q at *
    rw [div_sub_div _ _ hP0 hP1, div_eq_div_iff (mul_ne_zero hP0 hP1) (mul_ne_zero hP0 hym)]
    push_cast [Nat.factorial_succ] at R3 ⊢
    linear_combination (-(m ! : ℚ) * P) * R3

theorem erdos_1063.variants.exists_exception {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  by_contra hcon
  have hd : ∀ i < k, (n - i) ∣ n.choose k := fun i hi => by
    by_contra hh
    exact hcon ⟨i, hi, hh⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, n - m = a := ⟨_, rfl⟩
  have hdiv : ∀ j, ∃ q : ℕ, j < m + 1 → n.choose (m + 1) = (a + j) * q := by
    intro j
    by_cases hj : j < m + 1
    · obtain ⟨q, hq⟩ := hd (m - j) (by omega)
      refine ⟨q, fun _ => ?_⟩
      rw [hq, show n - (m - j) = a + j by omega]
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose q hq using hdiv
  have hy : ∀ i ≤ m, (a : ℚ) + i ≠ 0 := by
    intro i _
    have : ((a + i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show a + i ≠ 0 by omega)
    push_cast at this
    exact this
  have key := pf m a hy
  have hC : 0 < n.choose (m + 1) := Nat.choose_pos (by omega)
  have hC' : (n.choose (m + 1) : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hf : (m ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have e1 : ∏ i ∈ range (m + 1), (a + i) = n.descFactorial (m + 1) := by
    have r := Finset.prod_range_reflect (fun i => n - i) (m + 1)
    rw [Nat.descFactorial_eq_prod_range, ← r]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  have hP : ∏ i ∈ range (m + 1), ((a : ℚ) + i) = ((m + 1)! : ℚ) * (n.choose (m + 1) : ℚ) := by
    have : ((∏ i ∈ range (m + 1), (a + i) : ℕ) : ℚ) =
        (((m + 1)! * n.choose (m + 1) : ℕ) : ℚ) := by
      rw [e1, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast at this
    exact this
  have hS1 : (n.choose (m + 1) : ℚ) *
      ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) / ((a : ℚ) + i) = 1 / ((m : ℚ) + 1) := by
    rw [key, hP]
    push_cast [Nat.factorial_succ]
    field_simp
  have hS2 : (n.choose (m + 1) : ℚ) *
      ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) / ((a : ℚ) + i) =
      ((∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * (q i : ℤ) : ℤ) : ℚ) := by
    rw [Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.1 hi
    have hqi : (n.choose (m + 1) : ℚ) = ((a : ℚ) + i) * (q i : ℚ) := by exact_mod_cast hq i hi'
    have hai := hy i (by omega)
    rw [hqi]
    field_simp
  have hz : ((∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * (q i : ℤ) : ℤ) : ℚ) *
      ((m : ℚ) + 1) = 1 := by
    rw [← hS2, hS1]
    field_simp
  generalize (∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * (q i : ℤ)) = z at hz
  have hz' : z * ((m : ℤ) + 1) = 1 := by exact_mod_cast hz
  have hdvd : ((m : ℤ) + 1) ∣ 1 := Dvd.intro_left z hz'
  have := Int.le_of_dvd one_pos hdvd
  omega

end Erdos1063

#print axioms Erdos1063.erdos_1063.variants.exists_exception
