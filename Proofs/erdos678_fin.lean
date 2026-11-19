import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter Finset

/-- Restated from FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean. -/
def lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

namespace Erdos678

namespace LF

lemma Ioc_succ (m j : ℕ) :
    Finset.Ioc m (m + (j + 1)) = insert (m + (j + 1)) (Finset.Ioc m (m + j)) := by
  ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega

lemma L_succ (m j : ℕ) :
    lcmInterval m (j + 1) = Nat.lcm (m + (j + 1)) (lcmInterval m j) := by
  unfold lcmInterval
  rw [Ioc_succ, Finset.lcm_insert]
  rfl

lemma L_dvd_P (m j : ℕ) : lcmInterval m j ∣ ∏ i ∈ Finset.Ioc m (m + j), i :=
  Finset.lcm_dvd (fun _ hi => Finset.dvd_prod_of_mem _ hi)

lemma P_pos (m j : ℕ) : 0 < ∏ i ∈ Finset.Ioc m (m + j), i :=
  Finset.prod_pos (fun i hi => by simp only [Finset.mem_Ioc] at hi; omega)

lemma gcd_prod_dvd (s : Finset ℕ) (x : ℕ) :
    Nat.gcd (∏ i ∈ s, i) x ∣ ∏ i ∈ s, Nat.gcd i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.gcd_comm]
    refine dvd_trans (gcd_mul_dvd_mul_gcd x a _) ?_
    show Nat.gcd x a * Nat.gcd x (∏ i ∈ s, i) ∣ _
    rw [Nat.gcd_comm x a, Nat.gcd_comm x]
    exact mul_dvd_mul_left _ ih

lemma gcd_le (m j : ℕ) : Nat.gcd (lcmInterval m j) (m + (j + 1)) ≤ j ^ j := by
  have h1 : Nat.gcd (lcmInterval m j) (m + (j + 1)) ∣
      ∏ i ∈ Finset.Ioc m (m + j), Nat.gcd i (m + (j + 1)) :=
    dvd_trans (Nat.gcd_dvd_gcd_of_dvd_left _ (L_dvd_P m j)) (gcd_prod_dvd _ _)
  have h2 : ∏ i ∈ Finset.Ioc m (m + j), Nat.gcd i (m + (j + 1)) ≤ j ^ j := by
    have := Finset.prod_le_pow_card (Finset.Ioc m (m + j)) (fun i => Nat.gcd i (m + (j + 1))) j
      (by
        intro i hi
        simp only [Finset.mem_Ioc] at hi
        have hd : Nat.gcd i (m + (j + 1)) ∣ m + (j + 1) - i :=
          Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
        have := Nat.le_of_dvd (by omega) hd
        omega)
    simpa [Nat.card_Ioc] using this
  have hpos : 0 < ∏ i ∈ Finset.Ioc m (m + j), Nat.gcd i (m + (j + 1)) :=
    Finset.prod_pos (fun i hi => Nat.gcd_pos_of_pos_right _ (by omega))
  exact le_trans (Nat.le_of_dvd hpos h1) h2

/-- The constant `c j = ∏_{i<j} i^i`. -/
def c (j : ℕ) : ℕ := ∏ i ∈ Finset.range j, i ^ i

lemma c_pos (j : ℕ) : 0 < c j :=
  Finset.prod_pos (fun i _ => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · exact pow_pos h i)

/-- LOWER BOUND FOR THE LCM OF CONSECUTIVE INTEGERS: `(m+1)^j ≤ c j · lcm(m+1..m+j)`. -/
lemma lower (m j : ℕ) : (m + 1) ^ j ≤ lcmInterval m j * c j := by
  induction j with
  | zero => simp [lcmInterval, c]
  | succ j ih =>
    have hg := gcd_le m j
    have hl : Nat.gcd (m + (j + 1)) (lcmInterval m j) * lcmInterval m (j + 1) =
        (m + (j + 1)) * lcmInterval m j := by
      rw [L_succ]; exact Nat.gcd_mul_lcm _ _
    rw [Nat.gcd_comm] at hl
    have hc : c (j + 1) = c j * j ^ j := Finset.prod_range_succ _ _
    rw [hc, pow_succ]
    have h3 : (m + 1) * lcmInterval m j ≤ lcmInterval m (j + 1) * j ^ j := by
      have : (m + 1) * lcmInterval m j ≤ (m + (j + 1)) * lcmInterval m j :=
        Nat.mul_le_mul_right _ (by omega)
      have : Nat.gcd (lcmInterval m j) (m + (j + 1)) * lcmInterval m (j + 1) ≤
          j ^ j * lcmInterval m (j + 1) := Nat.mul_le_mul_right _ hg
      nlinarith
    calc (m + 1) ^ j * (m + 1) ≤ lcmInterval m j * c j * (m + 1) := Nat.mul_le_mul_right _ ih
      _ = ((m + 1) * lcmInterval m j) * c j := by ring
      _ ≤ (lcmInterval m (j + 1) * j ^ j) * c j := Nat.mul_le_mul_right _ h3
      _ = lcmInterval m (j + 1) * (c j * j ^ j) := by ring

lemma upper (n k : ℕ) : lcmInterval n k ≤ (n + k) ^ k := by
  have h1 := Nat.le_of_dvd (P_pos n k) (L_dvd_P n k)
  have h2 := Finset.prod_le_pow_card (Finset.Ioc n (n + k)) (fun i => i) (n + k)
    (fun i hi => by simp only [Finset.mem_Ioc] at hi; omega)
  simp only [Nat.card_Ioc, Nat.add_sub_cancel_left] at h2
  exact le_trans h1 h2

lemma finite (k : ℕ) :
    {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Finite := by
  refine (((Finset.range (c (k + 1))) ×ˢ (Finset.range (c (k + 1))) :
    Finset (ℕ × ℕ)).finite_toSet).subset ?_
  rintro ⟨m, n⟩ ⟨h1, h2⟩
  have hc := c_pos (k + 1)
  have hlow := lower m (k + 1)
  have hup : lcmInterval n k ≤ m ^ k :=
    le_trans (upper n k) (Nat.pow_le_pow_left h1 k)
  have h3 : lcmInterval m (k + 1) * c (k + 1) < lcmInterval n k * c (k + 1) :=
    Nat.mul_lt_mul_of_pos_right h2 hc
  have h4 : (m + 1) * m ^ k ≤ (m + 1) ^ (k + 1) := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ m) k)
  have h5 : lcmInterval n k * c (k + 1) ≤ m ^ k * c (k + 1) := Nat.mul_le_mul_right _ hup
  have h6 : (m + 1) * m ^ k < c (k + 1) * m ^ k := by
    rw [mul_comm (c (k + 1))]; omega
  have h7 : m + 1 < c (k + 1) := Nat.lt_of_mul_lt_mul_right h6
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨show m < c (k + 1) by omega, show n < c (k + 1) by omega⟩

end LF

theorem erdos_678.variants.not_infinitely_many_pairs :
    ¬ ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite := by
  intro h
  obtain ⟨k, hk⟩ := h.exists
  exact hk (LF.finite k)

end Erdos678

#print axioms Erdos678.erdos_678.variants.not_infinitely_many_pairs
