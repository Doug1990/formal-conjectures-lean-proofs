import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Lattice.Nat

open Filter Asymptotics

namespace Erdos1028

def imbalance (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|

noncomputable def H (n : ℕ) : ℕ :=
  sInf {m | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)}

namespace UB

/-- one factor of the Sylvester–Hadamard sign -/
def s (a b : Bool) : ℤ := if (a && b) then -1 else 1

def h {k : ℕ} (u v : Fin k → Bool) : ℤ := ∏ i, s (u i) (v i)

lemma s_pair (a a' : Bool) : ∑ b : Bool, s a b * s a' b = if a = a' then 2 else 0 := by
  rw [Fintype.sum_bool]
  cases a <;> cases a' <;> simp [s]

lemma s_sq (a b : Bool) : s a b * s a b = 1 := by
  cases a <;> cases b <;> simp [s]

lemma s_comm (a b : Bool) : s a b = s b a := by
  cases a <;> cases b <;> rfl

lemma h_comm {k : ℕ} (u v : Fin k → Bool) : h u v = h v u := by
  unfold h; exact Finset.prod_congr rfl (fun i _ => s_comm _ _)

lemma h_sq {k : ℕ} (u v : Fin k → Bool) : h u v * h u v = 1 := by
  unfold h
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => s_sq _ _)

lemma h_pm {k : ℕ} (u v : Fin k → Bool) : h u v = 1 ∨ h u v = -1 :=
  mul_self_eq_one_iff.mp (h_sq u v)

/-- orthogonality of the rows -/
lemma orth {k : ℕ} (u u' : Fin k → Bool) :
    ∑ v : Fin k → Bool, h u v * h u' v = if u = u' then 2 ^ k else 0 := by
  have e1 : ∀ v : Fin k → Bool, h u v * h u' v = ∏ i, (s (u i) (v i) * s (u' i) (v i)) := by
    intro v; unfold h; rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun v _ => e1 v)]
  rw [← Fintype.prod_sum (fun i b => s (u i) b * s (u' i) b)]
  simp only [s_pair]
  split_ifs with hu
  · subst hu
    simp
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ u' i := by
      by_contra hc
      push Not at hc
      exact hu (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Lindsey's lemma for the Hadamard matrix -/
lemma lindsey {k : ℕ} (X : Finset ℕ) (φ : ℕ → Fin k → Bool) (hφ : Set.InjOn φ X) :
    (∑ x ∈ X, ∑ y ∈ X, h (φ x) (φ y)) ^ 2 ≤ (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) := by
  set R : (Fin k → Bool) → ℤ := fun v => ∑ x ∈ X, h (φ x) v with hR
  have e1 : ∑ x ∈ X, ∑ y ∈ X, h (φ x) (φ y) = ∑ y ∈ X, R (φ y) := by
    rw [Finset.sum_comm]
  rw [e1]
  have cs := sq_sum_le_card_mul_sum_sq (s := X) (f := fun y => R (φ y))
  refine le_trans cs ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e2 : ∑ y ∈ X, R (φ y) ^ 2 = ∑ v ∈ X.image φ, R v ^ 2 := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hφ ha hb hab
  rw [e2]
  have e3 : ∑ v ∈ X.image φ, R v ^ 2 ≤ ∑ v, R v ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun v => sq_nonneg _)
  refine le_trans e3 (le_of_eq ?_)
  have e4 : ∀ v, R v ^ 2 = ∑ x ∈ X, ∑ x' ∈ X, h (φ x) v * h (φ x') v := by
    intro v
    rw [hR, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun v _ => e4 v), Finset.sum_comm]
  have e5 : ∀ x ∈ X, ∑ v, ∑ x' ∈ X, h (φ x) v * h (φ x') v = 2 ^ k := by
    intro x hx
    rw [Finset.sum_comm]
    simp only [orth]
    have : ∀ x' ∈ X, (if φ x = φ x' then (2 : ℤ) ^ k else 0) = if x = x' then 2 ^ k else 0 := by
      intro x' hx'
      by_cases hxx : x = x'
      · subst hxx; simp
      · rw [if_neg hxx, if_neg (fun h' => hxx (hφ hx hx' h'))]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hx]
  rw [Finset.sum_congr rfl e5]
  simp

/-- splitting the full double sum of a symmetric function -/
lemma split (g : ℕ → ℕ → ℤ) (hg : ∀ x y, g x y = g y x) (X : Finset ℕ) :
    ∑ x ∈ X, ∑ y ∈ X, g x y
      = 2 * ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y + ∑ x ∈ X, g x x := by
  have pt : ∀ x y, g x y = (if x < y then g x y else 0) + (if y < x then g x y else 0)
      + (if x = y then g x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · rw [if_pos hxy, if_neg (lt_asymm hxy), if_neg (ne_of_lt hxy)]; ring
    · subst hxy; simp
    · rw [if_neg (lt_asymm hxy), if_pos hxy, if_neg (ne_of_gt hxy)]; ring
  have A : ∑ x ∈ X, ∑ y ∈ X, g x y = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0)
      + ∑ x ∈ X, ∑ y ∈ X, (if y < x then g x y else 0)
      + ∑ x ∈ X, ∑ y ∈ X, (if x = y then g x y else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => pt x y)
  have B : ∑ x ∈ X, ∑ y ∈ X, (if y < x then g x y else 0)
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hg]
  have C : ∑ x ∈ X, ∑ y ∈ X, (if x = y then g x y else 0) = ∑ x ∈ X, g x x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_ite_eq]
    simp [hx]
  have D : ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_filter]
  rw [A, B, C, D]
  ring

def φ (k : ℕ) (x : ℕ) : Fin k → Bool := fun i => x.testBit i

def F (k : ℕ) (x y : ℕ) : ℤ := h (φ k x) (φ k y)

lemma φ_inj (k n : ℕ) (hn : n < 2 ^ k) : Set.InjOn (φ k) (Finset.Icc 1 n : Set ℕ) := by
  intro x hx y hy hxy
  simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun hxy ⟨i, hi⟩
  · have hk : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

lemma imb_bound (k n : ℕ) (hn : n < 2 ^ k) (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 n) :
    imbalance (F k) X ≤ ((Nat.sqrt (n * n * 2 ^ k) + n : ℕ) : ℤ) := by
  have inj : Set.InjOn (φ k) (X : Set ℕ) := (φ_inj k n hn).mono (Finset.coe_subset.mpr hX)
  have hc : (X.card : ℤ) ≤ n := by
    have := Finset.card_le_card hX
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have L : (∑ x ∈ X, ∑ y ∈ X, F k x y) ^ 2 ≤ (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) :=
    lindsey X (φ k) inj
  have Sp := split (F k) (fun x y => h_comm _ _) X
  have hD : |∑ x ∈ X, F k x x| ≤ X.card := by
    calc |∑ x ∈ X, F k x x| ≤ ∑ x ∈ X, |F k x x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ X, (1 : ℤ) := Finset.sum_congr rfl (fun x _ => by
          rcases h_pm (φ k x) (φ k x) with h' | h' <;> simp [F, h'])
      _ = X.card := by simp
  set S := ∑ x ∈ X, ∑ y ∈ X, F k x y with hS
  set D := ∑ x ∈ X, F k x x with hDdef
  set r := Nat.sqrt (n * n * 2 ^ k) with hr
  have hr1 : ((n * n * 2 ^ k : ℕ) : ℤ) < (((r + 1) * (r + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_succ_sqrt (n * n * 2 ^ k)
  push_cast at hr1
  have h0 : (0 : ℤ) ≤ X.card := by positivity
  have hXn : (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) ≤ n * (n * 2 ^ k) := by
    have h2 : (0 : ℤ) < 2 ^ k := by positivity
    have h3 : (X.card : ℤ) * 2 ^ k ≤ n * 2 ^ k := mul_le_mul_of_nonneg_right hc h2.le
    calc (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) ≤ n * ((X.card : ℤ) * 2 ^ k) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ n * (n * 2 ^ k) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hSr : |S| ≤ (r : ℤ) := by
    by_contra hcon
    push Not at hcon
    have hr0 : (0 : ℤ) ≤ (r : ℤ) + 1 := by positivity
    have : ((r : ℤ) + 1) * ((r : ℤ) + 1) ≤ |S| * |S| := mul_self_le_mul_self hr0 (by omega)
    have hsq : |S| * |S| = S ^ 2 := by rw [← sq, sq_abs]
    nlinarith
  unfold imbalance
  push_cast
  have a1 := abs_le.mp hSr
  have a2 := abs_le.mp hD
  have hr0 : (0 : ℤ) ≤ r := by positivity
  rw [abs_le]
  constructor <;> linarith

end UB

theorem erdos_1028.variants.upper_bound :
    (fun n => (H n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop 1] with n hn
  set k := Nat.log 2 n + 1 with hkdef
  have hk1 : n < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk2 : 2 ^ k ≤ 2 * n := by
    have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    rw [hkdef, pow_succ]; omega
  have hH : H n ≤ Nat.sqrt (n * n * 2 ^ k) + n := by
    apply Nat.sInf_le
    exact ⟨UB.F k, fun x y => UB.h_pm _ _, fun X hX => UB.imb_bound k n hk1 X hX⟩
  set r := Nat.sqrt (n * n * 2 ^ k) with hrdef
  have hr : r * r ≤ n * n * (2 * n) :=
    le_trans (Nat.sqrt_le (n * n * 2 ^ k)) (Nat.mul_le_mul_left _ hk2)
  have hrR : (r : ℝ) * r ≤ 2 * (n : ℝ) ^ 3 := by
    have := (by exact_mod_cast hr : ((r * r : ℕ) : ℝ) ≤ ((n * n * (2 * n) : ℕ) : ℝ))
    push_cast at this
    nlinarith
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t := (n : ℝ) ^ (3 / 2 : ℝ) with htdef
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t * t = (n : ℝ) ^ 3 := by
    rw [htdef, ← Real.rpow_add hpos, show (3 / 2 : ℝ) + 3 / 2 = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hnt : (n : ℝ) ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  have hrt : (r : ℝ) ≤ 2 * t := by
    by_contra hc
    push Not at hc
    have : (2 * t) * (2 * t) < r * r := mul_self_lt_mul_self (by positivity) hc
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg ht0]
  have : (H n : ℝ) ≤ r + n := by exact_mod_cast hH
  linarith

end Erdos1028

#print axioms Erdos1028.erdos_1028.variants.upper_bound
