import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.NormNum.GCD
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace OeisA372761

open scoped Nat

open Rat

def continuedFractionDenominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) - (n : ℚ) / (n + 4 : ℚ)
      else
        let R_next := continuedFractionDenominator n (k + 1)
        if R_next = 0 then 0 else (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (1 / continuedFractionDenominator n 2).den

namespace P

/-- backward continuants: `w n t = u_{n+1-t}` -/
def w (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => (n : ℤ) + 4
  | (t + 2) => ((n : ℤ) - 1 - t) * w n (t + 1) - ((n : ℤ) - t) * w n t

lemma w_succ_succ (n t : ℕ) :
    w n (t + 2) = ((n : ℤ) - 1 - t) * w n (t + 1) - ((n : ℤ) - t) * w n t := rfl

lemma Q (n : ℕ) : ∀ t, t + 2 ≤ n →
    ((n : ℤ) - 1 - t) * w n (t + 1) - (((n : ℤ) - 1 - t) ^ 2 - 1) * w n t = 5 * n - 4 := by
  intro t
  induction t with
  | zero =>
    intro _
    show ((n : ℤ) - 1 - ((0 : ℕ) : ℤ)) * ((n : ℤ) + 4)
      - (((n : ℤ) - 1 - ((0 : ℕ) : ℤ)) ^ 2 - 1) * 1 = 5 * n - 4
    push_cast; ring
  | succ t ih =>
    intro ht
    have h := ih (by omega)
    rw [show w n (t + 1 + 1) = _ from w_succ_succ n t]
    push_cast
    linear_combination h

lemma pos (n : ℕ) : ∀ t, t + 1 ≤ n → 0 < w n t := by
  intro t
  induction t with
  | zero => intro _; show (0 : ℤ) < 1; norm_num
  | succ t ih =>
    intro ht
    have h0 := ih (by omega)
    have hq := Q n t (by omega)
    have hK : (1 : ℤ) ≤ (n : ℤ) - 1 - t := by omega
    have hm : (0 : ℤ) < 5 * n - 4 := by omega
    have hK2 : (0 : ℤ) ≤ ((n : ℤ) - 1 - t) ^ 2 - 1 := by nlinarith
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonneg hK2 h0.le,
      mul_nonneg (by linarith : (0 : ℤ) ≤ (n : ℤ) - 1 - t) (by linarith : (0 : ℤ) ≤ -w n (t + 1))]

lemma cf (n : ℕ) (hn : 3 ≤ n) : ∀ t, t + 3 ≤ n →
    continuedFractionDenominator n (n - 1 - t) = (w n (t + 2) : ℚ) / w n (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [continuedFractionDenominator, if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show w n (0 + 2) = ((n : ℤ) - 1 - ((0 : ℕ) : ℤ)) * ((n : ℤ) + 4)
      - ((n : ℤ) - ((0 : ℕ) : ℤ)) * 1 from rfl, show w n (0 + 1) = (n : ℤ) + 4 from rfl]
    have hc : ((n - 1 - 0 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      have h : n - 1 - 0 + 1 = n := by omega
      have := congrArg (Nat.cast (R := ℚ)) h
      push_cast at this
      linarith
    rw [hc]
    push_cast
    have h4 : (n : ℚ) + 4 ≠ 0 := by
      have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      intro h; linarith
    field_simp
    try ring
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hp1 : (0 : ℚ) < w n (t + 1) := by exact_mod_cast pos n (t + 1) (by omega)
    have hp2 : (0 : ℚ) < w n (t + 2) := by exact_mod_cast pos n (t + 2) (by omega)
    have hp1' := hp1.ne'
    have hp2' := hp2.ne'
    rw [continuedFractionDenominator, if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    dsimp only
    have e : n - 1 - (t + 1) + 1 = n - 1 - t := by omega
    rw [e, ih', if_neg (div_ne_zero hp2' hp1')]
    rw [show w n (t + 1 + 2) = ((n : ℤ) - 1 - ((t + 1 : ℕ) : ℤ)) * w n (t + 2)
      - ((n : ℤ) - ((t + 1 : ℕ) : ℤ)) * w n (t + 1) from rfl,
      show w n (t + 1 + 1) = w n (t + 2) from rfl]
    have hc : ((n - 1 - (t + 1) : ℕ) : ℚ) = (n : ℚ) - 2 - t := by
      have h : n - 1 - (t + 1) + (t + 2) = n := by omega
      have := congrArg (Nat.cast (R := ℚ)) h
      push_cast at this
      linarith
    rw [hc]
    push_cast
    field_simp
    try ring

lemma w_last (n : ℕ) (hn : 3 ≤ n) : w n (n - 1) = 5 * n - 4 := by
  have h := Q n (n - 2) (by omega)
  rw [show n - 2 + 1 = n - 1 by omega] at h
  have hK : ((n : ℤ) - 1 - ((n - 2 : ℕ) : ℤ)) = 1 := by omega
  rw [hK] at h
  linear_combination h

def hh : ℕ → ℤ
  | 0 => 1
  | (i + 1) => ((i : ℤ) + 3) * hh i

lemma hh_fac : ∀ i, 2 * hh i = (((i + 2)! : ℕ) : ℤ)
  | 0 => by decide
  | i + 1 => by
    rw [show hh (i + 1) = ((i : ℤ) + 3) * hh i from rfl,
      show (i + 1 + 2)! = (i + 3) * (i + 2)! from rfl]
    push_cast
    linear_combination ((i : ℤ) + 3) * hh_fac i

lemma chain (n : ℕ) (hn : 4 ≤ n) : ∀ i, i + 4 ≤ n →
    (5 * (n : ℤ) - 4) ∣ w n (n - 2) - ((i : ℤ) + 4) * hh i * w n (n - 4 - i) := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨t, ht⟩ : ∃ t, t = n - 4 := ⟨_, rfl⟩
    rw [show n - 2 = t + 2 by omega, show n - 4 - 0 = t by omega, w_succ_succ]
    have hq := Q n t (by omega)
    have hK : (n : ℤ) - 1 - t = 3 := by omega
    have hK2 : (n : ℤ) - t = 4 := by omega
    rw [hK] at hq
    rw [hK, hK2, show hh 0 = 1 from rfl]
    exact ⟨1, by push_cast; linear_combination hq⟩
  | succ i ih =>
    intro hi
    obtain ⟨t, ht⟩ : ∃ t, t = n - 5 - i := ⟨_, rfl⟩
    have ih' := ih (by omega)
    rw [show n - 4 - i = t + 1 by omega] at ih'
    rw [show n - 4 - (i + 1) = t by omega]
    have hq := Q n t (by omega)
    have hK : (n : ℤ) - 1 - t = (i : ℤ) + 4 := by omega
    rw [hK] at hq
    obtain ⟨c, hc⟩ := ih'
    refine ⟨c + hh i, ?_⟩
    rw [show hh (i + 1) = ((i : ℤ) + 3) * hh i from rfl]
    push_cast
    linear_combination hc + hh i * hq

lemma F_eq (k : ℕ) : (((k + 4)! / 2 : ℕ) : ℤ) = ((k : ℤ) + 3) * ((k : ℤ) + 4) * hh k := by
  have hF : (k + 4)! / 2 * 2 = (k + 4)! :=
    Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
  have hfe : (k + 4)! = (k + 4) * ((k + 3) * (k + 2)!) := rfl
  have h2 := hh_fac k
  generalize (k + 4)! / 2 = F at hF ⊢
  rw [hfe] at hF
  have hz : (F : ℤ) * 2 = ((k : ℤ) + 4) * (((k : ℤ) + 3) * (((k + 2)! : ℕ) : ℤ)) := by
    exact_mod_cast hF
  apply mul_right_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  linear_combination hz - ((k : ℤ) + 4) * ((k : ℤ) + 3) * h2

lemma den_nat (A B : ℕ) (hB : 0 < B) : ((A : ℚ) / B).den = B / Nat.gcd A B := by
  have hg : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_right A hB
  have hc := Nat.coprime_div_gcd_div_gcd hg
  have hdA := Nat.gcd_dvd_left A B
  have hdB := Nat.gcd_dvd_right A B
  generalize Nat.gcd A B = g at hc hdA hdB hg ⊢
  obtain ⟨a', rfl⟩ := hdA
  obtain ⟨b', rfl⟩ := hdB
  rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at hc
  rw [Nat.mul_div_cancel_left _ hg]
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hb' : 0 < b' := Nat.pos_of_ne_zero (by rintro rfl; simp at hB)
  rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hg0,
    ← Int.cast_natCast a', ← Int.cast_natCast b']
  have := Rat.den_div_eq_of_coprime (a := (a' : ℤ)) (b := (b' : ℤ)) (by exact_mod_cast hb')
    (by simpa using hc)
  exact_mod_cast this

lemma formula (n : ℕ) (hn : 3 ≤ n) : a n = (5 * n - 4) / Nat.gcd (5 * n - 4) (n ! / 2) := by
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | h4
  · have hcf := cf 3 le_rfl 0 (by norm_num)
    rw [show 3 - 1 - 0 = 2 from rfl] at hcf
    have hw2 : w 3 (0 + 2) = ((11 : ℕ) : ℤ) := rfl
    have hw1 : w 3 (0 + 1) = ((7 : ℕ) : ℤ) := rfl
    have ha : a 3 = (1 / continuedFractionDenominator 3 2).den := by
      unfold a; rw [if_neg (by omega)]
    rw [ha, hcf, hw2, hw1, one_div_div, Int.cast_natCast, Int.cast_natCast,
      den_nat 7 11 (by norm_num)]
    norm_num [Nat.factorial]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have hcf := cf (k + 4) (by omega) (k + 1) (by omega)
    rw [show k + 4 - 1 - (k + 1) = 2 by omega, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl] at hcf
    have hw1 : w (k + 4) (k + 3) = ((5 * (k + 4) - 4 : ℕ) : ℤ) := by
      have := w_last (k + 4) (by omega)
      rw [show k + 4 - 1 = k + 3 by omega] at this
      rw [this]; omega
    obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le (pos (k + 4) (k + 2) (by omega)).le
    have ha : a (k + 4) = (1 / continuedFractionDenominator (k + 4) 2).den := by
      unfold a; rw [if_neg (by omega)]
    rw [ha, hcf, hw1, hA, one_div_div, Int.cast_natCast, Int.cast_natCast,
      den_nat A (5 * (k + 4) - 4) (by omega)]
    -- divisibility relation
    have e : ((5 * (k + 4) - 4 : ℕ) : ℤ) = 5 * ((k : ℤ) + 4) - 4 := by omega
    have hdiv : ((5 * (k + 4) - 4 : ℕ) : ℤ) ∣ ((k : ℤ) + 3) * A - (((k + 4)! / 2 : ℕ) : ℤ) := by
      have hc := chain (k + 4) (by omega) k (by omega)
      rw [show k + 4 - 4 - k = 0 by omega, show k + 4 - 2 = k + 2 by omega, hA,
        show w (k + 4) 0 = 1 from rfl] at hc
      rw [F_eq k, e]
      obtain ⟨c, hc⟩ := hc
      refine ⟨((k : ℤ) + 3) * c, ?_⟩
      push_cast at hc
      linear_combination ((k : ℤ) + 3) * hc
    have hgcd : Nat.gcd A (5 * (k + 4) - 4) = Nat.gcd (5 * (k + 4) - 4) ((k + 4)! / 2) := by
      apply Nat.dvd_antisymm
      · apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
        have h1 : ((Nat.gcd A (5 * (k + 4) - 4) : ℕ) : ℤ) ∣ (A : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
        have h2 : ((Nat.gcd A (5 * (k + 4) - 4) : ℕ) : ℤ) ∣ ((5 * (k + 4) - 4 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
        have h3 := h2.trans hdiv
        have h5 := dvd_sub (dvd_mul_of_dvd_right h1 ((k : ℤ) + 3)) h3
        rw [sub_sub_cancel] at h5
        exact Int.natCast_dvd_natCast.mp h5
      · apply Nat.dvd_gcd _ (Nat.gcd_dvd_left _ _)
        have h1 : ((Nat.gcd (5 * (k + 4) - 4) ((k + 4)! / 2) : ℕ) : ℤ) ∣
            ((5 * (k + 4) - 4 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
        have h2 : ((Nat.gcd (5 * (k + 4) - 4) ((k + 4)! / 2) : ℕ) : ℤ) ∣
            (((k + 4)! / 2 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
        have h3 := h1.trans hdiv
        have h4 := dvd_add h3 h2
        rw [sub_add_cancel] at h4
        have hAe : (A : ℤ) = ((5 * (k + 4) - 4 : ℕ) : ℤ) * A - 5 * (((k : ℤ) + 3) * A) := by
          rw [e]; ring
        have h5 : ((Nat.gcd (5 * (k + 4) - 4) ((k + 4)! / 2) : ℕ) : ℤ) ∣ (A : ℤ) := by
          rw [hAe]
          exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h4 5)
        exact Int.natCast_dvd_natCast.mp h5
    rw [hgcd]

lemma pow_dvd_fact (p : ℕ) (hp : 1 ≤ p) : ∀ e, p ^ e ∣ (e * p)!
  | 0 => by simp
  | e + 1 => by
    have ih := pow_dvd_fact p hp e
    have h2 : (e * p + p) * (e * p + p - 1)! = (e * p + p)! := Nat.mul_factorial_pred (by omega)
    rw [pow_succ, add_one_mul, ← h2, mul_comm (p ^ e)]
    exact Nat.mul_dvd_mul ⟨e + 1, by ring⟩
      (ih.trans (Nat.factorial_dvd_factorial (by omega)))

lemma five_le (e : ℕ) : 5 * (e + 3) ≤ 7 ^ (e + 2) := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [show e + 1 + 2 = (e + 2) + 1 by ring, pow_succ]
    omega

lemma char (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hodd : p % 2 = 1) (hn : 3 ≤ n)
    (h : (5 * n - 4) / Nat.gcd (5 * n - 4) (n ! / 2) = p) :
    n < p ∧ ∃ g, 1 ≤ g ∧ g ≤ 4 ∧ 5 * n - 4 = p * g := by
  have hF : n ! / 2 * 2 = n ! := Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
  generalize n ! / 2 = F at h hF
  generalize hg : Nat.gcd (5 * n - 4) F = g at h
  have hgm : g ∣ 5 * n - 4 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
  have hgF : g ∣ F := by rw [← hg]; exact Nat.gcd_dvd_right _ _
  have hm : 5 * n - 4 = p * g := by rw [← h, Nat.div_mul_cancel hgm]
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  by_cases hlt : n < p
  · refine ⟨hlt, g, hg0, ?_, hm⟩
    by_contra hg5
    have := Nat.mul_le_mul_left p (show 5 ≤ g by omega)
    omega
  · exfalso
    have := Fact.mk hp
    have hm0 : 5 * n - 4 ≠ 0 := by omega
    have hpe : p ^ padicValNat p (5 * n - 4) ∣ 5 * n - 4 := pow_padicValNat_dvd
    have hns : ¬ p ^ (padicValNat p (5 * n - 4) + 1) ∣ 5 * n - 4 :=
      pow_succ_padicValNat_not_dvd hm0
    generalize padicValNat p (5 * n - 4) = e at hpe hns
    have hle : p ^ e ≤ 5 * n - 4 := Nat.le_of_dvd (by omega) hpe
    have hep : e * p ≤ n := by
      rcases Nat.lt_or_ge e 3 with he3 | he3
      · interval_cases e
        · simp
        · omega
        · by_cases h7 : p = 7
          · subst h7
            norm_num at hpe
            omega
          · have h9 : p ≠ 9 := by
              rintro rfl
              rcases Nat.Prime.eq_one_or_self_of_dvd hp 3 ⟨3, rfl⟩ with h | h <;> omega
            have h11 : 11 ≤ p := by omega
            have : 11 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p h11
            omega
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
        have h7 := five_le f
        have hpow : 7 ^ (f + 2) ≤ p ^ (f + 2) := Nat.pow_le_pow_left hp7 _
        have : 5 * ((f + 3) * p) ≤ 5 * n - 4 := by
          calc 5 * ((f + 3) * p) = (5 * (f + 3)) * p := by ring
            _ ≤ p ^ (f + 2) * p := Nat.mul_le_mul_right p (h7.trans hpow)
            _ = p ^ (f + 3) := by ring
            _ ≤ 5 * n - 4 := hle
        omega
    have hfact : p ^ e ∣ n ! :=
      (pow_dvd_fact p (by omega) e).trans (Nat.factorial_dvd_factorial hep)
    have hcop : Nat.Coprime (p ^ e) 2 :=
      Nat.Coprime.pow_left e ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    have hpF : p ^ e ∣ F := hcop.dvd_of_dvd_mul_right (by rw [hF]; exact hfact)
    have hpg : p ^ e ∣ g := by rw [← hg]; exact Nat.dvd_gcd hpe hpF
    apply hns
    rw [pow_succ, hm, mul_comm p g]
    exact Nat.mul_dvd_mul_right hpg p

end P

open P in
theorem exists_unique_a_eq_prime :
    ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 → ∃! n, n ≥ 3 ∧ a n = p := by
  rintro p ⟨hp, hodd, h3, h5⟩
  have hp2 := hp.two_le
  have hp7 : 7 ≤ p := by omega
  have h5d : p % 5 ≠ 0 := by
    intro h0
    have : 5 ∣ p := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).mp this with h | h <;> omega
  obtain ⟨c, hc1, hc4, hcmod⟩ : ∃ c, 1 ≤ c ∧ c ≤ 4 ∧ (p * c) % 5 = 1 := by
    have : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
    rcases this with h | h | h | h
    · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨3, by omega, by omega, by omega⟩
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨4, by omega, by omega, by omega⟩
  have hex : ∀ n, 5 * n = p * c + 4 → n ≥ 3 ∧ a n = p := by
    intro n h5n
    have hpc : p * 1 ≤ p * c := Nat.mul_le_mul_left p hc1
    have hpc4 : p * c ≤ p * 4 := Nat.mul_le_mul_left p hc4
    have hn3 : 3 ≤ n := by omega
    refine ⟨hn3, ?_⟩
    rw [formula n hn3]
    have hm : 5 * n - 4 = c * p := by rw [Nat.mul_comm c p]; omega
    rw [hm]
    have hlt : n < p := by omega
    have hF : n ! / 2 * 2 = n ! :=
      Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
    have hcF : c ∣ n ! / 2 := by
      rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2
      · exact one_dvd _
      · have hpc2 : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc2
        have hn4 : 4 ≤ n := by omega
        have h24 : 4 ! ∣ n ! := Nat.factorial_dvd_factorial hn4
        rw [show (4 : ℕ)! = 24 from rfl] at h24
        have h12 : 12 ∣ n ! / 2 := by omega
        exact (show c ∣ 12 by interval_cases c <;> decide).trans h12
    obtain ⟨F', hF'⟩ := hcF
    rw [hF', Nat.gcd_mul_left]
    have hcop : Nat.gcd p F' = 1 := by
      apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
      intro hd
      have h1 : p ∣ n ! / 2 := by rw [hF']; exact Dvd.dvd.mul_left hd c
      have h2 : p ∣ n ! := h1.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega)))
      have := (Nat.Prime.dvd_factorial hp).mp h2
      omega
    rw [hcop, mul_one, Nat.mul_div_cancel_left p (by omega : 0 < c)]
  refine ⟨(p * c + 4) / 5, hex _ (by omega), ?_⟩
  rintro y ⟨hy3, hy⟩
  rw [formula y hy3] at hy
  obtain ⟨hyl, g, hg1, hg4, hyg⟩ := char p y hp hp7 hodd hy3 hy
  have hgc : g = c := by
    interval_cases g <;> interval_cases c <;> omega
  subst hgc
  omega

end OeisA372761

#print axioms OeisA372761.exists_unique_a_eq_prime
