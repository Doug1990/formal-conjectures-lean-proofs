import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace OeisA368692

open Nat

namespace Q

lemma layer (m q : ℕ) (hq : 2 ≤ q) (hodd : q = 2 → m % 2 = 1) :
    2 * m / q + m / q + (3 * m + 2) / q ≤ 6 * m / q := by
  have hq0 : 0 < q := by omega
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < q ∧ m = r + q * a :=
    ⟨m / q, m % q, Nat.mod_lt _ hq0, (Nat.mod_add_div m q).symm⟩
  have hr1 : q = 2 → r = 1 := by
    intro h
    subst h
    have := hodd rfl
    omega
  have e1 : 2 * (r + q * a) / q = 2 * r / q + 2 * a := by
    rw [show 2 * (r + q * a) = 2 * r + q * (2 * a) by ring, Nat.add_mul_div_left _ _ hq0]
  have e2 : (r + q * a) / q = r / q + a := Nat.add_mul_div_left _ _ hq0
  have e3 : (3 * (r + q * a) + 2) / q = (3 * r + 2) / q + 3 * a := by
    rw [show 3 * (r + q * a) + 2 = (3 * r + 2) + q * (3 * a) by ring,
      Nat.add_mul_div_left _ _ hq0]
  have e4 : 6 * (r + q * a) / q = 6 * r / q + 6 * a := by
    rw [show 6 * (r + q * a) = 6 * r + q * (6 * a) by ring, Nat.add_mul_div_left _ _ hq0]
  rw [e1, e2, e3, e4, Nat.div_eq_of_lt hr]
  have hX := Nat.div_add_mod (2 * r) q
  have hX' := Nat.mod_lt (2 * r) hq0
  have hY := Nat.div_add_mod (3 * r + 2) q
  have hY' := Nat.mod_lt (3 * r + 2) hq0
  have hU := Nat.div_add_mod (6 * r) q
  have hU' := Nat.mod_lt (6 * r) hq0
  have bX : 2 * r / q < 2 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bY : (3 * r + 2) / q < 3 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bU : 6 * r / q < 6 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  generalize 2 * r / q = X at *
  generalize (3 * r + 2) / q = Y at *
  generalize 6 * r / q = U at *
  generalize 2 * r % q = x at *
  generalize (3 * r + 2) % q = y at *
  generalize 6 * r % q = u at *
  interval_cases X <;> interval_cases Y <;> interval_cases U <;> omega

lemma top3 (m q w : ℕ) (hw : q = 3 * w) (hq : 3 ≤ q) (hle : q ≤ 3 * m) (hlt : m < q) :
    2 * m / q + m / q + (3 * m + 2) / q + 1 ≤ 6 * m / q := by
  have hq0 : 0 < q := by omega
  rw [Nat.div_eq_of_lt hlt]
  have hX := Nat.div_add_mod (2 * m) q
  have hX' := Nat.mod_lt (2 * m) hq0
  have hY := Nat.div_add_mod (3 * m + 2) q
  have hY' := Nat.mod_lt (3 * m + 2) hq0
  have hU := Nat.div_add_mod (6 * m) q
  have hU' := Nat.mod_lt (6 * m) hq0
  have bX : 2 * m / q < 2 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bY : (3 * m + 2) / q < 4 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bU : 6 * m / q < 6 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  generalize 2 * m / q = X at *
  generalize (3 * m + 2) / q = Y at *
  generalize 6 * m / q = U at *
  generalize 2 * m % q = x at *
  generalize (3 * m + 2) % q = y at *
  generalize 6 * m % q = u at *
  interval_cases X <;> interval_cases Y <;> interval_cases U <;> omega

lemma top2 (m q w : ℕ) (hw : q = 4 * w) (hq : 4 ≤ q) (hle : q ≤ 2 * m) (hlt : m < q)
    (hodd : m % 2 = 1) (h31 : ¬ 4 ∣ 3 * m + 1) :
    2 * m / q + m / q + (3 * m + 2) / q + 1 ≤ 6 * m / q := by
  have hq0 : 0 < q := by omega
  rw [Nat.div_eq_of_lt hlt]
  have hX := Nat.div_add_mod (2 * m) q
  have hX' := Nat.mod_lt (2 * m) hq0
  have hY := Nat.div_add_mod (3 * m + 2) q
  have hY' := Nat.mod_lt (3 * m + 2) hq0
  have hU := Nat.div_add_mod (6 * m) q
  have hU' := Nat.mod_lt (6 * m) hq0
  have bX : 2 * m / q < 2 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bY : (3 * m + 2) / q < 4 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have bU : 6 * m / q < 6 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  generalize 2 * m / q = X at *
  generalize (3 * m + 2) / q = Y at *
  generalize 6 * m / q = U at *
  generalize 2 * m % q = x at *
  generalize (3 * m + 2) % q = y at *
  generalize 6 * m % q = u at *
  interval_cases X <;> interval_cases Y <;> interval_cases U <;> omega

lemma strict_sum (s : Finset ℕ) (f g : ℕ → ℕ) (h : ∀ i ∈ s, f i ≤ g i) (j : ℕ) (hj : j ∈ s)
    (hj' : f j + 1 ≤ g j) : (∑ i ∈ s, f i) + 1 ≤ ∑ i ∈ s, g i :=
  Nat.succ_le_of_lt (Finset.sum_lt_sum h ⟨j, hj, hj'⟩)

theorem B (m : ℕ) (hm : m % 2 = 1) :
    2 ^ 2 * 3 * ((2 * m)! * m ! * (3 * m + 2)!) ∣ (6 * m)! * ((3 * m + 4) * (3 * m + 5)) := by
  have hA : (2 * m)! * m ! * (3 * m + 2)! ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)
  have h12 : (2 : ℕ) ^ 2 * 3 ≠ 0 := by norm_num
  have hD : 2 ^ 2 * 3 * ((2 * m)! * m ! * (3 * m + 2)!) ≠ 0 := Nat.mul_ne_zero h12 hA
  have h45 : (3 * m + 4) * (3 * m + 5) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hN : (6 * m)! * ((3 * m + 4) * (3 * m + 5)) ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) h45
  rw [← Nat.factorization_prime_le_iff_dvd hD hN]
  intro p hp
  have := Fact.mk hp
  have f2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have f3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul h12 hA, padicValNat.mul (by norm_num : (2 : ℕ) ^ 2 ≠ 0)
      (by norm_num : (3 : ℕ) ≠ 0), padicValNat.pow 2 2,
    padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_ne_zero (2 * m)) (Nat.factorial_ne_zero m))
      (Nat.factorial_ne_zero (3 * m + 2)),
    padicValNat.mul (Nat.factorial_ne_zero (2 * m)) (Nat.factorial_ne_zero m),
    padicValNat.mul (Nat.factorial_ne_zero (6 * m)) h45,
    padicValNat.mul (by omega : 3 * m + 4 ≠ 0) (by omega : 3 * m + 5 ≠ 0)]
  have hb : ∀ k, k ≤ 6 * m → Nat.log p k < Nat.log p (6 * m) + 1 := fun k hk =>
    Nat.lt_succ_of_le (Nat.log_mono_right hk)
  rw [padicValNat_factorial (hb (2 * m) (by omega)), padicValNat_factorial (hb m (by omega)),
    padicValNat_factorial (hb (3 * m + 2) (by omega)), padicValNat_factorial (hb (6 * m) le_rfl),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hlay : ∀ i ∈ Finset.Ico 1 (Nat.log p (6 * m) + 1),
      2 * m / p ^ i + m / p ^ i + (3 * m + 2) / p ^ i ≤ 6 * m / p ^ i := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hpi : p ^ 1 ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
    rw [pow_one] at hpi
    exact layer m (p ^ i) (by have := hp.two_le; omega) (fun _ => hm)
  have hsum := Finset.sum_le_sum hlay
  by_cases h2 : p = 2
  · subst h2
    rw [padicValNat_self, padicValNat_primes (by decide : 2 ≠ 3)]
    by_cases h4 : 4 ∣ 3 * m + 1
    · have : 2 ≤ padicValNat 2 (3 * m + 5) :=
        (padicValNat_dvd_iff_le (by omega)).1 (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega)
      omega
    · have : 1 ≤ padicValNat 2 (3 * m + 5) :=
        (padicValNat_dvd_iff_le (by omega)).1 (by rw [pow_one]; omega)
      have hm3 : 2 ≤ m := by omega
      have hk1 : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) (by rw [pow_one]; omega)
      have hk : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
      have hk' : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      have h2k : 2 ^ 1 ≤ 2 ^ Nat.log 2 m := Nat.pow_le_pow_right (by norm_num) hk1
      have hj : Nat.log 2 m + 1 ≤ Nat.log 2 (6 * m) :=
        Nat.le_log_of_pow_le (by norm_num) (by rw [pow_succ]; omega)
      have hw : 2 ^ (Nat.log 2 m + 1) = 4 * 2 ^ (Nat.log 2 m - 1) := by
        rw [show Nat.log 2 m + 1 = 2 + (Nat.log 2 m - 1) by omega, pow_add]
        norm_num
      have hst := strict_sum _ (fun i => 2 * m / 2 ^ i + m / 2 ^ i + (3 * m + 2) / 2 ^ i)
        (fun i => 6 * m / 2 ^ i) hlay (Nat.log 2 m + 1)
        (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        (top2 m _ _ hw (by rw [pow_succ]; omega) (by rw [pow_succ]; omega) hk' hm h4)
      beta_reduce at hst
      omega
  · by_cases h3 : p = 3
    · subst h3
      rw [padicValNat_self, padicValNat_primes (by decide : 3 ≠ 2)]
      have hk : 3 ^ Nat.log 3 m ≤ m := Nat.pow_log_le_self 3 (by omega)
      have hk' : m < 3 ^ (Nat.log 3 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      have h1k : 3 ^ 0 ≤ 3 ^ Nat.log 3 m := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)
      rw [pow_zero] at h1k
      have hj : Nat.log 3 m + 1 ≤ Nat.log 3 (6 * m) :=
        Nat.le_log_of_pow_le (by norm_num) (by rw [pow_succ]; omega)
      have hst := strict_sum _ (fun i => 2 * m / 3 ^ i + m / 3 ^ i + (3 * m + 2) / 3 ^ i)
        (fun i => 6 * m / 3 ^ i) hlay (Nat.log 3 m + 1)
        (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        (top3 m _ (3 ^ Nat.log 3 m) (by rw [pow_succ, mul_comm])
          (by rw [pow_succ]; omega) (by rw [pow_succ]; omega) hk')
      beta_reduce at hst
      omega
    · rw [padicValNat_primes h2, padicValNat_primes h3]
      omega

lemma fact4 (k : ℕ) : (k + 4)! = k ! * ((k + 1) * (k + 2) * (k + 3) * (k + 4)) := by
  rw [show k + 4 = k + 3 + 1 from rfl, Nat.factorial_succ, show k + 3 = k + 2 + 1 from rfl,
    Nat.factorial_succ, show k + 2 = k + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
  ring

lemma fact2 (k : ℕ) : (k + 2)! = k ! * ((k + 1) * (k + 2)) := by
  rw [show k + 2 = k + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
  ring

end Q

theorem a_is_int (n : ℕ) : 108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!) ^ 2) ∣
    (12 * n + 6)! * (6 * n + 9)! := by
  have hB := Q.B (2 * n + 1) (by omega)
  rw [show 2 * (2 * n + 1) = 4 * n + 2 by ring, show 3 * (2 * n + 1) + 2 = 6 * n + 5 by ring,
    show 6 * (2 * n + 1) = 12 * n + 6 by ring, show 3 * (2 * n + 1) + 4 = 6 * n + 7 by ring,
    show 3 * (2 * n + 1) + 5 = 6 * n + 8 by ring] at hB
  have f9 : (6 * n + 9)! = (6 * n + 5)! * ((6 * n + 6) * (6 * n + 7) * (6 * n + 8) * (6 * n + 9)) :=
    Q.fact4 (6 * n + 5)
  have f3 : (2 * n + 3)! = (2 * n + 1)! * ((2 * n + 2) * (2 * n + 3)) := Q.fact2 (2 * n + 1)
  rw [f9, f3]
  have e1 : 108 * ((4 * n + 2)! * ((2 * n + 1)! * ((2 * n + 2) * (2 * n + 3))) * (6 * n + 5)! ^ 2)
      = 2 ^ 2 * 3 * ((4 * n + 2)! * (2 * n + 1)! * (6 * n + 5)!) *
        (9 * ((2 * n + 2) * (2 * n + 3)) * (6 * n + 5)!) := by ring
  have e2 : (12 * n + 6)! * ((6 * n + 5)! * ((6 * n + 6) * (6 * n + 7) * (6 * n + 8) * (6 * n + 9)))
      = (12 * n + 6)! * ((6 * n + 7) * (6 * n + 8)) *
        (9 * ((2 * n + 2) * (2 * n + 3)) * (6 * n + 5)!) := by ring
  rw [e1, e2]
  exact Nat.mul_dvd_mul_right hB _

end OeisA368692

#print axioms OeisA368692.a_is_int
