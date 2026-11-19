import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Digits.Defs

namespace OeisA361033

/-- The factorial ratio $3(4n)!/(n!((n+1)!)^3)$. -/
def a (n : ℕ) : ℕ :=
  3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3)

namespace P

/-- binary digit sum -/
def S (m : ℕ) : ℕ := (Nat.digits 2 m).sum

lemma S_pos_eq (m : ℕ) (hm : 0 < m) : S m = m % 2 + S (m / 2) := by
  unfold S
  rw [Nat.digits_def' (by decide : 1 < 2) hm, List.sum_cons]

lemma S_zero : S 0 = 0 := by simp [S]

lemma S_two_mul (m : ℕ) : S (2 * m) = S m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · rw [S_pos_eq (2 * m) (by omega), show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega,
      zero_add]

lemma S_ge (m : ℕ) (hm : 0 < m) : 1 ≤ S m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [S_pos_eq m hm]
    by_cases h : m % 2 = 1
    · omega
    · have := ih (m / 2) (by omega) (by omega)
      omega

lemma S_eq_one (m : ℕ) : S m = 1 ↔ ∃ k, m = 2 ^ k := by
  constructor
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro h
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [S_zero] at h
        omega
      rw [S_pos_eq m hm] at h
      by_cases h2 : m % 2 = 1
      · have h0 : S (m / 2) = 0 := by omega
        have : m / 2 = 0 := by
          by_contra hc
          have := S_ge (m / 2) (by omega)
          omega
        exact ⟨0, by omega⟩
      · obtain ⟨k, hk⟩ := ih (m / 2) (by omega) (by omega)
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => rw [pow_zero, S_pos_eq 1 (by omega), show 1 / 2 = 0 from rfl, S_zero]
    | succ k ih => rw [pow_succ, mul_comm, S_two_mul, ih]

lemma S_le (m : ℕ) : S m ≤ m := Nat.digit_sum_le 2 m

lemma val2_fact (m : ℕ) : padicValNat 2 m.factorial = m - S m := by
  have := Fact.mk Nat.prime_two
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  rw [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  exact h

lemma term (n q : ℕ) (hq : 0 < q) :
    (n / q + 3 * ((n + 1) / q)) * q + min q 4 ≤ 4 * n + 4 := by
  have h1 := Nat.div_add_mod' n q
  have h1' := Nat.mod_lt n hq
  have h2 := Nat.div_add_mod' (n + 1) q
  have h2' := Nat.mod_lt (n + 1) hq
  have hm4 : min q 4 ≤ 4 := min_le_right _ _
  have hmq : min q 4 ≤ q := min_le_left _ _
  rw [add_mul, mul_assoc]
  by_cases hc : (n + 1) / q * q ≤ n
  · omega
  · have hB : (n + 1) / q * q = n + 1 := by omega
    have hAB : n / q < (n + 1) / q := by
      by_contra hh
      have := Nat.mul_le_mul_right q (Nat.le_of_not_lt hh)
      omega
    have := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hAB)
    rw [Nat.succ_mul] at this
    omega

lemma term4 (n q : ℕ) (hq : 4 ≤ q) : n / q + 3 * ((n + 1) / q) ≤ 4 * n / q := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have := term n q (by omega)
  have : min q 4 = 4 := min_eq_right hq
  omega

lemma term3 (n : ℕ) : n / 3 + 3 * ((n + 1) / 3) ≤ 4 * n / 3 + 1 := by omega

lemma sum_le_one_add (b : ℕ) (f g : ℕ → ℕ) (h1 : f 1 ≤ g 1 + 1)
    (h : ∀ i, 2 ≤ i → f i ≤ g i) :
    ∑ i ∈ Finset.Ico 1 b, f i ≤ 1 + ∑ i ∈ Finset.Ico 1 b, g i := by
  induction b with
  | zero => simp
  | succ b ih =>
    rcases Nat.lt_or_ge b 1 with hb | hb
    · have : b = 0 := by omega
      subst this
      simp
    · rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top hb]
      rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
      · simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
        omega
      · have := h b hb2
        omega

lemma val_odd (n p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    padicValNat p n.factorial + 3 * padicValNat p (n + 1).factorial ≤
      padicValNat p 3 + padicValNat p (4 * n).factorial := by
  have := Fact.mk hp
  have hb : ∀ m, m ≤ 4 * n + 4 → Nat.log p m < Nat.log p (4 * n + 4) + 1 := fun m hm =>
    Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [padicValNat_factorial (hb n (by omega)), padicValNat_factorial (hb (n + 1) (by omega)),
    padicValNat_factorial (hb (4 * n) (by omega)), Finset.mul_sum, ← Finset.sum_add_distrib]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  by_cases h3 : p = 3
  · subst h3
    rw [padicValNat_self]
    refine sum_le_one_add _ (fun i => n / 3 ^ i + 3 * ((n + 1) / 3 ^ i))
      (fun i => 4 * n / 3 ^ i) ?_ ?_
    · simp only [pow_one]
      exact term3 n
    · intro i hi
      apply term4
      calc 4 ≤ 3 ^ 2 := by decide
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) hi
  · refine le_add_left (Finset.sum_le_sum fun i hi => term4 n (p ^ i) ?_)
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have : p ^ 1 ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
    rw [pow_one] at this
    omega

lemma valD (n p : ℕ) [Fact p.Prime] :
    padicValNat p (n.factorial * (n + 1).factorial ^ 3) =
      padicValNat p n.factorial + 3 * padicValNat p (n + 1).factorial := by
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
    padicValNat.pow]

lemma valN (n p : ℕ) [Fact p.Prime] :
    padicValNat p (3 * (4 * n).factorial) = padicValNat p 3 + padicValNat p (4 * n).factorial :=
  padicValNat.mul (by omega) (Nat.factorial_ne_zero _)

lemma v2_three : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

lemma S_four (n : ℕ) : S (4 * n) = S n := by
  rw [show 4 * n = 2 * (2 * n) by omega, S_two_mul, S_two_mul]

theorem dvd (n : ℕ) :
    n.factorial * (n + 1).factorial ^ 3 ∣ 3 * (4 * n).factorial := by
  have hD : n.factorial * (n + 1).factorial ^ 3 ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hN : 3 * (4 * n).factorial ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero _)
  rw [← Nat.factorization_prime_le_iff_dvd hD hN]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, valD, valN]
  by_cases h2 : p = 2
  · subst h2
    rw [val2_fact, val2_fact, val2_fact, v2_three, S_four]
    have := S_ge (n + 1) (by omega)
    have := S_le n
    have := S_le (n + 1)
    omega
  · exact val_odd n p hp h2

theorem val_a (n : ℕ) : padicValNat 2 (a n) = 3 * (S (n + 1) - 1) := by
  have := Fact.mk Nat.prime_two
  rw [show a n = 3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3) from rfl,
    padicValNat.div_of_dvd (dvd n), valN, valD, val2_fact, val2_fact, val2_fact, v2_three,
    S_four]
  have := S_ge (n + 1) (by omega)
  have := S_le n
  have := S_le (n + 1)
  omega

theorem a_ne_zero (n : ℕ) : a n ≠ 0 := by
  have hD : 0 < n.factorial * (n + 1).factorial ^ 3 :=
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.factorial_pos _) _)
  have hN : 0 < 3 * (4 * n).factorial := Nat.mul_pos (by omega) (Nat.factorial_pos _)
  exact (Nat.div_pos (Nat.le_of_dvd hN (dvd n)) hD).ne'

end P

open P in
theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  have hv := val_a n
  have ha := a_ne_zero n
  have e : padicValNat 2 (a n) = 0 ↔ ¬ 2 ∣ a n := by
    constructor
    · intro h
      rcases padicValNat.eq_zero_iff.mp h with h | h | h
      · omega
      · exact absurd h ha
      · exact h
    · intro h
      exact padicValNat.eq_zero_of_not_dvd h
  have e2 : (∃ k : ℕ, n = 2 ^ k - 1) ↔ S (n + 1) = 1 := by
    rw [S_eq_one]
    constructor
    · rintro ⟨k, hk⟩
      have := Nat.two_pow_pos k
      exact ⟨k, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by omega⟩
  rw [e2, Nat.odd_iff]
  have := S_ge (n + 1) (by omega)
  constructor
  · intro h
    by_contra hc
    have h' : ¬ 2 ∣ a n := by omega
    have := e.mpr h'
    omega
  · intro h
    have := e.mp (by rw [hv]; omega)
    omega

end OeisA361033

#print axioms OeisA361033.conjecture_1
