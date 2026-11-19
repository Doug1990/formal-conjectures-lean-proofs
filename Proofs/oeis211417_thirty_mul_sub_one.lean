import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace OeisA211417

def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

namespace T

lemma div_eq (m q c d : ℕ) (hc : 0 < c) (h : c * d = 30) :
    d * m / q = 30 * m / q / c := by
  rw [Nat.div_div_eq_div_mul, ← h, mul_comm q c, mul_assoc,
    Nat.mul_div_mul_left _ _ hc]

lemma key (m q : ℕ) :
    15 * m / q + 10 * m / q + 6 * m / q ≤ 30 * m / q + m / q := by
  have h2 := div_eq m q 2 15 (by omega) (by omega)
  have h3 := div_eq m q 3 10 (by omega) (by omega)
  have h5 := div_eq m q 5 6 (by omega) (by omega)
  have h30 := div_eq m q 30 1 (by omega) (by omega)
  rw [one_mul] at h30
  rw [h2, h3, h5, h30]
  generalize 30 * m / q = J
  omega

lemma key1 (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 30 * m - 1) (hm : 1 ≤ m) :
    15 * m / q + 10 * m / q + 6 * m / q + 1 ≤ 30 * m / q + m / q := by
  have h2 := div_eq m q 2 15 (by omega) (by omega)
  have h3 := div_eq m q 3 10 (by omega) (by omega)
  have h5 := div_eq m q 5 6 (by omega) (by omega)
  have h30 := div_eq m q 30 1 (by omega) (by omega)
  rw [one_mul] at h30
  rw [h2, h3, h5, h30]
  obtain ⟨k, hk⟩ := hd
  have e : 30 * m = q * k + 1 := by omega
  have hJ : 30 * m / q = k := by
    rw [e, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
  have m2 : (q * k) % 2 = (q % 2) * (k % 2) % 2 := Nat.mul_mod _ _ _
  have m3 : (q * k) % 3 = (q % 3) * (k % 3) % 3 := Nat.mul_mod _ _ _
  have m5 : (q * k) % 5 = (q % 5) * (k % 5) % 5 := Nat.mul_mod _ _ _
  have k2 : k % 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at m2; generalize q * k = P at m2 e; omega
  have k3 : k % 3 ≠ 0 := by
    intro h; rw [h, mul_zero] at m3; generalize q * k = P at m3 e; omega
  have k5 : k % 5 ≠ 0 := by
    intro h; rw [h, mul_zero] at m5; generalize q * k = P at m5 e; omega
  rw [hJ]
  omega

lemma sum_bound (b v : ℕ) (L R : ℕ → ℕ) (hvb : v + 1 ≤ b) (h0 : ∀ i, L i ≤ R i)
    (h1 : ∀ i, 1 ≤ i → i ≤ v → L i + 1 ≤ R i) :
    v + ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i := by
  rw [← Finset.sum_Ico_consecutive L (show 1 ≤ v + 1 by omega) hvb,
    ← Finset.sum_Ico_consecutive R (show 1 ≤ v + 1 by omega) hvb]
  have hA : ∑ i ∈ Finset.Ico 1 (v + 1), (L i + 1) ≤ ∑ i ∈ Finset.Ico 1 (v + 1), R i := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact h1 i hi.1 (by omega)
  have hc : ∑ i ∈ Finset.Ico 1 (v + 1), (fun _ => (1 : ℕ)) i = v := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.card_Ico]
    omega
  rw [Finset.sum_add_distrib, hc] at hA
  have hB : ∑ i ∈ Finset.Ico (v + 1) b, L i ≤ ∑ i ∈ Finset.Ico (v + 1) b, R i :=
    Finset.sum_le_sum (fun i _ => h0 i)
  omega

theorem main (n : ℕ) (hn : 1 ≤ n) :
    (30 * n - 1) * (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      Nat.factorial (30 * n) * Nat.factorial n := by
  have hx : 30 * n - 1 ≠ 0 := by omega
  have f15 := Nat.factorial_ne_zero (15 * n)
  have f10 := Nat.factorial_ne_zero (10 * n)
  have f6 := Nat.factorial_ne_zero (6 * n)
  have f30 := Nat.factorial_ne_zero (30 * n)
  have f1 := Nat.factorial_ne_zero n
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6))
    (Nat.mul_ne_zero f30 f1)]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6),
    padicValNat.mul (Nat.mul_ne_zero f15 f10) f6, padicValNat.mul f15 f10,
    padicValNat.mul f30 f1]
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * n) < Nat.log p (30 * n) + 1 := fun c hc =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right n hc))
  have hb1 : Nat.log p n < Nat.log p (30 * n) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial (hb 15 (by omega)), padicValNat_factorial (hb 10 (by omega)),
    padicValNat_factorial (hb 6 (by omega)), padicValNat_factorial (hb 30 (by omega)),
    padicValNat_factorial hb1]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hdv : p ^ padicValNat p (30 * n - 1) ∣ 30 * n - 1 := pow_padicValNat_dvd
  apply sum_bound
  · have hle : p ^ padicValNat p (30 * n - 1) ≤ 30 * n :=
      (Nat.le_of_dvd (by omega) hdv).trans (by omega)
    have := Nat.le_log_of_pow_le hp.one_lt hle
    omega
  · intro i
    exact key n (p ^ i)
  · intro i hi hiv
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact key1 n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) hn

end T

theorem thirty_mul_sub_one_dvd_a (n : ℕ) : (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨-(a 0 : ℤ), ?_⟩
    push_cast
    ring
  · have h := T.main n hn
    have h2 : (30 * n - 1) ∣ a n := by
      unfold a
      rw [mul_comm] at h
      exact Nat.dvd_div_of_mul_dvd h
    have h3 : ((30 * n - 1 : ℕ) : ℤ) = 30 * (n : ℤ) - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ 30 * n by omega)]
      ring
    rw [← h3]
    exact Int.natCast_dvd_natCast.mpr h2

end OeisA211417

#print axioms OeisA211417.thirty_mul_sub_one_dvd_a
