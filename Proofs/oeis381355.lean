import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.LinearCombination

namespace OeisA381355

open PowerSeries

/-- The $n$-th prime, indexed from $p_1=2$. -/
noncomputable def primeN (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The coefficients of $F$, obtained successively from $[x^n]F(x)^{p_n}=0$. -/
noncomputable def f : ℕ → ℤ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else if n = 1 then 1
    else
      -(coeff n
          (PowerSeries.mk (fun k => if h : k < n then ih k h else 0) ^ primeN n) /
        (primeN n : ℤ))

/-- The generating function of A381353. -/
noncomputable def series : PowerSeries ℤ := PowerSeries.mk f

/-- The coefficients of $xF'(x)/F(x)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n (X * derivative ℤ series * invOfUnit series 1)

private lemma f_eq (n : ℕ) :
    f n = if n = 0 then 1 else if n = 1 then 1 else
      -(coeff n (PowerSeries.mk (fun k => if k < n then f k else 0) ^ primeN n) /
        (primeN n : ℤ)) := by
  rw [f, Nat.strongRec_eq]
  rfl

private lemma f_0 : f 0 = 1 := by rw [f_eq]; simp

private lemma coeff_mul_range (n : ℕ) (F G : PowerSeries ℤ) :
    coeff n (F * G) = ∑ k ∈ Finset.range (n + 1), coeff k F * coeff (n - k) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

namespace P

/-- For a prime `p` and `G` with constant term 1, the coefficients `1 ≤ j < p` of `G^p`
are divisible by `p`. -/
lemma pdvd (p : ℕ) (hp : p.Prime) (G : PowerSeries ℤ) (h0 : coeff 0 G = 1) (j : ℕ)
    (hj1 : 1 ≤ j) (hjp : j < p) : (p : ℤ) ∣ coeff j (G ^ p) := by
  have hG : G = X * mk (fun k => coeff (k + 1) G) + 1 := by
    ext k
    rcases k with _ | k
    · simp [h0]
    · rw [map_add, coeff_succ_X_mul, coeff_mk, coeff_one]
      simp
  rw [hG, add_pow, map_sum]
  apply Finset.dvd_sum
  intro m hm
  rw [Finset.mem_range] at hm
  rw [one_pow, mul_one, ← map_natCast (C : ℤ →+* PowerSeries ℤ), coeff_mul_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [coeff_one, show j ≠ 0 by omega]
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with rfl | hmp
  · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]
    simp
  · exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) hmp)) _

lemma coeff0_series : coeff 0 series = 1 := by
  rw [series, coeff_mk, f_0]

lemma lt_primeN (n : ℕ) (hn : 1 < n) : n < primeN n := by
  have := Nat.add_two_le_nth_prime (n - 1)
  unfold primeN
  omega

/-- The defining property: `[x^n] F^{p_n} = 0` for `n ≥ 2`. -/
lemma coeff_pow_eq_zero (n : ℕ) (hn : 1 < n) : coeff n (series ^ primeN n) = 0 := by
  have hf := f_eq n
  rw [if_neg (by omega), if_neg (by omega)] at hf
  have hp : (primeN n).Prime := Nat.prime_nth_prime _
  have hlt := lt_primeN n hn
  have hsplit : series = X ^ n * mk (fun k => f (k + n)) +
      mk (fun k => if k < n then f k else 0) := by
    ext k
    rw [map_add, coeff_X_pow_mul']
    simp only [series, coeff_mk]
    by_cases h : n ≤ k
    · rw [if_pos h, if_neg (by omega), Nat.sub_add_cancel h, add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hc := pdvd (primeN n) hp (mk (fun k => if k < n then f k else 0))
    (by rw [coeff_mk, if_pos (by omega), f_0]) n (by omega) hlt
  generalize mk (fun k => if k < n then f k else 0) = G at hf hsplit hc
  have hG0 : constantCoeff G = 1 := by
    have := congrArg (coeff 0) hsplit
    rw [map_add, coeff_X_pow_mul', if_neg (by omega), zero_add, coeff0_series] at this
    rw [← coeff_zero_eq_constantCoeff_apply, ← this]
  generalize primeN n = p at hf hc hp hlt ⊢
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [hsplit, add_pow, map_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ m ∈ Finset.range (q + 1), coeff n ((X ^ n * mk (fun k => f (k + n))) ^ (m + 1 + 1) *
      G ^ (q + 2 - (m + 1 + 1)) * ((q + 2).choose (m + 1 + 1) : PowerSeries ℤ)) = 0 := by
    intro m _
    rw [mul_pow, ← pow_mul, mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg]
    have : n * (m + 1 + 1) = n * m + n + n := by ring
    omega
  rw [Finset.sum_eq_zero hz, zero_add]
  simp only [zero_add, pow_one, Nat.choose_one_right, pow_zero, one_mul, Nat.sub_zero,
    Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply]
  simp only [map_mul, map_pow, hG0, one_pow, one_mul, map_natCast]
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, hf]
  rw [Int.neg_mul, Int.ediv_mul_cancel (by exact_mod_cast hc)]
  ring

lemma hinv : series * invOfUnit series 1 = 1 :=
  mul_invOfUnit _ _ (by rw [Units.val_one, ← coeff_zero_eq_constantCoeff_apply, coeff0_series])

lemma key (q : ℕ) :
    X * derivative ℤ (series ^ (q + 1)) =
      ((q + 1 : ℕ) : PowerSeries ℤ) *
        ((X * derivative ℤ series * invOfUnit series 1) * series ^ (q + 1)) := by
  rw [derivative_pow, Nat.add_sub_cancel, pow_succ]
  linear_combination (-(((q + 1 : ℕ) : PowerSeries ℤ) * X * derivative ℤ series * series ^ q)) *
    hinv

end P

theorem conjecture (n : ℕ) (hn : 1 < n) : (primeN n : ℤ) ∣ a n := by
  have hp : (primeN n).Prime := Nat.prime_nth_prime _
  have hlt := P.lt_primeN n hn
  have h0 := P.coeff_pow_eq_zero n hn
  have hdvd : ∀ j, 1 ≤ j → j < primeN n → (primeN n : ℤ) ∣ coeff j (series ^ primeN n) :=
    fun j h1 h2 => P.pdvd _ hp series P.coeff0_series j h1 h2
  generalize primeN n = p at hp hlt h0 hdvd ⊢
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk := congrArg (coeff (m + 1)) (P.key q)
  rw [coeff_succ_X_mul, coeff_derivative, h0, zero_mul,
    ← map_natCast (C : ℤ →+* PowerSeries ℤ), mul_comm, coeff_mul_C] at hk
  have hne : ((q + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (show q + 1 ≠ 0 by omega)
  have hs : coeff (m + 1) ((X * derivative ℤ series * invOfUnit series 1) *
      series ^ (q + 1)) = 0 := by
    rcases mul_eq_zero.mp hk.symm with h | h
    · exact h
    · exact absurd h hne
  rw [coeff_mul_range, Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    map_pow, ← coeff_zero_eq_constantCoeff_apply, P.coeff0_series, one_pow, mul_one] at hs
  have ha : a (m + 1) = -∑ k ∈ Finset.range (m + 1),
      coeff k (X * derivative ℤ series * invOfUnit series 1) *
        coeff (m + 1 - k) (series ^ (q + 1)) := by
    unfold a
    linear_combination hs
  rw [ha]
  apply Dvd.dvd.neg_right
  apply Finset.dvd_sum
  intro k hk'
  rw [Finset.mem_range] at hk'
  exact Dvd.dvd.mul_left (hdvd _ (by omega) (by omega)) _

end OeisA381355

#print axioms OeisA381355.conjecture
