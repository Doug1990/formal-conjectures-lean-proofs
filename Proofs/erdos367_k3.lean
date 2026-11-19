import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Associated

open Asymptotics Filter

namespace Erdos367

def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

namespace K3

lemma B_dvd (r m : ℕ) (hm : m ≠ 0) : B r m ∣ m := by
  unfold B
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

lemma B_ne_zero (m : ℕ) (hm : m ≠ 0) : B 2 m ≠ 0 := by
  intro h
  have := B_dvd 2 m hm
  rw [h, zero_dvd_iff] at this
  exact hm this

lemma pow_dvd_B (m p : ℕ) (hp : 2 ≤ m.factorization p) :
    p ^ m.factorization p ∣ B 2 m := by
  unfold B
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finsupp.mem_support_iff]
  exact ⟨by omega, hp⟩

/-- if `n = c * s^2` then the primes occurring exactly once divide `c`. -/
lemma le_mul_B (c s : ℕ) (hc : c ≠ 0) (hs : s ≠ 0) :
    c * s ^ 2 ≤ c * B 2 (c * s ^ 2) := by
  have hn0 : c * s ^ 2 ≠ 0 := mul_ne_zero hc (pow_ne_zero 2 hs)
  have he : ∀ a, (c * s ^ 2).factorization a = c.factorization a + 2 * s.factorization a := by
    intro a
    rw [Nat.factorization_mul hc (pow_ne_zero 2 hs), Nat.factorization_pow]
    simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hsplit := Finset.prod_filter_mul_prod_filter_not (c * s ^ 2).factorization.support
    (fun i => 2 ≤ (c * s ^ 2).factorization i) (fun i => i ^ (c * s ^ 2).factorization i)
  have hprod := Nat.prod_factorization_pow_eq_self hn0
  rw [Finsupp.prod] at hprod
  rw [hprod] at hsplit
  have hR : (∏ i ∈ (c * s ^ 2).factorization.support with ¬ 2 ≤ (c * s ^ 2).factorization i,
      i ^ (c * s ^ 2).factorization i) ∣ c := by
    rw [Finset.prod_congr rfl (g := fun i => i)]
    · apply Finset.prod_primes_dvd
      · intro a ha
        rw [Finset.mem_filter] at ha
        have h1 := ha.1
        rw [Nat.support_factorization] at h1
        exact (Nat.prime_of_mem_primeFactors h1).prime
      · intro a ha
        rw [Finset.mem_filter, Finsupp.mem_support_iff] at ha
        apply Nat.dvd_of_factorization_pos
        have := he a
        omega
    · intro x hx
      rw [Finset.mem_filter, Finsupp.mem_support_iff] at hx
      have : (c * s ^ 2).factorization x = 1 := by omega
      rw [this, pow_one]
  have hRle := Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hR
  have hB : B 2 (c * s ^ 2) = ∏ i ∈ (c * s ^ 2).factorization.support with
      2 ≤ (c * s ^ 2).factorization i, i ^ (c * s ^ 2).factorization i := rfl
  rw [← hB] at hsplit
  calc c * s ^ 2 = B 2 (c * s ^ 2) * _ := hsplit.symm
    _ ≤ B 2 (c * s ^ 2) * c := Nat.mul_le_mul_left _ hRle
    _ = c * B 2 (c * s ^ 2) := Nat.mul_comm _ _

/-- `P (i+1) = P i * (4 P i^2 + 3)`, `m i = 2 P i^2 + 1` iterates `t ↦ 4t^3 - 3t` from `3`. -/
def P : ℕ → ℕ
  | 0 => 1
  | i + 1 => P i * (4 * P i ^ 2 + 3)

lemma P_pos (i : ℕ) : 0 < P i := by
  induction i with
  | zero => simp [P]
  | succ i ih => simp only [P]; exact Nat.mul_pos ih (by omega)

lemma P_Q (i : ℕ) : ∃ Q, P i ^ 2 + 1 = 2 * Q ^ 2 := by
  induction i with
  | zero => exact ⟨1, by simp [P]⟩
  | succ i ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q * (4 * P i ^ 2 + 1), ?_⟩
    simp only [P]
    rw [show 2 * (Q * (4 * P i ^ 2 + 1)) ^ 2 = (2 * Q ^ 2) * (4 * P i ^ 2 + 1) ^ 2 by ring,
      ← hQ]
    ring

lemma m_step (i : ℕ) :
    (2 * P (i + 1) ^ 2 + 1) + 3 * (2 * P i ^ 2 + 1) = 4 * (2 * P i ^ 2 + 1) ^ 3 := by
  simp only [P]; ring

lemma m_dvd (i : ℕ) : 3 ^ (i + 1) ∣ 2 * P i ^ 2 + 1 := by
  induction i with
  | zero => simp [P]
  | succ i ih =>
    have hs := m_step i
    have he : 2 * P (i + 1) ^ 2 + 1 = 4 * (2 * P i ^ 2 + 1) ^ 3 - 3 * (2 * P i ^ 2 + 1) := by
      omega
    rw [he]
    apply Nat.dvd_sub
    · apply Dvd.dvd.mul_left
      have h1 := pow_dvd_pow_of_dvd ih 3
      rw [← pow_mul] at h1
      exact (pow_dvd_pow 3 (by omega)).trans h1
    · rw [pow_succ']
      exact Nat.mul_dvd_mul_left 3 ih

lemma m_size (i : ℕ) : 2 * (2 * P i ^ 2 + 1) ≤ 6 ^ (3 ^ i) := by
  induction i with
  | zero => simp [P]
  | succ i ih =>
    have hs := m_step i
    have h8 : 2 * (2 * P (i + 1) ^ 2 + 1) ≤ (2 * (2 * P i ^ 2 + 1)) ^ 3 := by
      rw [mul_pow]; omega
    have h3 := Nat.pow_le_pow_left ih 3
    rw [← pow_mul, ← pow_succ] at h3
    omega

lemma three_pow (a : ℕ) : a + 1 ≤ 3 ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ]; omega

lemma prod_three (n : ℕ) :
    ∏ m ∈ Finset.Ico n (n + 3), B 2 m = B 2 n * B 2 (n + 1) * B 2 (n + 2) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, add_zero]

lemma key (i : ℕ) (hi : 1 ≤ i) : ∃ n : ℕ, i ≤ n ∧ 2 ≤ n ∧ n ≤ 6 ^ (3 ^ i) ∧
    n * (n + 2) * 3 ^ (i + 1) ≤ 2 * ∏ m ∈ Finset.Ico n (n + 3), B 2 m := by
  obtain ⟨Q, hQ⟩ := P_Q i
  have hP := P_pos i
  have hd := m_dvd i
  have hsz := m_size i
  have h3 := three_pow i
  set p := P i with hp
  have hm0 : 2 * p ^ 2 + 1 ≠ 0 := by omega
  have hmle := Nat.le_of_dvd (by omega) hd
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hP
  refine ⟨2 * p ^ 2, by omega, by omega, by omega, ?_⟩
  rw [prod_three]
  -- the three factors
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  have hA := le_mul_B 2 p (by omega) (by omega)
  have hC := le_mul_B 1 (2 * Q) (by omega) (by omega)
  rw [one_mul, one_mul] at hC
  have hC' : 2 * p ^ 2 + 2 = (2 * Q) ^ 2 := by rw [mul_pow]; omega
  rw [← hC'] at hC
  -- middle factor
  have hv : i + 1 ≤ (2 * p ^ 2 + 1).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm0).mp hd
  have hM : 3 ^ (i + 1) ∣ B 2 (2 * p ^ 2 + 1) :=
    (pow_dvd_pow 3 hv).trans (pow_dvd_B _ 3 (by omega))
  have hMle := Nat.le_of_dvd (Nat.pos_of_ne_zero (B_ne_zero _ hm0)) hM
  have e1 : 2 * p ^ 2 + 2 = 2 * p ^ 2 + 1 + 1 := rfl
  calc 2 * p ^ 2 * (2 * p ^ 2 + 2) * 3 ^ (i + 1)
      ≤ (2 * B 2 (2 * p ^ 2)) * B 2 (2 * p ^ 2 + 2) * B 2 (2 * p ^ 2 + 1) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul hA hC) hMle
    _ = 2 * (B 2 (2 * p ^ 2) * B 2 (2 * p ^ 2 + 1) * B 2 (2 * p ^ 2 + 2)) := by ring

lemma lower : ∃ᶠ (n : ℕ) in atTop,
    (1 / 4 : ℝ) * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
      ((∏ m ∈ .Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, han, hn2, hn6, hprod⟩ := key (a + 1) (by omega)
  refine ⟨n, by omega, ?_⟩
  set Pr := ∏ m ∈ Finset.Ico n (n + 3), B 2 m
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : Real.log (n : ℝ) ≤ 5 * 3 ^ (a + 1) := by
    have h1 : Real.log (n : ℝ) ≤ Real.log ((6 : ℝ) ^ (3 ^ (a + 1))) := by
      apply Real.log_le_log (by linarith)
      exact_mod_cast hn6
    rw [Real.log_pow] at h1
    have h6 : Real.log 6 ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h7 : (0 : ℝ) ≤ ((3 ^ (a + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.log (n : ℝ) ≤ ((3 ^ (a + 1) : ℕ) : ℝ) * Real.log 6 := h1
      _ ≤ ((3 ^ (a + 1) : ℕ) : ℝ) * 5 := by
        apply mul_le_mul_of_nonneg_left _ h7; linarith
      _ = 5 * 3 ^ (a + 1) := by push_cast; ring
  have hP : (n : ℝ) * (n + 2) * 3 ^ (a + 1 + 1) ≤ 2 * (Pr : ℝ) := by exact_mod_cast hprod
  have ht : (0 : ℝ) ≤ 3 ^ (a + 1) := by positivity
  rw [pow_succ] at hP
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hl : (1 / 4 : ℝ) * ((n : ℝ) ^ 2 * Real.log n) ≤ (1 / 4) * ((n : ℝ) ^ 2 * (5 * 3 ^ (a + 1))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
  nlinarith [mul_nonneg (mul_nonneg hn0 hn0) ht, mul_nonneg hn0 ht]

end K3

theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∃ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        ((∏ m ∈ .Ico n (n + 3), B 2 m : ℕ) : ℝ) :=
  ⟨1 / 4, by norm_num, K3.lower⟩

theorem erdos_367.parts.ii : ¬ ∀ k : ℕ, 1 ≤ k →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro h
  obtain ⟨C, hC⟩ := (h 3 (by norm_num)).bound
  have hlog : ∀ᶠ (n : ℕ) in atTop, 4 * C + 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨n, hlow, hup, hl, hn⟩ :=
    (K3.lower.and_eventually (hC.and (hlog.and (eventually_ge_atTop 1)))).exists
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_two,
    Real.norm_of_nonneg (by positivity)] at hup
  have hN : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hN.le]

end Erdos367

#print axioms Erdos367.erdos_367.variants.k_ge_three_lower
#print axioms Erdos367.erdos_367.parts.ii
