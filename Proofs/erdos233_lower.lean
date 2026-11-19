import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Chebyshev

open Filter Real

namespace Erdos233

/-- Restated from FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

namespace L

lemma mono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma sum_gap (N : ℕ) :
    (∑ n ∈ Finset.range N, (primeGap n : ℝ)) = (Nat.nth Nat.Prime N : ℝ) - 2 := by
  have h : ∀ n, (primeGap n : ℝ) = (Nat.nth Nat.Prime (n+1) : ℝ) - Nat.nth Nat.Prime n := by
    intro n
    unfold primeGap
    rw [Nat.cast_sub (mono (Nat.lt_succ_self n)).le]
  simp only [h]
  rw [Finset.sum_range_sub (fun n => (Nat.nth Nat.Prime n : ℝ)), Nat.nth_prime_zero_eq_two]
  simp

lemma theta_ge (N M : ℕ) :
    ((N - M : ℕ) : ℝ) * Real.log (M + 2) ≤ Chebyshev.theta (Nat.nth Nat.Prime N) := by
  have e : ∑ k ∈ Finset.Ico M N, Real.log (Nat.nth Nat.Prime k)
      = ∑ q ∈ (Finset.Ico M N).image (Nat.nth Nat.Prime), Real.log q :=
    (Finset.sum_image (f := fun q : ℕ => Real.log (q : ℝ)) (s := Finset.Ico M N)
      (fun a _ b _ h => mono.injective h)).symm
  have h1 : ∑ k ∈ Finset.Ico M N, Real.log (Nat.nth Nat.Prime k)
      ≤ Chebyshev.theta (Nat.nth Nat.Prime N) := by
    rw [e]
    unfold Chebyshev.theta
    rw [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [Finset.mem_image, Finset.mem_Ico] at hq
      obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hq
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨(Nat.prime_nth_prime k).pos, (mono hk).le⟩, Nat.prime_nth_prime k⟩
    · intro q hq _
      apply Real.log_nonneg
      simp only [Finset.mem_filter] at hq
      exact_mod_cast hq.2.one_lt.le
  have h2 : ∀ k ∈ Finset.Ico M N, Real.log (M + 2) ≤ Real.log (Nat.nth Nat.Prime k) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hM0 : (0:ℝ) < (M:ℝ) + 2 := by
      have := (Nat.cast_nonneg M : (0:ℝ) ≤ M); linarith
    apply Real.log_le_log hM0
    have : M + 2 ≤ Nat.nth Nat.Prime k :=
      (Nat.add_two_le_nth_prime M).trans (mono.monotone hk.1)
    exact_mod_cast this
  calc ((N - M : ℕ) : ℝ) * Real.log (M + 2)
        = ∑ k ∈ Finset.Ico M N, Real.log (M + 2) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum h2
    _ ≤ _ := h1

lemma p_lower (N : ℕ) (hN : 4 ≤ N) :
    (N : ℝ) * Real.log N ≤ 4 * Real.log 4 * (Nat.nth Nat.Prime N : ℝ) := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = N / 2 := ⟨_, rfl⟩
  have hM : M ≤ N := by omega
  have h1 := theta_ge N M
  have h2 := Chebyshev.theta_le_log4_mul_x
    (Nat.cast_nonneg (Nat.nth Nat.Prime N) : (0:ℝ) ≤ (Nat.nth Nat.Prime N : ℝ))
  have hA : (N : ℝ) / 2 ≤ ((N - M : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]
    have h : M * 2 ≤ N := by omega
    have : (M : ℝ) * 2 ≤ N := by exact_mod_cast h
    linarith
  have hB0 : (N:ℝ) / 2 ≤ (M : ℝ) + 2 := by
    have h : N ≤ M * 2 + 1 := by omega
    have : (N:ℝ) ≤ M * 2 + 1 := by exact_mod_cast h
    linarith
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hB : Real.log N / 2 ≤ Real.log (M + 2) := by
    have h3 : Real.log ((N:ℝ) / 2) ≤ Real.log (M + 2) := Real.log_le_log (by linarith) hB0
    rw [Real.log_div (by linarith) (by norm_num)] at h3
    linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have key : (N:ℝ) / 2 * (Real.log N / 2) ≤ ((N - M : ℕ) : ℝ) * Real.log (M + 2) :=
    mul_le_mul hA hB (by linarith) (by linarith)
  linarith

end L

theorem erdos_233.variants.lower_bound :
    (fun (N : ℕ) => N * (log N)^2) =O[atTop]
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 4 * Real.log 4 := ⟨_, rfl⟩
  have c0 : 0 < c := by rw [hc]; have := Real.log_pos (show (1:ℝ) < 4 by norm_num); linarith
  apply Asymptotics.IsBigO.of_bound (4 * c ^ 2)
  filter_upwards [eventually_ge_atTop 16] with N hN
  have hN' : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hP := L.p_lower N (by omega)
  rw [← hc] at hP
  have hT := L.sum_gap N
  have hCS : ((Nat.nth Nat.Prime N : ℝ) - 2) ^ 2
      ≤ (N : ℝ) * ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => (primeGap n : ℝ))
    rw [Finset.card_range] at this
    rw [← hT]
    exact this
  have hS0 : 0 ≤ ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hP4 : (4:ℝ) ≤ (Nat.nth Nat.Prime N : ℝ) := by
    have h := Nat.add_two_le_nth_prime N
    have : (N : ℝ) + 2 ≤ (Nat.nth Nat.Prime N : ℝ) := by exact_mod_cast h
    linarith
  have hD : (N:ℝ) * Real.log N ≤ 2 * c * ((Nat.nth Nat.Prime N : ℝ) - 2) := by
    have : 0 ≤ c * ((Nat.nth Nat.Prime N : ℝ) - 4) := mul_nonneg c0.le (by linarith)
    nlinarith
  have h0 : 0 ≤ (N:ℝ) * Real.log N := mul_nonneg hNpos.le hlogN
  have hsq := pow_le_pow_left₀ h0 hD 2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hNpos.le (sq_nonneg _)),
    abs_of_nonneg hS0]
  have : (N:ℝ) * ((N:ℝ) * Real.log N ^ 2)
      ≤ (N:ℝ) * (4 * c ^ 2 * ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2) := by
    calc (N:ℝ) * ((N:ℝ) * Real.log N ^ 2) = ((N:ℝ) * Real.log N) ^ 2 := by ring
      _ ≤ (2 * c * ((Nat.nth Nat.Prime N : ℝ) - 2)) ^ 2 := hsq
      _ = 4 * c ^ 2 * ((Nat.nth Nat.Prime N : ℝ) - 2) ^ 2 := by ring
      _ ≤ 4 * c ^ 2 * ((N : ℝ) * ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (N:ℝ) * (4 * c ^ 2 * ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2) := by ring
  exact le_of_mul_le_mul_left this hNpos

end Erdos233

#print axioms Erdos233.erdos_233.variants.lower_bound
