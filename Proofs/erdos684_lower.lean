import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Lucas

namespace Erdos684

open Filter Real

/-- The factor of $\binom{n}{k}$ containing the full multiplicity of every prime at most $k$. -/
def smallPrimePart (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE k, p ^ ((n.choose k).factorization p)

namespace KL

lemma not_dvd_choose_pred (p j : ℕ) (hp : p.Prime) (hj : j < p) :
    ¬ p ∣ Nat.choose (p - 1) j := by
  intro h
  have hjle : j ≤ p - 1 := by omega
  have key := Nat.choose_mul_factorial_mul_factorial hjle
  have : p ∣ (p - 1).factorial := by
    rw [← key]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  rw [hp.dvd_factorial] at this
  have := hp.two_le
  omega

/-- Kummer-type lemma: if `p^e ∣ n+1` and `k < p^e`, then `p ∤ C(n,k)`. -/
lemma not_dvd_choose (p : ℕ) (hp : p.Prime) :
    ∀ e n k : ℕ, p ^ e ∣ n + 1 → k < p ^ e → ¬ p ∣ Nat.choose n k := by
  have := Fact.mk hp
  intro e
  induction e with
  | zero =>
    intro n k _ hk h
    have : k = 0 := by simpa using hk
    subst this
    simp at h
    exact hp.one_lt.ne' h
  | succ e ih =>
    intro n k hd hk h
    have hp1 : p ∣ n + 1 := (dvd_pow_self p (Nat.succ_ne_zero e)).trans hd
    obtain ⟨c, hc⟩ := hp1
    have hp2 := hp.two_le
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at hc
      · exact h0
    have hn : n = p * (c - 1) + (p - 1) := by
      have : p * c = p * (c - 1) + p := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
    have hmod : n % p = p - 1 := by
      rw [hn, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    have hdiv : n / p = c - 1 := by
      rw [hn, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; simp
    have hce : p ^ e ∣ n / p + 1 := by
      rw [hdiv, Nat.sub_add_cancel hc1]
      rw [pow_succ', hc] at hd
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) hd
    have hke : k / p < p ^ e := by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← pow_succ]; exact hk
    have hL := (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p))
    have h2 : p ∣ Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) :=
      (Nat.ModEq.dvd_iff hL (dvd_refl p)).1 h
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · rw [hmod] at h3
      exact not_dvd_choose_pred p (k % p) hp (Nat.mod_lt _ (by omega)) h3
    · exact ih (n / p) (k / p) hce hke h3

lemma spp_eq_one (n k : ℕ)
    (h : ∀ p, p.Prime → p ≤ k → ∃ e, p ^ e ∣ n + 1 ∧ k < p ^ e) :
    smallPrimePart n k = 1 := by
  unfold smallPrimePart
  apply Finset.prod_eq_one
  intro p hp
  have hpp := Nat.prime_of_mem_primesLE hp
  have hpk := Nat.le_of_mem_primesLE hp
  obtain ⟨e, he1, he2⟩ := h p hpp hpk
  rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_choose p hpp e n k he1 he2), pow_zero]

/-- The modulus `M = lcmUpto K * primorial K`. -/
lemma M_dvd (K p : ℕ) (hp : p.Prime) (hpK : p ≤ K) :
    p ^ (Nat.log p K + 1) ∣ Nat.lcmUpto K * primorial K := by
  rw [pow_succ]
  apply mul_dvd_mul
  · have := Nat.ordProj_dvd (Nat.lcmUpto K) p
    rwa [Nat.factorization_lcmUpto K hp] at this
  · unfold primorial
    apply Finset.dvd_prod_of_mem
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp⟩

lemma M_pos (K : ℕ) : 0 < Nat.lcmUpto K * primorial K :=
  Nat.mul_pos (Nat.lcmUpto_pos K) (primorial_pos K)

lemma log_M_le (K : ℕ) :
    Real.log ((Nat.lcmUpto K * primorial K : ℕ) : ℝ) ≤ (2 * Real.log 4 + 4) * K := by
  have h1 : Real.log (Nat.lcmUpto K : ℝ) ≤ (Real.log 4 + 4) * K := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  have h2 : Real.log (primorial K : ℝ) ≤ Real.log 4 * K := by
    have := Chebyshev.theta_le_log4_mul_x (x := (K : ℝ)) (by positivity)
    rwa [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at this
  push_cast
  rw [Real.log_mul (by exact_mod_cast (Nat.lcmUpto_pos K).ne')
    (by exact_mod_cast (primorial_pos K).ne')]
  linarith

end KL

theorem erdos_684.lower_bound :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by
  rw [Nat.frequently_atTop_iff_infinite]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  set K := B + 2 with hK
  set M := Nat.lcmUpto K * primorial K with hM
  have hMpos : 0 < M := KL.M_pos K
  -- M > K
  have h2 : 2 ^ (Nat.log 2 K + 1) ∣ M := KL.M_dvd K 2 Nat.prime_two (by omega)
  have hKlt : K < 2 ^ (Nat.log 2 K + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have hMK : K < M := lt_of_lt_of_le hKlt (Nat.le_of_dvd hMpos h2)
  have hmem : M - 1 ∈ {n : ℕ | 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1} := by
    refine ⟨by omega, ?_⟩
    intro k hk
    apply KL.spp_eq_one
    intro p hp hpk
    -- k < K
    have hlogn : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
      apply Real.log_le_log
      · have : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < M - 1 by omega)
        exact this
      · exact_mod_cast Nat.sub_le M 1
    have hlM := KL.log_M_le K
    have hl2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hKpos : (0 : ℝ) ≤ K := by positivity
    have hkK : (k : ℝ) ≤ K := by
      rw [hl4] at hlM
      nlinarith
    have hkK' : k ≤ K := by exact_mod_cast hkK
    refine ⟨Nat.log p K + 1, ?_, ?_⟩
    · rw [Nat.sub_add_cancel (by omega)]
      exact KL.M_dvd K p hp (by omega)
    · exact lt_of_le_of_lt hkK' (Nat.lt_pow_succ_log_self hp.one_lt K)
  have := hB hmem
  omega

end Erdos684

#print axioms Erdos684.erdos_684.lower_bound
