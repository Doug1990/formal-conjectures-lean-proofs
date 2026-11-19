import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Bugeaud06

open Filter

/-- The sequence $m$ eventually grows at least geometrically with a logarithmic correction. -/
def IsGenuinelySublacunary (m : ℕ → ℕ) : Prop :=
  ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, (1 + c / Real.log n) ≤ (m (n+1) : ℝ) / m n

def HasIntermediateGrowth (α : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, Real.exp ((n : ℝ) ^ α) ≤ m n

lemma exp_half_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp (y / 2) ≤ 1 + y := by
  have hF := Real.add_one_le_exp (-(y / 2))
  have e : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (y / 2)
  nlinarith [mul_nonneg (mul_nonneg hE.le (show 0 ≤ Real.exp (-(y / 2)) - (-(y / 2) + 1) by
    linarith)) (show 0 ≤ 1 + y by linarith), mul_nonneg hE.le (show 0 ≤ y - y ^ 2 by nlinarith)]

/-- Positivity and the ratio step past the threshold `N`. -/
lemma step {m : ℕ → ℕ} {c : ℝ} {k : ℕ} (hk : 3 ≤ k)
    (h : 1 + c / Real.log k ≤ (m (k+1) : ℝ) / m k) (hc : 0 < c) :
    0 < m k ∧ (m k : ℝ) * (1 + c / Real.log k) ≤ m (k+1) := by
  have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hy : 0 < c / Real.log k := div_pos hc hl
  have hpos : 0 < m k := by
    rcases Nat.eq_zero_or_pos (m k) with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  refine ⟨hpos, ?_⟩
  have hp : (0 : ℝ) < m k := by exact_mod_cast hpos
  rw [le_div_iff₀ hp] at h
  linarith

lemma pow_bound {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N)
    (hev : ∀ k ≥ N, 1 + c / Real.log k ≤ (m (k+1) : ℝ) / m k) (n : ℕ) :
    ∀ j, N + j ≤ n → (1 + c / Real.log n) ^ j ≤ (m (N + j) : ℝ) := by
  intro j
  induction j with
  | zero =>
    intro _
    have := (step hN (hev N le_rfl) hc).1
    simp only [pow_zero, add_zero]
    exact_mod_cast this
  | succ j ih =>
    intro hj
    have hk : 3 ≤ N + j := by omega
    obtain ⟨hp, hs⟩ := step hk (hev (N + j) (by omega)) hc
    have hl : 0 < Real.log (N + j : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N + j))
    have hle : Real.log (N + j : ℕ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N + j)) (by exact_mod_cast (by omega))
    have hy : c / Real.log n ≤ c / Real.log (N + j : ℕ) :=
      div_le_div_of_nonneg_left hc.le hl hle
    have hyn : 0 ≤ c / Real.log n := div_nonneg hc.le (hl.le.trans hle)
    have ih' := ih (by omega)
    rw [pow_succ, show N + (j + 1) = (N + j) + 1 by omega]
    calc (1 + c / Real.log n) ^ j * (1 + c / Real.log n)
        ≤ (m (N + j) : ℝ) * (1 + c / Real.log (N + j : ℕ)) :=
          mul_le_mul ih' (by linarith) (by linarith) (by positivity)
      _ ≤ _ := hs

lemma asymp {c α : ℝ} (hc : 0 < c) (hα1 : α < 1) :
    ∀ᶠ n : ℕ in atTop, 4 * Real.log n * (n : ℝ) ^ α ≤ c * n := by
  have h := (isLittleO_log_rpow_atTop (r := 1 - α) (by linarith)).bound
    (show 0 < c / 4 by positivity)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with n hn h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast h1)),
    abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hn
  have hpa : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hn0.le _
  have hmul : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ α = n := by
    rw [← Real.rpow_add hn0]; simp
  nlinarith [mul_le_mul_of_nonneg_right hn hpa]

theorem hasIntermediateGrowth_of_isGenuinelySublacunary {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set N := max N0 3 with hNdef
  have hN : 3 ≤ N := le_max_right _ _
  have hev' : ∀ k ≥ N, 1 + c / Real.log k ≤ (m (k+1) : ℝ) / m k :=
    fun k hk => hN0 k (le_trans (le_max_left _ _) hk)
  have hlogc : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop c)
  unfold HasIntermediateGrowth
  filter_upwards [asymp hc hα1, hlogc, eventually_ge_atTop (2 * N)] with n ha hlc hn
  have hl : 0 < Real.log n := lt_of_lt_of_le hc hlc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set y := c / Real.log n with hy
  have hy0 : 0 ≤ y := div_nonneg hc.le hl.le
  have hy1 : y ≤ 1 := (div_le_one hl).2 hlc
  have hpow := pow_bound hc hN hev' n (n - N) (by omega)
  rw [show N + (n - N) = n by omega] at hpow
  have hexp : Real.exp (((n - N : ℕ) : ℝ) * (y / 2)) ≤ (1 + y) ^ (n - N) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_half_le hy0 hy1) _
  refine le_trans (Real.exp_le_exp.2 ?_) (hexp.trans hpow)
  have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by
    rw [Nat.cast_sub (by omega)]
  have h2N : (2 * N : ℝ) ≤ n := by exact_mod_cast hn
  rw [hcast, hy]
  have hpa : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hn0.le _
  -- target: n^α ≤ (n - N) * (c / log n / 2)
  have key : (n : ℝ) ^ α ≤ (n : ℝ) / 2 * (c / Real.log n / 2) := by
    rw [show (n : ℝ) / 2 * (c / Real.log n / 2) = c * n / (4 * Real.log n) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine key.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end Bugeaud06

#print axioms Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary
