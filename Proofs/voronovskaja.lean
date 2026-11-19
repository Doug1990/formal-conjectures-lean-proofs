import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (k / n) * ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

namespace Voro

noncomputable def b (x : ℝ) (n k : ℕ) : ℝ := (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

lemma b_nonneg {x : ℝ} (hx : x ∈ I) (n k : ℕ) : 0 ≤ b x n k := by
  have h0 : 0 ≤ x := hx.1
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg h1 _)

lemma sum_b (x : ℝ) (n : ℕ) : ∑ k ∈ Finset.range (n + 1), b x n k = 1 := by
  have h := add_pow x (1 - x) n
  rw [show x + (1 - x) = 1 by ring, one_pow] at h
  refine (Finset.sum_congr rfl fun k _ => ?_).trans h.symm
  unfold b; ring

lemma shift (x : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1 + 1), (k : ℝ) * g k * b x (n + 1) k
      = (n + 1) * x * ∑ k ∈ Finset.range (n + 1), g (k + 1) * b x n k := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold b
  have h : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := Nat.add_one_mul_choose_eq n k
  have h' : ((n : ℝ) + 1) * (n.choose k : ℝ) = ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast h
  rw [show n + 1 - (k + 1) = n - k by omega]
  push_cast
  linear_combination (-(g (k + 1) * x ^ (k + 1) * (1 - x) ^ (n - k))) * h'

lemma lin (x : ℝ) (n : ℕ) (c0 c1 c2 c3 c4 : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        (c0 + c1 * k + c2 * (k : ℝ) ^ 2 + c3 * (k : ℝ) ^ 3 + c4 * (k : ℝ) ^ 4) * b x n k
      = c0 * ∑ k ∈ Finset.range (n + 1), b x n k
        + c1 * ∑ k ∈ Finset.range (n + 1), (k : ℝ) * b x n k
        + c2 * ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * b x n k
        + c3 * ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 3 * b x n k
        + c4 * ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 4 * b x n k := by
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma shiftPow (x : ℝ) (m i : ℕ) :
    ∑ k ∈ Finset.range (m + 1 + 1), (k : ℝ) ^ (i + 1) * b x (m + 1) k
      = (m + 1) * x * ∑ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ i * b x m k := by
  have h := shift x m (fun k => (k : ℝ) ^ i)
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma m1 (x : ℝ) (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (k : ℝ) * b x n k = n * x := by
  cases n with
  | zero => simp
  | succ m =>
    have h := shiftPow x m 0
    simp only [zero_add, pow_one, pow_zero, one_mul] at h
    rw [h, sum_b]; push_cast; ring

lemma m2 (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * b x n k = n * (n - 1) * x ^ 2 + n * x := by
  cases n with
  | zero => simp
  | succ m =>
    rw [shiftPow x m 1]
    have e : ∑ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ 1 * b x m k
        = ∑ k ∈ Finset.range (m + 1),
          (1 + 1 * k + 0 * (k : ℝ) ^ 2 + 0 * (k : ℝ) ^ 3 + 0 * (k : ℝ) ^ 4) * b x m k :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e, lin, sum_b, m1]; push_cast; ring

lemma m3 (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 3 * b x n k
      = n * (n - 1) * (n - 2) * x ^ 3 + 3 * n * (n - 1) * x ^ 2 + n * x := by
  cases n with
  | zero => simp
  | succ m =>
    rw [shiftPow x m 2]
    have e : ∑ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ 2 * b x m k
        = ∑ k ∈ Finset.range (m + 1),
          (1 + 2 * k + 1 * (k : ℝ) ^ 2 + 0 * (k : ℝ) ^ 3 + 0 * (k : ℝ) ^ 4) * b x m k :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e, lin, sum_b, m1, m2]; push_cast; ring

lemma m4 (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 4 * b x n k
      = n * (n - 1) * (n - 2) * (n - 3) * x ^ 4 + 6 * n * (n - 1) * (n - 2) * x ^ 3
        + 7 * n * (n - 1) * x ^ 2 + n * x := by
  cases n with
  | zero => simp
  | succ m =>
    rw [shiftPow x m 3]
    have e : ∑ k ∈ Finset.range (m + 1), ((k : ℝ) + 1) ^ 3 * b x m k
        = ∑ k ∈ Finset.range (m + 1),
          (1 + 3 * k + 3 * (k : ℝ) ^ 2 + 1 * (k : ℝ) ^ 3 + 0 * (k : ℝ) ^ 4) * b x m k :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e, lin, sum_b, m1, m2, m3]; push_cast; ring

lemma S1 (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) * b x n k = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [show ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) * b x n k
      = ∑ k ∈ Finset.range (n + 1), ((-x) + (1 / n) * k + 0 * (k : ℝ) ^ 2 + 0 * (k : ℝ) ^ 3
        + 0 * (k : ℝ) ^ 4) * b x n k from
      Finset.sum_congr rfl fun k _ => by ring]
  rw [lin, sum_b, m1]
  field_simp
  ring

lemma S2 (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * b x n k = x * (1 - x) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [show ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * b x n k
      = ∑ k ∈ Finset.range (n + 1), (x ^ 2 + (-2 * x / n) * k + (1 / n ^ 2) * (k : ℝ) ^ 2
        + 0 * (k : ℝ) ^ 3 + 0 * (k : ℝ) ^ 4) * b x n k from
      Finset.sum_congr rfl fun k _ => by ring]
  rw [lin, sum_b, m1, m2]
  field_simp
  ring

lemma S4 (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * b x n k
      = x * (1 - x) * (1 + 3 * (n - 2) * (x * (1 - x))) / n ^ 3 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [show ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * b x n k
      = ∑ k ∈ Finset.range (n + 1), (x ^ 4 + (-4 * x ^ 3 / n) * k + (6 * x ^ 2 / n ^ 2) * (k : ℝ) ^ 2
        + (-4 * x / n ^ 3) * (k : ℝ) ^ 3 + (1 / n ^ 4) * (k : ℝ) ^ 4) * b x n k from
      Finset.sum_congr rfl fun k _ => by ring]
  rw [lin, sum_b, m1, m2, m3, m4]
  field_simp
  ring

lemma num_le (u n : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) (hn : 1 ≤ n) :
    u * (1 + 3 * (n - 2) * u) ≤ n := by
  have e2 : u * u ≤ 1 / 4 * (1 / 4) := mul_le_mul hu1 hu1 hu0 (by norm_num)
  have e3 : n * (u * u) ≤ n * (1 / 4 * (1 / 4)) := mul_le_mul_of_nonneg_left e2 (by linarith)
  have e4 : 0 ≤ u * u := mul_nonneg hu0 hu0
  have : u * (1 + 3 * (n - 2) * u) = u + 3 * (n * (u * u)) - 6 * (u * u) := by ring
  rw [this]; linarith

lemma u_le (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by
  have : x * (1 - x) = 1 / 4 - (x - 1 / 2) ^ 2 := by ring
  rw [this]; linarith [sq_nonneg (x - 1 / 2)]

lemma S4_le (x : ℝ) (hx : x ∈ I) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * b x n k ≤ 1 / n ^ 2 := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [S4 x hn]
  have h := num_le (x * (1 - x)) n (mul_nonneg hx.1 (by linarith [hx.2])) (u_le x) hn1
  have h3 : (0 : ℝ) < n ^ 3 := pow_pos hnpos 3
  calc x * (1 - x) * (1 + 3 * (n - 2) * (x * (1 - x))) / n ^ 3 ≤ n / n ^ 3 :=
        (div_le_div_iff_of_pos_right h3).2 h
    _ = 1 / n ^ 2 := by rw [div_eq_div_iff h3.ne' (pow_pos hnpos 2).ne']; ring

/-! Taylor part -/

lemma P_eq (f : ℝ → ℝ) (s : Set ℝ) (x t : ℝ) :
    taylorWithinEval f 2 s x t = f x + (t - x) * iteratedDerivWithin 1 f s x
      + (1 / 2) * (t - x) ^ 2 * iteratedDerivWithin 2 f s x := by
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ, Nat.factorial]

noncomputable def R (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f t - (f x + (t - x) * iteratedDerivWithin 1 f I x
    + (1 / 2) * (t - x) ^ 2 * iteratedDerivWithin 2 f I x)

lemma R_littleO (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I) (hf : ContDiffOn ℝ 2 f I) :
    (R f x) =o[𝓝[I] x] fun t => (t - x) ^ 2 := by
  have h := taylor_isLittleO (n := 2) (convex_Icc (0 : ℝ) 1) hx (by exact_mod_cast hf)
  have e : (fun t => f t - taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) x t) = R f x := by
    funext t; rw [P_eq]; rfl
  rw [e] at h
  exact h

lemma R_cont (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffOn ℝ 2 f I) : ContinuousOn (R f x) I := by
  unfold R
  refine hf.continuousOn.sub (Continuous.continuousOn ?_)
  exact (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)).add
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).mul continuous_const)

lemma taylor_bound (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I) (hf : ContDiffOn ℝ 2 f I)
    {ε : ℝ} (hε : 0 < ε) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ I,
      |R f x t| ≤ ε * (t - x) ^ 2 + K * (t - x) ^ 4 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 ((R_littleO f x hx hf).def hε)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (R_cont f x hf)
  have hK : 0 ≤ max M 0 / δ ^ 4 := div_nonneg (le_max_right _ _) (le_of_lt (pow_pos hδ 4))
  refine ⟨max M 0 / δ ^ 4, hK, fun t ht => ?_⟩
  have h4 : 0 ≤ (t - x) ^ 4 := by
    rw [show (t - x) ^ 4 = ((t - x) ^ 2) ^ 2 by ring]; exact sq_nonneg _
  have h2 : 0 ≤ ε * (t - x) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  by_cases hd : |t - x| < δ
  · have h1 : ‖R f x t‖ ≤ ε * ‖(t - x) ^ 2‖ :=
      hsub ⟨(by rwa [Metric.mem_ball, Real.dist_eq]), ht⟩
    rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, sq_abs] at h1
    have := mul_nonneg hK h4
    linarith
  · have hd' : δ ≤ |t - x| := not_lt.1 hd
    have hM' : |R f x t| ≤ max M 0 := by
      have := hM t ht
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hδ4 : δ ^ 4 ≤ (t - x) ^ 4 := by
      have := pow_le_pow_left₀ hδ.le hd' 4
      rwa [← abs_pow, abs_of_nonneg h4] at this
    have e : max M 0 = max M 0 / δ ^ 4 * δ ^ 4 :=
      (div_mul_cancel₀ _ (pow_ne_zero 4 hδ.ne')).symm
    have := mul_le_mul_of_nonneg_left hδ4 hK
    linarith

/-! Assembly -/

lemma tail_diff (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    (bernsteinTail n k).eval x - (bernsteinTail n (k + 1)).eval x = b x n k := by
  unfold bernsteinTail
  rw [Finset.Icc_eq_cons_Ioc hk, Finset.sum_cons,
    show Finset.Ioc k n = Finset.Icc (k + 1) n by
      ext j; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
  simp [bernsteinPolynomial, b]

lemma bez_one (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    bezierBernstein n 1 f x = ∑ k ∈ Finset.range (n + 1), f (k / n) * b x n k := by
  unfold bezierBernstein
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Real.rpow_one, Real.rpow_one, tail_diff n k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

lemma key (f : ℝ → ℝ) (x : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (bezierBernstein n 1 f x - f x)
      = (1 / 2) * x * (1 - x) * iteratedDerivWithin 2 f I x
        + n * ∑ k ∈ Finset.range (n + 1), R f x (k / n) * b x n k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : ∀ k : ℕ, f (k / n) * b x n k = f x * b x n k
      + iteratedDerivWithin 1 f I x * (((k : ℝ) / n - x) * b x n k)
      + (1 / 2) * iteratedDerivWithin 2 f I x * (((k : ℝ) / n - x) ^ 2 * b x n k)
      + R f x (k / n) * b x n k := by
    intro k; unfold R; ring
  rw [bez_one, Finset.sum_congr rfl fun k _ => e k]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_b, S1 x hn, S2 x hn]
  field_simp
  ring

lemma rem_bound (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I) {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hR : ∀ t ∈ I, |R f x t| ≤ ε * (t - x) ^ 2 + K * (t - x) ^ 4) {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * ∑ k ∈ Finset.range (n + 1), R f x (k / n) * b x n k| ≤ ε / 4 + K / n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 : |∑ k ∈ Finset.range (n + 1), R f x (k / n) * b x n k|
      ≤ ∑ k ∈ Finset.range (n + 1), (ε * (((k : ℝ) / n - x) ^ 2 * b x n k)
          + K * (((k : ℝ) / n - x) ^ 4 * b x n k)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hkI : ((k : ℝ) / n) ∈ I := by
      have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      exact ⟨div_nonneg (Nat.cast_nonneg _) hnpos.le,
        (div_le_one hnpos).2 (by exact_mod_cast hk')⟩
    rw [abs_mul, abs_of_nonneg (b_nonneg hx n k)]
    have := mul_le_mul_of_nonneg_right (hR _ hkI) (b_nonneg hx n k)
    exact this.trans_eq (by ring)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, S2 x hn] at h1
  have h4 := S4_le x hx hn
  have hu := u_le x
  rw [abs_mul, abs_of_pos hnpos]
  calc (n : ℝ) * |∑ k ∈ Finset.range (n + 1), R f x (k / n) * b x n k|
      ≤ n * (ε * (x * (1 - x) / n)
          + K * ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * b x n k) :=
        mul_le_mul_of_nonneg_left h1 hnpos.le
    _ ≤ n * (ε * (x * (1 - x) / n) + K * (1 / n ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left h4 hK)) hnpos.le
    _ = ε * (x * (1 - x)) + K / n := by field_simp
    _ ≤ ε / 4 + K / n := by
        have := mul_le_mul_of_nonneg_left hu hε
        linarith

end Voro

theorem voronovskaja_theorem.bernstein_operators
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    let f'' : ℝ := iteratedDerivWithin 2 f I x
    Tendsto (fun (n : ℕ) => (n : ℝ) * (bezierBernstein n 1 f x - f x))
    atTop
    (𝓝 ((1 / 2) * x * (1 - x) * f'')) := by
  intro f''
  show Tendsto _ atTop (𝓝 ((1 / 2) * x * (1 - x) * iteratedDerivWithin 2 f I x))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK, hR⟩ := Voro.taylor_bound f x hx hf (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have e : (n : ℝ) * (bezierBernstein n 1 f x - f x)
      - (1 / 2) * x * (1 - x) * iteratedDerivWithin 2 f I x
      = n * ∑ k ∈ Finset.range (n + 1), Voro.R f x (k / n) * Voro.b x n k := by
    rw [Voro.key f x hn0]; ring
  rw [Real.dist_eq, e]
  have hb := Voro.rem_bound f x hx (half_pos hε).le hK hR hn0
  have hNn : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hKn : K / n < ε / 2 := by
    rw [div_lt_iff₀ hnpos]
    have h1 := (div_lt_iff₀ hε).1 hN
    have h2 : (N : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    linarith
  linarith

end VoronovskajaTypeFormula

#print axioms VoronovskajaTypeFormula.voronovskaja_theorem.bernstein_operators
