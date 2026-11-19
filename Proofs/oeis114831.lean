import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace OeisA114831

open Filter Real Topology

noncomputable def a : ℕ → ℕ
| 0 => 0 -- Dummy value, sequence starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let an1 : ℕ := a (n + 2)
  let an2 : ℕ := a (n + 1)
  let num : ℚ := (2 * an1 * an2 : ℕ).cast
  let den : ℚ := (an1 + an2 : ℕ).cast
  let harmonicTermFloor : ℕ := Int.toNat (num / den).floor
  an1 + harmonicTermFloor

namespace P

lemma a1 : a 1 = 1 := by rw [a]

lemma a2 : a 2 = 2 := by rw [a]

lemma rec (n : ℕ) :
    a (n + 3) = a (n + 2) + 2 * a (n + 2) * a (n + 1) / (a (n + 2) + a (n + 1)) := by
  have h : a (n + 3) = a (n + 2) +
      Int.toNat ⌊((2 * a (n + 2) * a (n + 1) : ℕ) : ℚ) / ((a (n + 2) + a (n + 1) : ℕ) : ℚ)⌋ := by
    rw [a]; rfl
  rw [h, Rat.floor_natCast_div_natCast, ← Int.natCast_div, Int.toNat_natCast]

lemma grow (n : ℕ) : n + 1 ≤ a (n + 1) ∧ n + 2 ≤ a (n + 2) := by
  induction n with
  | zero => exact ⟨by simp [a1], by simp [a2]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show n + 3 ≤ a (n + 3)
    rw [rec n]
    have hX := ih.2
    have hY := ih.1
    generalize a (n + 2) = X at *
    generalize a (n + 1) = Y at *
    have : 1 ≤ 2 * X * Y / (X + Y) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    generalize 2 * X * Y / (X + Y) = t at *
    omega

lemma step (x y q s : ℝ) (hx : 0 < x) (hy : 0 < y) (hs : s * s = 3) (hs0 : 0 ≤ s)
    (h1 : q * (x + y) ≤ 2 * x * y) (h2 : 2 * x * y < (q + 1) * (x + y)) :
    |(x + q) / x - s| ≤ 3 / 4 * |x / y - s| + 1 / x := by
  have hxy : 0 < x + y := by linarith
  have hs1 : s ≤ 7 / 4 := by nlinarith
  have hs2 : 1 ≤ s := by nlinarith
  have hden : 0 < x * (x + y) := mul_pos hx hxy
  have key : x + 3 * y - s * x - s * y = (1 - s) * (x - s * y) := by
    linear_combination (-y) * hs
  have e1 : (x + q) / x - s = (q * (x + y) - 2 * x * y) / (x * (x + y)) +
      (x + 3 * y - s * x - s * y) / (x + y) := by
    rw [div_add_div _ _ hden.ne' hxy.ne', eq_div_iff (mul_ne_zero hden.ne' hxy.ne'),
      div_sub' hx.ne']
    rw [div_mul_eq_mul_div, div_eq_iff hx.ne']
    ring
  have e2 : x / y - s = (x - s * y) / y := by
    rw [sub_div, mul_div_assoc, div_self hy.ne', mul_one]
  rw [e1, key, e2]
  have hA : |(q * (x + y) - 2 * x * y) / (x * (x + y))| ≤ 1 / x := by
    rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hx]
    have hN : |q * (x + y) - 2 * x * y| ≤ x + y := abs_le.2 ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_right hN hx.le
    linarith
  have hB : |(1 - s) * (x - s * y) / (x + y)| ≤ 3 / 4 * |(x - s * y) / y| := by
    have hD := abs_nonneg (x - s * y)
    rw [abs_div, abs_div, abs_mul, abs_of_pos hxy, abs_of_pos hy,
      abs_of_nonpos (by linarith : 1 - s ≤ 0), ← mul_div_assoc, div_le_div_iff₀ hxy hy]
    have h5 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 7 / 4 - s) hD) hy.le
    have h6 := mul_nonneg hD hx.le
    linarith
  generalize (q * (x + y) - 2 * x * y) / (x * (x + y)) = A at *
  generalize (1 - s) * (x - s * y) / (x + y) = B at *
  rw [abs_le]
  constructor <;> linarith [le_abs_self A, neg_abs_le A, le_abs_self B, neg_abs_le B]

lemma conv (e d : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hd : Tendsto d atTop (𝓝 0))
    (hrec : ∀ n, e (n + 1) ≤ 3 / 4 * e n + d n) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hd (ε / 8) (by linarith)
  have hk : ∀ k, e (N + k) ≤ (3 / 4 : ℝ) ^ k * e N + ε / 2 := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero, pow_zero, one_mul]; linarith
    | succ k ih =>
      have h1 : e (N + (k + 1)) ≤ 3 / 4 * e (N + k) + d (N + k) := hrec (N + k)
      have h2 : d (N + k) < ε / 8 := by
        have := hN (N + k) (by omega)
        rw [Real.dist_eq, sub_zero] at this
        exact lt_of_le_of_lt (le_abs_self _) this
      have h3 : (3 / 4 : ℝ) ^ (k + 1) * e N = 3 / 4 * ((3 / 4 : ℝ) ^ k * e N) := by ring
      rw [h3]
      linarith
  have hp : Tendsto (fun k => (3 / 4 : ℝ) ^ k * e N) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 3 / 4)
      (by norm_num)).mul_const (e N)
    rw [zero_mul] at this
    exact this
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hp (ε / 2) (by linarith)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  have h4 := hK k (by omega)
  rw [Real.dist_eq, sub_zero] at h4 ⊢
  rw [abs_of_nonneg (he _)]
  have := hk k
  have := le_abs_self ((3 / 4 : ℝ) ^ k * e N)
  linarith


end P

open P in
theorem conjecture3 :
    Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds (Real.sqrt 3)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1, tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine conv _ (fun n => 1 / (a (n + 2) : ℝ)) (fun n => abs_nonneg _) ?_ ?_
  · refine squeeze_zero (fun n => ?_) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    · exact one_div_nonneg.2 (Nat.cast_nonneg _)
    have := (grow n).2
    have h : (n : ℝ) + 1 ≤ a (n + 2) := by exact_mod_cast (by omega : n + 1 ≤ a (n + 2))
    exact one_div_le_one_div_of_le (by linarith) h
  · intro n
    show |(a (n + 3) : ℝ) / a (n + 2) - Real.sqrt 3| ≤
      3 / 4 * |(a (n + 2) : ℝ) / a (n + 1) - Real.sqrt 3| + 1 / a (n + 2)
    rw [P.rec n]
    obtain ⟨hY, hX⟩ := grow n
    generalize a (n + 2) = X at *
    generalize a (n + 1) = Y at *
    have hS : 0 < X + Y := by omega
    have hdm := Nat.div_add_mod (2 * X * Y) (X + Y)
    have hml := Nat.mod_lt (2 * X * Y) hS
    generalize 2 * X * Y / (X + Y) = q at *
    generalize 2 * X * Y % (X + Y) = r at *
    have e1 : ((X : ℝ) + Y) * q + r = 2 * X * Y := by exact_mod_cast hdm
    have hr : (r : ℝ) < X + Y := by exact_mod_cast hml
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    push_cast
    exact step (X : ℝ) Y q (Real.sqrt 3) (by exact_mod_cast (by omega : 0 < X))
      (by exact_mod_cast (by omega : 0 < Y)) (Real.mul_self_sqrt (by norm_num))
      (Real.sqrt_nonneg _) (by linarith) (by linarith)

end OeisA114831

#print axioms OeisA114831.conjecture3
