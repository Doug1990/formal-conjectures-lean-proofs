import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OeisA114362

open scoped Nat Real
open Filter
open Complex

/-- `t n` is used in the second conjecture. -/
noncomputable def t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

namespace P

/-- Dirichlet-coefficient combination, written for an arbitrary `f`. -/
noncomputable def E (f : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, f (i * j))
  - (∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      (f (2 * (i * j)) + f (3 * (i * j)) + f (5 * (i * j)) + f (7 * (i * j))))
  - (∑ k ∈ Finset.range 4, f (k * k))
  - (∑ k ∈ Finset.range 4,
      (f (2 * (k * k)) + f (3 * (k * k)) + f (5 * (k * k)) + f (7 * (k * k))))

lemma E_add (g h : ℕ → ℝ) : E (fun m => g m + h m) = E g + E h := by
  simp only [E, Finset.sum_add_distrib]
  ring

lemma E_low (f : ℕ → ℝ) : E (fun m => if 1 ≤ m ∧ m ≤ 10 then f m else 0) = 0 := by
  simp only [E, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

lemma E_high (h : ℕ → ℝ) (c : ℝ) (h0 : ∀ m, 0 ≤ h m) (h1 : ∀ m, h m ≤ c) :
    |E h| ≤ 625 * c := by
  have hc : 0 ≤ c := le_trans (h0 0) (h1 0)
  have A0 : 0 ≤ ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, h (i * j) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => h0 _))
  have A1 : ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, h (i * j) ≤ 121 * c := by
    calc _ ≤ ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, c :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h1 _))
      _ = 121 * c := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]; ring
  have B0 : 0 ≤ ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      (h (2 * (i * j)) + h (3 * (i * j)) + h (5 * (i * j)) + h (7 * (i * j))) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      linarith [h0 (2 * (i * j)), h0 (3 * (i * j)), h0 (5 * (i * j)), h0 (7 * (i * j))]))
  have B1 : ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      (h (2 * (i * j)) + h (3 * (i * j)) + h (5 * (i * j)) + h (7 * (i * j))) ≤ 484 * c := by
    calc _ ≤ ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, 4 * c :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
            linarith [h1 (2 * (i * j)), h1 (3 * (i * j)), h1 (5 * (i * j)), h1 (7 * (i * j))]))
      _ = 484 * c := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]; ring
  have Q0 : 0 ≤ ∑ k ∈ Finset.range 4, h (k * k) :=
    Finset.sum_nonneg (fun k _ => h0 _)
  have Q1 : ∑ k ∈ Finset.range 4, h (k * k) ≤ 4 * c := by
    calc _ ≤ ∑ k ∈ Finset.range 4, c := Finset.sum_le_sum (fun k _ => h1 _)
      _ = 4 * c := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
  have D0 : 0 ≤ ∑ k ∈ Finset.range 4,
      (h (2 * (k * k)) + h (3 * (k * k)) + h (5 * (k * k)) + h (7 * (k * k))) :=
    Finset.sum_nonneg (fun k _ => by
      linarith [h0 (2 * (k * k)), h0 (3 * (k * k)), h0 (5 * (k * k)), h0 (7 * (k * k))])
  have D1 : ∑ k ∈ Finset.range 4,
      (h (2 * (k * k)) + h (3 * (k * k)) + h (5 * (k * k)) + h (7 * (k * k))) ≤ 16 * c := by
    calc _ ≤ ∑ k ∈ Finset.range 4, 4 * c := Finset.sum_le_sum (fun k _ => by
            linarith [h1 (2 * (k * k)), h1 (3 * (k * k)), h1 (5 * (k * k)), h1 (7 * (k * k))])
      _ = 16 * c := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]; ring
  unfold E
  rw [abs_le]
  constructor <;> linarith

lemma E_split (f : ℕ → ℝ) (f0 : f 0 = 0) (c : ℝ) (hc0 : 0 ≤ c) (h0 : ∀ m, 0 ≤ f m)
    (hle : ∀ m, 11 ≤ m → f m ≤ c) : |E f| ≤ 625 * c := by
  have key : E f = E (fun m => if 1 ≤ m ∧ m ≤ 10 then f m else 0)
      + E (fun m => if 11 ≤ m then f m else 0) := by
    rw [← E_add]
    congr 1
    funext m
    by_cases h1 : 1 ≤ m ∧ m ≤ 10
    · have h2 : ¬ 11 ≤ m := by omega
      rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : 11 ≤ m
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero, show m = 0 by omega, f0]
  rw [key, E_low, zero_add]
  refine E_high _ c (fun m => ?_) (fun m => ?_)
  · by_cases hm : 11 ≤ m
    · simp [hm, h0 m]
    · simp [hm]
  · by_cases hm : 11 ≤ m
    · simp [hm, hle m hm]
    · simp [hm, hc0]

lemma E_mul (f : ℕ → ℝ) (hf : ∀ a b, f (a * b) = f a * f b) :
    E f = (1 - (f 2 + f 3 + f 5 + f 7)) * (∑ i ∈ Finset.range 11, f i) ^ 2
      - (1 + (f 2 + f 3 + f 5 + f 7)) * (∑ k ∈ Finset.range 4, f k ^ 2) := by
  have hP : ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, f i * f j
      = (∑ i ∈ Finset.range 11, f i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hB : ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      (f 2 * (f i * f j) + f 3 * (f i * f j) + f 5 * (f i * f j) + f 7 * (f i * f j))
      = (f 2 + f 3 + f 5 + f 7) * (∑ i ∈ Finset.range 11, f i) ^ 2 := by
    rw [← hP, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hQ : ∑ k ∈ Finset.range 4,
      (f 2 * (f k * f k) + f 3 * (f k * f k) + f 5 * (f k * f k) + f 7 * (f k * f k))
      = (f 2 + f 3 + f 5 + f 7) * ∑ k ∈ Finset.range 4, f k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hQ' : ∑ k ∈ Finset.range 4, f k * f k = ∑ k ∈ Finset.range 4, f k ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by ring)
  simp only [E, hf]
  rw [hP, hB, hQ, hQ']
  ring

/-- `F n k = 1 / k ^ n`. -/
noncomputable def F (n k : ℕ) : ℝ := 1 / (k : ℝ) ^ n

lemma F_mul (n : ℕ) (a b : ℕ) : F n (a * b) = F n a * F n b := by
  unfold F
  rw [Nat.cast_mul, mul_pow, div_mul_div_comm, one_mul]

lemma F_sq (n k : ℕ) : F n k ^ 2 = F (2 * n) k := by
  unfold F
  rw [div_pow, one_pow, ← pow_mul, mul_comm n 2]

lemma F_zero (n : ℕ) (hn : n ≠ 0) : F n 0 = 0 := by
  simp [F, zero_pow hn]

lemma F_nonneg (n k : ℕ) : 0 ≤ F n k := by
  unfold F; positivity

lemma F_le_one (n k : ℕ) (hn : n ≠ 0) : F n k ≤ 1 := by
  unfold F
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [zero_pow hn]
  · exact div_le_one_of_le₀ (one_le_pow₀ (Nat.one_le_cast.mpr hk)) (by positivity)

lemma F_mono (n m : ℕ) (hm : 11 ≤ m) : F n m ≤ F n 11 := by
  unfold F
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hm) n)

lemma F_tail (n m k : ℕ) (hn : 2 ≤ n) (hm : 11 ≤ m) (hk : k + 1 ≤ m) :
    F n m ≤ F n 11 * (121 * (1 / ((k : ℝ) + 1) ^ 2)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have key : 11 ^ (d + 2) * (k + 1) ^ 2 ≤ 121 * m ^ (d + 2) := by
    have h1 : 11 ^ d ≤ m ^ d := Nat.pow_le_pow_left hm d
    have h2 : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hk 2
    calc 11 ^ (d + 2) * (k + 1) ^ 2 = 121 * (11 ^ d * (k + 1) ^ 2) := by ring
      _ ≤ 121 * (m ^ d * m ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ = 121 * m ^ (d + 2) := by ring
  have key' : (11 : ℝ) ^ (d + 2) * ((k : ℝ) + 1) ^ 2 ≤ 121 * (m : ℝ) ^ (d + 2) := by
    exact_mod_cast key
  have hm0 : (0 : ℝ) < (m : ℝ) ^ (d + 2) :=
    pow_pos (by exact_mod_cast (by omega : 0 < m)) _
  have hpos : (0 : ℝ) < (11 : ℝ) ^ (d + 2) * ((k : ℝ) + 1) ^ 2 := by positivity
  have eq : (1 : ℝ) / ((11 : ℕ) : ℝ) ^ (d + 2) * (121 * (1 / ((k : ℝ) + 1) ^ 2))
      = 121 / ((11 : ℝ) ^ (d + 2) * ((k : ℝ) + 1) ^ 2) := by
    rw [Nat.cast_ofNat]
    field_simp
  unfold F
  rw [eq, div_le_div_iff₀ hm0 hpos]
  linarith

lemma zeta1 (n : ℕ) (hn : 1 < n) : (riemannZeta (n : ℂ)).re = ∑' k : ℕ, F n k := by
  rw [zeta_nat_eq_tsum_of_gt_one hn]
  have h : (fun k : ℕ => 1 / (k : ℂ) ^ n) = fun k : ℕ => ((F n k : ℝ) : ℂ) := by
    funext k; simp [F]
  rw [h, ← Complex.ofReal_tsum, Complex.ofReal_re]

lemma zeta2 (n : ℕ) (hn : 1 ≤ n) :
    (riemannZeta (2 * (n : ℂ))).re = ∑' k : ℕ, F n k ^ 2 := by
  have h2 : (2 * (n : ℂ)) = ((2 * n : ℕ) : ℂ) := by norm_num
  rw [h2, zeta1 (2 * n) (by omega)]
  exact tsum_congr (fun k => (F_sq n k).symm)

lemma alg (P R1 Q R2 S c K : ℝ) (hE : |(1 - S) * P ^ 2 - (1 + S) * Q| ≤ 625 * c)
    (hP0 : 0 ≤ P) (hP : P ≤ 11) (hR10 : 0 ≤ R1) (hR1 : R1 ≤ c * K) (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (hK : 0 ≤ K) (hR20 : 0 ≤ R2) (hR2 : R2 ≤ c * K) (hS0 : 0 ≤ S) (hS : S ≤ 4)
    (hZ1 : 1 ≤ P + R1) (hZ2 : 1 ≤ Q + R2) :
    |(1 - (Q + R2) / (P + R1) ^ 2) / (1 + (Q + R2) / (P + R1) ^ 2) - S|
      ≤ (625 + 4 * K * (22 + K) + 5 * K) * c := by
  have hZ1sq : 1 ≤ (P + R1) ^ 2 := by nlinarith
  have hD : 0 < (P + R1) ^ 2 + (Q + R2) := by linarith
  have hA : (P + R1) ^ 2 ≠ 0 := ne_of_gt (by linarith)
  have hB : (P + R1) ^ 2 + (Q + R2) ≠ 0 := ne_of_gt hD
  have key : (1 - (Q + R2) / (P + R1) ^ 2) / (1 + (Q + R2) / (P + R1) ^ 2) - S
      = ((1 - S) * (P + R1) ^ 2 - (1 + S) * (Q + R2)) / ((P + R1) ^ 2 + (Q + R2)) := by
    rw [eq_div_iff hB]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hD]
  have hR1K : R1 ≤ K := le_trans hR1 (by nlinarith)
  have hM0 : 0 ≤ 2 * P * R1 + R1 ^ 2 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP0) hR10) (sq_nonneg _)
  have hM : 2 * P * R1 + R1 ^ 2 ≤ K * (22 + K) * c := by
    nlinarith [mul_le_mul hP hR1 hR10 (by norm_num : (0:ℝ) ≤ 11),
      mul_le_mul hR1 hR1K hR10 (mul_nonneg hc0 hK)]
  have hN : (1 - S) * (P + R1) ^ 2 - (1 + S) * (Q + R2)
      = ((1 - S) * P ^ 2 - (1 + S) * Q) + (1 - S) * (2 * P * R1 + R1 ^ 2) - (1 + S) * R2 := by
    ring
  have hE' := abs_le.1 hE
  have hBd : (1 + S) * R2 ≤ 5 * (c * K) := by nlinarith
  have hB0 : 0 ≤ (1 + S) * R2 := mul_nonneg (by linarith) hR20
  have hAb : |(1 - S) * (2 * P * R1 + R1 ^ 2)| ≤ 4 * (K * (22 + K) * c) := by
    rw [abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) hM hM0 (by norm_num)
  have hA' := abs_le.1 hAb
  have hD1 : 1 ≤ (P + R1) ^ 2 + (Q + R2) := by linarith
  have hT0 : 0 ≤ (625 + 4 * K * (22 + K) + 5 * K) * c := mul_nonneg (by nlinarith) hc0
  rw [div_le_iff₀ hD]
  refine le_trans ?_ (le_mul_of_one_le_right hT0 hD1)
  rw [hN, abs_le]
  constructor <;> nlinarith

noncomputable def K0 : ℝ := ∑' k : ℕ, 121 * (1 / ((k : ℝ) + 1) ^ 2)

lemma pointwise (n : ℕ) (hn : 2 ≤ n) :
    |(1 - t n) / (1 + t n) - (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n)|
      ≤ (625 + 4 * K0 * (22 + K0) + 5 * K0) * (1 / (11:ℝ)^n) := by
  have hn0 : n ≠ 0 := by omega
  have hs : Summable (F n) := Real.summable_one_div_nat_pow.mpr (by omega)
  have hsq : Summable (fun k => F n k ^ 2) := by
    have h : Summable (F (2 * n)) := Real.summable_one_div_nat_pow.mpr (by omega)
    exact h.congr (fun k => (F_sq n k).symm)
  have hs11 : Summable (fun k => F n (k + 11)) := (summable_nat_add_iff 11).mpr hs
  have hs4 : Summable (fun k => F n (k + 4) ^ 2) := (summable_nat_add_iff 4).mpr hsq
  have e1 : (riemannZeta (n : ℂ)).re
      = (∑ k ∈ Finset.range 11, F n k) + ∑' k, F n (k + 11) := by
    rw [zeta1 n (by omega)]
    exact (hs.sum_add_tsum_nat_add 11).symm
  have e2 : (riemannZeta (2 * (n : ℂ))).re
      = (∑ k ∈ Finset.range 4, F n k ^ 2) + ∑' k, F n (k + 4) ^ 2 := by
    rw [zeta2 n (by omega)]
    exact (hsq.sum_add_tsum_nat_add 4).symm
  have hK : Summable (fun k : ℕ => 121 * (1 / ((k : ℝ) + 1) ^ 2)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (h.mul_left 121).congr (fun k => ?_)
    push_cast
    ring
  have hK0 : 0 ≤ K0 := tsum_nonneg (fun k => by positivity)
  have hR1 : ∑' k, F n (k + 11) ≤ F n 11 * K0 := by
    rw [K0, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => F_tail n (k + 11) k hn (by omega) (by omega))
      hs11 (hK.mul_left _)
  have hR2 : ∑' k, F n (k + 4) ^ 2 ≤ F n 11 * K0 := by
    rw [K0, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) hs4 (hK.mul_left _)
    rw [sq, ← F_mul]
    exact F_tail n ((k + 4) * (k + 4)) k hn (by nlinarith) (by nlinarith)
  have hR10 : 0 ≤ ∑' k, F n (k + 11) := tsum_nonneg (fun k => F_nonneg _ _)
  have hR20 : 0 ≤ ∑' k, F n (k + 4) ^ 2 := tsum_nonneg (fun k => sq_nonneg _)
  have hE := E_split (F n) (F_zero n hn0) (F n 11) (F_nonneg n 11) (fun m => F_nonneg n m)
    (fun m hm => F_mono n m hm)
  rw [E_mul (F n) (F_mul n)] at hE
  have hP0 : 0 ≤ ∑ k ∈ Finset.range 11, F n k := Finset.sum_nonneg (fun k _ => F_nonneg n k)
  have hP : ∑ k ∈ Finset.range 11, F n k ≤ 11 := by
    calc _ ≤ ∑ k ∈ Finset.range 11, (1:ℝ) := Finset.sum_le_sum (fun k _ => F_le_one n k hn0)
      _ = 11 := by norm_num
  have h1 : F n 1 = 1 := by simp [F]
  have hP1 : 1 ≤ ∑ k ∈ Finset.range 11, F n k := by
    have := Finset.single_le_sum (f := F n) (fun k _ => F_nonneg n k)
      (by simp : 1 ∈ Finset.range 11)
    linarith
  have hQ1 : 1 ≤ ∑ k ∈ Finset.range 4, F n k ^ 2 := by
    have := Finset.single_le_sum (f := fun k => F n k ^ 2) (fun k _ => sq_nonneg (F n k))
      (by simp : 1 ∈ Finset.range 4)
    simp only [h1, one_pow] at this
    linarith
  have hc0 := F_nonneg n 11
  have hc1 := F_le_one n 11 hn0
  have hS0 : 0 ≤ F n 2 + F n 3 + F n 5 + F n 7 := by
    linarith [F_nonneg n 2, F_nonneg n 3, F_nonneg n 5, F_nonneg n 7]
  have hS4 : F n 2 + F n 3 + F n 5 + F n 7 ≤ 4 := by
    linarith [F_le_one n 2 hn0, F_le_one n 3 hn0, F_le_one n 5 hn0, F_le_one n 7 hn0]
  have hS : F n 2 + F n 3 + F n 5 + F n 7
      = 1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n := by
    simp only [F, Nat.cast_ofNat]
  have hc : F n 11 = 1 / (11:ℝ)^n := by simp only [F, Nat.cast_ofNat]
  rw [t, e1, e2, ← hS, ← hc]
  exact alg _ _ _ _ _ _ _ hE hP0 hP hR10 hR1 hc0 hc1 hK0 hR20 hR2 hS0 hS4
    (by linarith) (by linarith)

end P

theorem conjecture2 :
    (fun n : ℕ => (1 - t n) / (1 + t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  refine Asymptotics.IsBigO.of_bound (625 + 4 * P.K0 * (22 + P.K0) + 5 * P.K0) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / 11 ^ n)]
    using P.pointwise n hn

end OeisA114362

#print axioms OeisA114362.conjecture2
