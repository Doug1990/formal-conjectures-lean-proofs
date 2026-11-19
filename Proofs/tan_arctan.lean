import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

open Finset

namespace Arxiv.«2607.05739»

def gaussProd (n : ℕ) : GaussianInt := ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

def A (n : ℕ) : ℤ := (gaussProd n).re

def B (n : ℕ) : ℤ := (gaussProd n).im

noncomputable def x (n : ℕ) : ℚ := (B n : ℚ) / (A n : ℚ)

def omega (n : ℕ) : ℕ := (A n).natAbs ^ 2 + (B n).natAbs ^ 2

def kernel (n : ℕ) : ℕ :=
  ∏ p ∈ (omega n).primeFactors.filter (fun p => Odd ((omega n).factorization p)), p

lemma gp_succ (n : ℕ) : gaussProd (n + 1) = gaussProd n * ⟨1, (n : ℤ) + 1⟩ := by
  unfold gaussProd
  rw [Finset.prod_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma AB_succ (n : ℕ) :
    A (n + 1) = A n - ((n : ℤ) + 1) * B n ∧ B (n + 1) = B n + ((n : ℤ) + 1) * A n := by
  unfold A B
  rw [gp_succ]
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  constructor <;> ring

lemma A_zero : A 0 = 1 := by
  unfold A gaussProd; simp

lemma B_zero : B 0 = 0 := by
  unfold B gaussProd; simp

noncomputable def θ (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.arctan k

noncomputable def r (n : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 n, Real.sqrt (1 + (k : ℝ) ^ 2)

lemma r_pos (n : ℕ) : 0 < r n := by
  unfold r
  refine Finset.prod_pos fun k _ => Real.sqrt_pos.2 ?_
  have := sq_nonneg (k : ℝ)
  linarith

lemma key (n : ℕ) : (A n : ℝ) = r n * Real.cos (θ n) ∧ (B n : ℝ) = r n * Real.sin (θ n) := by
  induction n with
  | zero => simp [A_zero, B_zero, r, θ]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := AB_succ n
    obtain ⟨ih1, ih2⟩ := ih
    have hθ : θ (n + 1) = θ n + Real.arctan ((n : ℝ) + 1) := by
      unfold θ
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast; rfl
    have hr : r (n + 1) = r n * Real.sqrt (1 + ((n : ℝ) + 1) ^ 2) := by
      unfold r
      rw [Finset.prod_Icc_succ_top (by omega)]
      push_cast; rfl
    have hs : 0 < Real.sqrt (1 + ((n : ℝ) + 1) ^ 2) := by
      apply Real.sqrt_pos.2
      have := sq_nonneg ((n : ℝ) + 1)
      linarith
    rw [hθ, hr, Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan]
    constructor
    · rw [h1]; push_cast; rw [ih1, ih2]
      field_simp
    · rw [h2]; push_cast; rw [ih1, ih2]
      field_simp

theorem x_eq_tan_sum_arctan (n : ℕ) (hn : 1 ≤ n) :
    (x n : ℝ) = Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) := by
  obtain ⟨h1, h2⟩ := key n
  have hr := (r_pos n).ne'
  change (x n : ℝ) = Real.tan (θ n)
  rw [Real.tan_eq_sin_div_cos, x]
  push_cast
  rw [h1, h2, mul_div_mul_left _ _ hr]

lemma omega_eq {n : ℕ} (hA : A n ≠ 0) {m : ℤ} (hx : x n = (m : ℚ)) :
    omega n = (A n).natAbs ^ 2 * (1 + m.natAbs ^ 2) := by
  have hA' : (A n : ℚ) ≠ 0 := by exact_mod_cast hA
  have hB : B n = m * A n := by
    have : (B n : ℚ) = m * A n := by
      rw [x, div_eq_iff hA'] at hx; exact hx
    exact_mod_cast this
  unfold omega
  rw [hB, Int.natAbs_mul]
  ring

lemma kernel_dvd {a t : ℕ} (ha : a ≠ 0) (ht : t ≠ 0) :
    (∏ p ∈ (a ^ 2 * t).primeFactors.filter (fun p => Odd ((a ^ 2 * t).factorization p)), p)
      ∣ t := by
  refine Finset.prod_primes_dvd t (fun p hp => ?_) (fun p hp => ?_)
  · rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact hp.1.1.prime
  · rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hp, -, -⟩, hodd⟩ := hp
    rw [Nat.factorization_mul (pow_ne_zero 2 ha) ht, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hodd
    have hpos : 0 < t.factorization p := by
      rcases Nat.eq_zero_or_pos (t.factorization p) with h | h
      · rw [h] at hodd
        exact absurd hodd (by simp)
      · exact h
    exact Nat.dvd_of_factorization_pos hpos.ne'

theorem kernel_dvd_of_eq_intCast {n : ℕ} (hn : 1 ≤ n) (hA : A n ≠ 0) {m : ℤ}
    (hx : x n = (m : ℚ)) :
    ((kernel n : ℤ) ∣ (1 + m ^ 2)) ∧
      (1 < kernel n → Real.sqrt ((kernel n : ℝ) - 1) ≤ |(m : ℝ)|) := by
  have ht : (1 + m.natAbs ^ 2) ≠ 0 := by omega
  have hd : kernel n ∣ 1 + m.natAbs ^ 2 := by
    unfold kernel
    rw [omega_eq hA hx]
    exact kernel_dvd (Int.natAbs_ne_zero.2 hA) ht
  have hdZ : (kernel n : ℤ) ∣ 1 + m ^ 2 := by
    have := Int.natCast_dvd_natCast.2 hd
    push_cast at this
    rwa [sq_abs] at this
  refine ⟨hdZ, fun _ => ?_⟩
  have hle : (kernel n : ℤ) ≤ 1 + m ^ 2 :=
    Int.le_of_dvd (by positivity) hdZ
  have hleR : (kernel n : ℝ) - 1 ≤ (m : ℝ) ^ 2 := by
    have : ((kernel n : ℤ) : ℝ) ≤ ((1 + m ^ 2 : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at this
    linarith
  calc Real.sqrt ((kernel n : ℝ) - 1) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt hleR
    _ = |(m : ℝ)| := Real.sqrt_sq_eq_abs _

#print axioms x_eq_tan_sum_arctan
#print axioms kernel_dvd_of_eq_intCast

end Arxiv.«2607.05739»
