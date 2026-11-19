import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Common

namespace Nat

/-- restated from FormalConjecturesForMathlib/Data/Nat/Full.lean -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

/-- restated from FormalConjecturesForMathlib/Data/Nat/Full.lean -/
abbrev Powerful : ℕ → Prop := (2).Full

end Nat

open Filter Asymptotics Real

namespace PowerfulNumbersDensity

/-- $Q(x)$ is the number of powerful integers $n$ with $1 \le n \le x$. -/
noncomputable abbrev Q (x : ℝ) : ℕ := {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard

/-- The leading constant $\zeta(3/2)/\zeta(3) = 2.173\ldots$ -/
noncomputable abbrev A : ℝ := (riemannZeta (3 / 2)).re / (riemannZeta 3).re

namespace PND

theorem sqf_unique {c b c' b' : ℕ} (hb : Squarefree b) (hb' : Squarefree b')
    (hc : c ≠ 0) (h : c ^ 2 * b = c' ^ 2 * b') : b = b' ∧ c = c' := by
  have hb0 := hb.ne_zero
  have hb0' := hb'.ne_zero
  have hne : c ^ 2 * b ≠ 0 := Nat.mul_ne_zero (pow_ne_zero 2 hc) hb0
  have hc' : c' ≠ 0 := by
    rintro rfl
    apply hne
    rw [h]
    simp
  have key : ∀ {c b : ℕ}, Squarefree b → c ≠ 0 → ∀ p,
      b.factorization p = (c ^ 2 * b).factorization p % 2 := by
    intro c b hb hc p
    rw [Nat.factorization_mul (pow_ne_zero 2 hc) hb.ne_zero, Nat.factorization_pow]
    have := hb.natFactorization_le_one p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    omega
  have hbb : b = b' := Nat.eq_of_factorization_eq hb0 hb0' (fun p => by
    rw [key hb hc p, key hb' hc' p, h])
  subst hbb
  refine ⟨rfl, ?_⟩
  have h2 : c ^ 2 = c' ^ 2 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb0) h
  rcases lt_trichotomy c c' with hl | hl | hl
  · have := Nat.pow_lt_pow_left hl two_ne_zero
    omega
  · exact hl
  · have := Nat.pow_lt_pow_left hl two_ne_zero
    omega

theorem powerful_mk {a b : ℕ} : (a ^ 2 * b ^ 3).Powerful := by
  unfold Nat.Powerful Nat.Full
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 2) _
  · have h1 : p ^ 2 ∣ b ^ 3 :=
      (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 3)
    exact Dvd.dvd.mul_left h1 _

theorem powerful_decomp {n : ℕ} (hn : 0 < n) (hP : n.Powerful) :
    ∃ a b, 0 < a ∧ Squarefree b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨b, c, hb0, hc0, hcb, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hdvd : b ∣ c := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpb := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        refine ⟨hpp, ?_, hn.ne'⟩
        rw [← hcb]
        exact Dvd.dvd.mul_left hpb _
      have h2 : p ^ 2 ∣ c ^ 2 * b := by
        rw [hcb]
        exact hP p hpn
      by_contra hpc
      have hcop : Nat.Coprime (p ^ 2) (c ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpc)
      have h3 : p ^ 2 ∣ b := hcop.dvd_of_dvd_mul_left h2
      have := hsq p (by rw [← sq]; exact h3)
      exact hpp.one_lt.ne' (Nat.isUnit_iff.1 this)
  obtain ⟨a, rfl⟩ := hdvd
  refine ⟨a, b, ?_, hsq, ?_⟩
  · rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      simp at hc0
    · exact h
  · rw [← hcb]
    ring

theorem Q_eq {x : ℝ} (hx : 0 ≤ x) :
    Q x = ∑ b ∈ Finset.Icc 1 ⌊x⌋₊, if Squarefree b then Nat.sqrt (⌊x⌋₊ / b ^ 3) else 0 := by
  set N := ⌊x⌋₊ with hN
  set T := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p : ℕ × ℕ => Squarefree p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ N) with hT
  have hset : {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x} =
      ↑(T.image (fun p : ℕ × ℕ => p.1 ^ 2 * p.2 ^ 3)) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, hT,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.exists]
    constructor
    · rintro ⟨hn, hP, hnx⟩
      have hnN : n ≤ N := Nat.le_floor hnx
      obtain ⟨a, b, ha, hb, rfl⟩ := powerful_decomp hn hP
      have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb.ne_zero
      have h1 : a ≤ a ^ 2 * b ^ 3 :=
        le_trans (Nat.le_self_pow two_ne_zero a) (Nat.le_mul_of_pos_right _ (pow_pos hb1 3))
      have h2 : b ≤ a ^ 2 * b ^ 3 :=
        le_trans (Nat.le_self_pow (by norm_num) b) (Nat.le_mul_of_pos_left _ (pow_pos ha 2))
      exact ⟨a, b, ⟨⟨⟨ha, by omega⟩, ⟨hb1, by omega⟩⟩, hb, hnN⟩, rfl⟩
    · rintro ⟨a, b, ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, hb, hle⟩, rfl⟩
      refine ⟨Nat.mul_pos (pow_pos ha1 2) (pow_pos hb1 3), powerful_mk, ?_⟩
      exact (Nat.le_floor_iff hx).1 hle
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 ^ 2 * p.2 ^ 3) ↑T := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hab hab'
    simp only at heq
    have e1 : (a * b) ^ 2 * b = (a' * b') ^ 2 * b' := by
      calc (a * b) ^ 2 * b = a ^ 2 * b ^ 3 := by ring
        _ = a' ^ 2 * b' ^ 3 := heq
        _ = (a' * b') ^ 2 * b' := by ring
    obtain ⟨hbb, hab2⟩ := sqf_unique hab.2.1 hab'.2.1
      (Nat.mul_ne_zero (by omega) (by omega)) e1
    subst hbb
    have : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) hab2
    subst this
    rfl
  show Set.ncard {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x} = _
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hT, Finset.card_filter,
    Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_Icc] at hb
  by_cases hsq : Squarefree b
  · simp only [hsq, true_and, if_true]
    rw [← Finset.card_filter]
    have hb3 : 0 < b ^ 3 := pow_pos hb.1 3
    have : (Finset.Icc 1 N).filter (fun a => a ^ 2 * b ^ 3 ≤ N) =
        Finset.Icc 1 (Nat.sqrt (N / b ^ 3)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hb3]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        have : a ≤ a ^ 2 * b ^ 3 :=
          le_trans (Nat.le_self_pow two_ne_zero a) (Nat.le_mul_of_pos_right _ hb3)
        omega
    rw [this, Nat.card_Icc]
    omega
  · simp [hsq]

/-- the squarefree weights -/
noncomputable def s (b : ℕ) : ℝ := if Squarefree b then 1 / (b : ℝ) ^ (3 / 2 : ℝ) else 0

theorem rpow_three_halves (t : ℝ) (ht : 0 ≤ t) : t ^ (3 / 2 : ℝ) = t * √t := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' ht (by norm_num), Real.rpow_one]

theorem s_nonneg (b : ℕ) : 0 ≤ s b := by
  unfold s
  split_ifs
  · exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg b) _)
  · exact le_refl 0

theorem s_le (b : ℕ) : s b ≤ 1 / (b : ℝ) ^ (3 / 2 : ℝ) := by
  unfold s
  split_ifs
  · exact le_refl _
  · exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg b) _)

theorem summ32 : Summable (fun b : ℕ => 1 / (b : ℝ) ^ (3 / 2 : ℝ)) :=
  Real.summable_one_div_nat_rpow.2 (by norm_num)

theorem s_summable : Summable s :=
  Summable.of_nonneg_of_le s_nonneg s_le summ32

theorem term_bounds {x : ℝ} (hx : 0 ≤ x) {b : ℕ} (hb : 1 ≤ b) :
    ((Nat.sqrt (⌊x⌋₊ / b ^ 3) : ℕ) : ℝ) * (b * √b) ≤ √x ∧
    √x < (((Nat.sqrt (⌊x⌋₊ / b ^ 3) : ℕ) : ℝ) + 1) * (b * √b) := by
  set N := ⌊x⌋₊ with hN
  set q := Nat.sqrt (N / b ^ 3) with hq
  have hb3 : 0 < b ^ 3 := pow_pos hb 3
  have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsq : ∀ t : ℝ, (t * (b * √b)) ^ 2 = t ^ 2 * (b : ℝ) ^ 3 := by
    intro t
    have := Real.sq_sqrt hbR
    calc (t * (b * √b)) ^ 2 = t ^ 2 * (b : ℝ) ^ 2 * (√b) ^ 2 := by ring
      _ = t ^ 2 * (b : ℝ) ^ 3 := by rw [this]; ring
  have hq1 : q ^ 2 * b ^ 3 ≤ N := (Nat.le_div_iff_mul_le hb3).1 (Nat.sqrt_le' (N / b ^ 3))
  have hq2 : N + 1 ≤ (q + 1) ^ 2 * b ^ 3 := by
    have h1 : N / b ^ 3 < (q + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h2 : N < b ^ 3 * (N / b ^ 3 + 1) := Nat.lt_mul_div_succ N hb3
    calc N + 1 ≤ b ^ 3 * (N / b ^ 3 + 1) := h2
      _ ≤ b ^ 3 * (q + 1) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = (q + 1) ^ 2 * b ^ 3 := mul_comm _ _
  have hxN : (N : ℝ) ≤ x := Nat.floor_le hx
  have hxN' : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hq1R : (q : ℝ) ^ 2 * (b : ℝ) ^ 3 ≤ x := by
    have : ((q ^ 2 * b ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq1
    push_cast at this
    linarith
  have hq2R : x < ((q : ℝ) + 1) ^ 2 * (b : ℝ) ^ 3 := by
    have : ((N + 1 : ℕ) : ℝ) ≤ (((q + 1) ^ 2 * b ^ 3 : ℕ) : ℝ) := by exact_mod_cast hq2
    push_cast at this
    linarith
  have hpos : 0 ≤ (b : ℝ) * √b := mul_nonneg hbR (Real.sqrt_nonneg _)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  constructor
  · have h := Real.sqrt_le_sqrt hq1R
    rw [← hsq (q : ℝ), Real.sqrt_sq (mul_nonneg hq0 hpos)] at h
    exact h
  · have h := Real.sqrt_lt_sqrt hx hq2R
    rw [← hsq ((q : ℝ) + 1), Real.sqrt_sq (mul_nonneg (by linarith) hpos)] at h
    exact h

theorem step_ineq {t : ℝ} (ht : 1 ≤ t) :
    1 / ((t + 1) * √(t + 1)) ≤ 2 / √t - 2 / √(t + 1) := by
  have ha0 : 0 < √t := Real.sqrt_pos.2 (by linarith)
  have hac : √t < √(t + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have ha2 : (√t) ^ 2 = t := Real.sq_sqrt (by linarith)
  have hc2 : (√(t + 1)) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  generalize √t = a at ha0 hac ha2 ⊢
  generalize √(t + 1) = c at hac hc2 ⊢
  have hc0 : 0 < c := by linarith
  rw [← hc2, div_sub_div _ _ ha0.ne' hc0.ne',
    div_le_div_iff₀ (mul_pos (pow_pos hc0 2) hc0) (mul_pos ha0 hc0)]
  have e : c ^ 2 * (c ^ 2 - a ^ 2 - 1) = 0 := by rw [ha2, hc2]; ring
  nlinarith [mul_nonneg hc0.le (sub_pos.2 hac).le,
    mul_nonneg (sq_nonneg c) (sq_nonneg (c - a))]

theorem tail_finite (K : ℕ) (hK : 1 ≤ K) (m : ℕ) :
    ∑ i ∈ Finset.range m, 1 / (((i + (K + 1) : ℕ) : ℝ) * √((i + (K + 1) : ℕ) : ℝ)) ≤
      2 / √(K : ℝ) - 2 / √((m + K : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have := step_ineq (t := ((m + K : ℕ) : ℝ)) (by push_cast; linarith)
    have e1 : ((m + (K + 1) : ℕ) : ℝ) = ((m + K : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((m + 1 + K : ℕ) : ℝ) = ((m + K : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

theorem tail_bound (K : ℕ) (hK : 1 ≤ K) :
    ∑' i, s (i + (K + 1)) ≤ 2 / √(K : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun i => s_nonneg _) (fun m => ?_)
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_trans (tail_finite K hK m) ?_)
  · refine le_trans (s_le _) (le_of_eq ?_)
    rw [rpow_three_halves _ (Nat.cast_nonneg _)]
  · have : 0 ≤ 2 / √((m + K : ℕ) : ℝ) := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    linarith

theorem S_split (K : ℕ) :
    ∑' b, s b = ∑ b ∈ Finset.Icc 1 K, s b + ∑' i, s (i + (K + 1)) := by
  rw [← s_summable.sum_add_tsum_nat_add (K + 1)]
  congr 1
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have : s 0 = 0 := by simp [s]
  rw [this, zero_add]
  congr 1

theorem Q_upper {x : ℝ} (hx : 0 ≤ x) : (Q x : ℝ) ≤ √x * ∑' b, s b := by
  rw [Q_eq hx, Nat.cast_sum]
  calc (∑ b ∈ Finset.Icc 1 ⌊x⌋₊,
        ((if Squarefree b then Nat.sqrt (⌊x⌋₊ / b ^ 3) else 0 : ℕ) : ℝ))
      ≤ ∑ b ∈ Finset.Icc 1 ⌊x⌋₊, √x * s b := Finset.sum_le_sum (fun b hb => ?_)
    _ = √x * ∑ b ∈ Finset.Icc 1 ⌊x⌋₊, s b := by rw [Finset.mul_sum]
    _ ≤ √x * ∑' b, s b :=
        mul_le_mul_of_nonneg_left (s_summable.sum_le_tsum _ (fun b _ => s_nonneg b))
          (Real.sqrt_nonneg x)
  rw [Finset.mem_Icc] at hb
  unfold s
  split_ifs with hsq
  · have h := (term_bounds hx hb.1).1
    rw [rpow_three_halves _ (Nat.cast_nonneg _)]
    have hpos : 0 < (b : ℝ) * √b :=
      mul_pos (Nat.cast_pos.2 hb.1) (Real.sqrt_pos.2 (Nat.cast_pos.2 hb.1))
    rw [mul_one_div, le_div_iff₀ hpos]
    exact h
  · simp

theorem Q_lower {x : ℝ} (hx : 0 ≤ x) (K : ℕ) (hKN : K ≤ ⌊x⌋₊) :
    √x * ∑ b ∈ Finset.Icc 1 K, s b - K ≤ (Q x : ℝ) := by
  rw [Q_eq hx, Nat.cast_sum]
  have hsub : Finset.Icc 1 K ⊆ Finset.Icc 1 ⌊x⌋₊ := Finset.Icc_subset_Icc le_rfl hKN
  calc √x * ∑ b ∈ Finset.Icc 1 K, s b - K = ∑ b ∈ Finset.Icc 1 K, (√x * s b - 1) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
          nsmul_eq_mul, mul_one]
        simp
    _ ≤ ∑ b ∈ Finset.Icc 1 K,
          ((if Squarefree b then Nat.sqrt (⌊x⌋₊ / b ^ 3) else 0 : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun b hb => ?_)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  rw [Finset.mem_Icc] at hb
  unfold s
  split_ifs with hsq
  · have h := (term_bounds hx hb.1).2
    rw [rpow_three_halves _ (Nat.cast_nonneg _)]
    have hpos : 0 < (b : ℝ) * √b :=
      mul_pos (Nat.cast_pos.2 hb.1) (Real.sqrt_pos.2 (Nat.cast_pos.2 hb.1))
    rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hpos]
    linarith
  · norm_num

theorem zeta_re {r : ℝ} (hr : 1 < r) :
    (riemannZeta (r : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ r := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hr)]
  have : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ (r : ℂ) = ((1 / (n : ℝ) ^ r : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

theorem supp_facts {b c : ℕ} (h : s b * (1 / (c : ℝ) ^ (3 : ℝ)) ≠ 0) :
    Squarefree b ∧ c ≠ 0 := by
  constructor
  · by_contra hb
    apply h
    simp [s, hb]
  · rintro rfl
    apply h
    simp

theorem prod_identity :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) = (∑' b, s b) * ∑' c : ℕ, 1 / (c : ℝ) ^ (3 : ℝ) := by
  have ht : Summable (fun c : ℕ => 1 / (c : ℝ) ^ (3 : ℝ)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  have ht0 : ∀ c : ℕ, 0 ≤ 1 / (c : ℝ) ^ (3 : ℝ) :=
    fun c => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg c) _)
  rw [tsum_mul_tsum_of_summable_norm
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun b => le_of_eq (Real.norm_of_nonneg (s_nonneg b))) s_summable)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun c => le_of_eq (Real.norm_of_nonneg (ht0 c))) ht)]
  refine tsum_eq_tsum_of_ne_zero_bij (fun p => p.1.2 ^ 2 * p.1.1) ?_ ?_ ?_
  · rintro ⟨⟨b, c⟩, hbc⟩ ⟨⟨b', c'⟩, hbc'⟩ heq
    obtain ⟨hb, hc⟩ := supp_facts (Function.mem_support.1 hbc)
    obtain ⟨hb', hc'⟩ := supp_facts (Function.mem_support.1 hbc')
    obtain ⟨h1, h2⟩ := sqf_unique hb hb' hc heq
    subst h1
    subst h2
    rfl
  · intro n hn
    rw [Function.mem_support] at hn
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hn
      · exact h
    obtain ⟨b, c, hb0, hc0, hcb, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn0
    refine ⟨⟨(b, c), ?_⟩, hcb⟩
    rw [Function.mem_support]
    refine mul_ne_zero ?_ (one_div_ne_zero (Real.rpow_pos_of_pos (Nat.cast_pos.2 hc0) _).ne')
    rw [s, if_pos hsq]
    exact one_div_ne_zero (Real.rpow_pos_of_pos (Nat.cast_pos.2 hb0) _).ne'
  · rintro ⟨⟨b, c⟩, hbc⟩
    obtain ⟨hb, hc⟩ := supp_facts (Function.mem_support.1 hbc)
    show 1 / (((c ^ 2 * b : ℕ) : ℝ)) ^ (3 / 2 : ℝ) = s b * (1 / (c : ℝ) ^ (3 : ℝ))
    rw [s, if_pos hb]
    push_cast
    rw [Real.mul_rpow (sq_nonneg _) (Nat.cast_nonneg b)]
    have : ((c : ℝ) ^ 2) ^ (3 / 2 : ℝ) = (c : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg c)]
      norm_num
    rw [this]
    ring

theorem A_eq : A = ∑' b, s b := by
  have h32 := zeta_re (r := 3 / 2) (by norm_num)
  have h3 := zeta_re (r := 3) (by norm_num)
  have e1 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by norm_num
  have e2 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  rw [e1] at h32
  rw [e2] at h3
  show (riemannZeta (3 / 2)).re / (riemannZeta 3).re = _
  rw [h32, h3, prod_identity]
  have hsum : Summable (fun c : ℕ => 1 / (c : ℝ) ^ (3 : ℝ)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  have hpos : 0 < ∑' c : ℕ, 1 / (c : ℝ) ^ (3 : ℝ) := by
    have h := hsum.sum_le_tsum {1} (fun c _ => div_nonneg zero_le_one
      (Real.rpow_nonneg (Nat.cast_nonneg c) _))
    simp only [Finset.sum_singleton, Nat.cast_one, Real.one_rpow, div_one] at h
    linarith
  field_simp

theorem main_bound {x : ℝ} (hx : 1 ≤ x) :
    ‖(Q x : ℝ) - A * x ^ ((1 : ℝ) / 2)‖ ≤ 4 * ‖x ^ ((1 : ℝ) / 3)‖ := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt : x ^ ((1 : ℝ) / 2) = √x := (Real.sqrt_eq_rpow x).symm
  have hy1 : 1 ≤ x ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx (by norm_num)
  have hyx : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [A_eq, hsqrt, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 3))]
  generalize x ^ ((1 : ℝ) / 3) = y at hy1 hyx ⊢
  have hy0 : 0 ≤ y := by linarith
  have hsx : √x = y * √y := by
    rw [← hyx, show y ^ 3 = y ^ 2 * y by ring, Real.sqrt_mul (sq_nonneg y),
      Real.sqrt_sq hy0]
  rw [abs_le]
  have hup := Q_upper hx0
  set K := ⌊y⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy1)
  have hKy : (K : ℝ) ≤ y := Nat.floor_le hy0
  have hKy2 : y < (K : ℝ) + 1 := Nat.lt_floor_add_one y
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hyy : y ≤ x := by
    rw [← hyx]
    have h1 : y ≤ y ^ 2 := by nlinarith
    have h2 : y ^ 2 ≤ y ^ 3 := by nlinarith
    linarith
  have hKN : K ≤ ⌊x⌋₊ := Nat.le_floor (by linarith)
  have hlow := Q_lower hx0 K hKN
  have hsplit := S_split K
  have htail := tail_bound K hK1
  have hK0 : 0 < √(K : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsy : 2 * √y ≤ 3 * √(K : ℝ) := by
    have h4 : 4 * y ≤ 9 * (K : ℝ) := by linarith
    nlinarith [Real.sq_sqrt hy0, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ K),
      Real.sqrt_nonneg y, Real.sqrt_nonneg (K : ℝ)]
  have key : √x * (2 / √(K : ℝ)) ≤ 3 * y := by
    rw [hsx, show y * √y * (2 / √(K : ℝ)) = y * (2 * √y / √(K : ℝ)) by ring,
      show 3 * y = y * 3 by ring]
    apply mul_le_mul_of_nonneg_left _ hy0
    rw [div_le_iff₀ hK0]
    linarith
  have h1 : √x * ∑' b, s b ≤ √x * ∑ b ∈ Finset.Icc 1 K, s b + √x * (2 / √(K : ℝ)) := by
    rw [hsplit, mul_add]
    have := mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg x)
    linarith
  constructor
  · linarith
  · linarith

end PND

theorem asymptotic_erdos_szekeres :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 3) :=
  Asymptotics.IsBigO.of_bound 4 (Filter.eventually_atTop.2 ⟨1, fun _ hx => PND.main_bound hx⟩)

end PowerfulNumbersDensity

#print axioms PowerfulNumbersDensity.asymptotic_erdos_szekeres
