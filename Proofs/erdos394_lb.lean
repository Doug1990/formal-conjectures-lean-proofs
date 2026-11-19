import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Statement restated from FormalConjectures/ErdosProblems/394.lean (Erdos394). -/

notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

namespace LB

lemma t2_prime {p : ℕ} (hp : Nat.Prime p) : p - 1 ≤ t 2 p := by
  have hne : {m : ℕ | 0 < m ∧ p ∣ ∏ i ∈ range 2, (m + i)}.Nonempty := by
    refine ⟨p, hp.pos, ?_⟩
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    exact dvd_mul_of_dvd_left (by simp) _
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  rw [Finset.prod_range_succ, Finset.prod_range_one] at hd
  unfold t
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · have := Nat.le_of_dvd (by omega) h; omega

/-- Chebyshev-type lower bound via the central binomial coefficient (copied from erdos888). -/
lemma cheb (m : ℕ) (hm : 1 ≤ m) :
    4 ^ m ≤ (2 * m + 1) * (2 * m) ^ Nat.count Nat.Prime (2 * m + 1) := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  rw [← Nat.centralBinom_eq_two_mul_choose, ← Nat.prod_pow_factorization_centralBinom,
    Nat.count_eq_card_filter_range, ← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p _
  split_ifs with h
  · rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.pow_factorization_choose_le (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero]

lemma pi_lower (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ≤ 6 * (Nat.count Nat.Prime (n + 1) : ℝ) := by
  obtain ⟨m, hm⟩ : ∃ m, m = (n - 1) / 2 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m + 1 ≤ n := by omega
  have h2m' : 2 * m ≤ n := by omega
  have h4m : n ≤ 4 * m := by omega
  have hc := cheb m hm1
  obtain ⟨k, hkdef⟩ : ∃ k, k = Nat.count Nat.Prime (2 * m + 1) := ⟨_, rfl⟩
  rw [← hkdef] at hc
  have hk : k ≤ Nat.count Nat.Prime (n + 1) := hkdef ▸ Nat.count_monotone _ (by omega)
  have h3 : Nat.count Nat.Prime 3 = 1 := by
    simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  have hk1 : 1 ≤ k := by
    have := Nat.count_monotone Nat.Prime (show 3 ≤ 2 * m + 1 by omega)
    omega
  have hcR : (4 : ℝ) ^ m ≤ (2 * m + 1) * (2 * m) ^ k := by exact_mod_cast hc
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have hlog := Real.log_le_log hpos hcR
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hn1 : Real.log (2 * m + 1) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast h2m)
  have hn2 : Real.log (2 * m) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast h2m')
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4] at hlog
  have hl2 := Real.log_two_gt_d9
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkn : (k : ℝ) ≤ (Nat.count Nat.Prime (n + 1) : ℝ) := by exact_mod_cast hk
  have hmn : (n : ℝ) ≤ 4 * m := by exact_mod_cast h4m
  have e1 : (k : ℝ) * Real.log (2 * m) ≤ k * Real.log n :=
    mul_le_mul_of_nonneg_left hn2 (by positivity)
  have e2 : Real.log n ≤ k * Real.log n := le_mul_of_one_le_left hlogn.le hkR
  have e3 : (k : ℝ) * Real.log n ≤ (Nat.count Nat.Prime (n + 1) : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right hkn hlogn.le
  have e5 : (m : ℝ) * (2 * 0.6931471803) ≤ m * (2 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [div_le_iff₀ hlogn]
  linarith

/-- Primes in `(b, a]`. -/
def Q (a b : ℕ) : Finset ℕ := (range (a + 1)).filter (fun p => Nat.Prime p ∧ b < p)

/-- `π(a) ≤ (b + 1) + #primes in (b, a]`. -/
lemma split (a b : ℕ) :
    Nat.count Nat.Prime (a + 1) ≤ (b + 1) + (Q a b).card := by
  rw [Nat.count_eq_card_filter_range,
    ← Finset.card_filter_add_card_filter_not (s := (range (a + 1)).filter Nat.Prime)
      (fun p => p ≤ b)]
  gcongr
  · calc _ ≤ (range (b + 1)).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          omega
      _ = b + 1 := Finset.card_range _
  · intro p hp
    simp only [Q, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.1, hp.1.2, by omega⟩

/-- `π(a) ≤ π(b) + #primes in (b, a]`. -/
lemma split' (a b : ℕ) :
    Nat.count Nat.Prime (a + 1) ≤ Nat.count Nat.Prime (b + 1) + (Q a b).card := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    ← Finset.card_filter_add_card_filter_not (s := (range (a + 1)).filter Nat.Prime)
      (fun p => p ≤ b)]
  gcongr
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  · intro p hp
    simp only [Q, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.1, hp.1.2, by omega⟩

lemma pow_le (y z : ℕ) : (z + 1) ^ (Q y z).card ≤ 4 ^ y := by
  calc (z + 1) ^ (Q y z).card ≤ ∏ p ∈ Q y z, p := by
        apply Finset.pow_card_le_prod
        intro p hp
        simp only [Q, Finset.mem_filter] at hp
        omega
    _ ≤ ∏ p ∈ (range (y + 1)).filter Nat.Prime, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro p hp
          simp only [Q, Finset.mem_filter] at hp ⊢
          exact ⟨hp.1, hp.2.1⟩
        · intro p hp _
          simp only [Finset.mem_filter] at hp
          exact hp.2.one_le
    _ = primorial y := rfl
    _ ≤ 4 ^ y := primorial_le_four_pow y

lemma sum_lower (n y : ℕ) : (Q n y).card * y ≤ ∑ k ∈ Icc 1 n, t 2 k := by
  calc (Q n y).card * y ≤ ∑ p ∈ Q n y, t 2 p := by
        rw [← smul_eq_mul]
        apply Finset.card_nsmul_le_sum
        intro p hp
        simp only [Q, Finset.mem_filter] at hp
        have := t2_prime hp.2.1
        omega
    _ ≤ ∑ k ∈ Icc 1 n, t 2 k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Q, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
          have := hp.2.1.pos
          omega
        · intros; exact Nat.zero_le _

/-- `#primes in (z, y] * log n ≤ 2 y log 4` for `z = sqrt n`. -/
lemma B_bound (n y : ℕ) (hn : 1 ≤ n) :
    ((Q y (Nat.sqrt n)).card : ℝ) * Real.log n ≤ 2 * y * Real.log 4 := by
  set z := Nat.sqrt n
  set B := (Q y z).card
  have h1 : ((z + 1 : ℕ) : ℝ) ^ B ≤ (4 : ℝ) ^ y := by exact_mod_cast pow_le y z
  have hz : (0 : ℝ) < ((z + 1 : ℕ) : ℝ) := by positivity
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at h2
  have h3 : n < (z + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have h4 : (n : ℝ) ≤ ((z + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h3.le
  have h5 := Real.log_le_log (by exact_mod_cast hn) h4
  rw [Real.log_pow] at h5
  have hB : (0 : ℝ) ≤ B := by positivity
  have h6 := mul_le_mul_of_nonneg_left h5 hB
  push_cast at h2 h6 ⊢
  linarith

/-- `(sqrt n + 1) log n ≤ n / 20` for large `n`. -/
lemma z_bound (n : ℕ) (hn : 160 ^ 4 ≤ n) :
    ((Nat.sqrt n : ℝ) + 1) * Real.log n ≤ (n : ℝ) / 20 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set s := Real.sqrt n with hs
  set r := Real.sqrt s with hr
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt hn0
  have hrr : r ^ 2 = s := Real.sq_sqrt hs0
  have hnR : ((160 : ℝ) ^ 2) ^ 2 ≤ n := by
    have : ((160 ^ 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  have hs1 : (160 : ℝ) ^ 2 ≤ s := by
    rw [hs, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 160 ^ 2)]
    exact Real.sqrt_le_sqrt hnR
  have hr1 : (160 : ℝ) ≤ r := by
    rw [hr, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 160)]
    exact Real.sqrt_le_sqrt hs1
  have hn4 : (n : ℝ) = r ^ 4 := by rw [← hss, ← hrr]; ring
  have hrpos : 0 < r := by linarith
  have hlog : Real.log n = 4 * Real.log r := by
    rw [hn4, Real.log_pow]; norm_num
  have hlr := Real.log_le_sub_one_of_pos hrpos
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hz : (Nat.sqrt n : ℝ) ≤ s := Real.nat_sqrt_le_real_sqrt
  have hz2 : (Nat.sqrt n : ℝ) + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hL : Real.log n ≤ 4 * r := by rw [hlog]; linarith
  have hL0 : 0 ≤ Real.log n := by rw [hlog]; positivity
  calc ((Nat.sqrt n : ℝ) + 1) * Real.log n ≤ (2 * r ^ 2) * (4 * r) :=
        mul_le_mul hz2 hL hL0 (by positivity)
    _ = r ^ 3 * 8 := by ring
    _ ≤ r ^ 3 * (r / 20) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (n : ℝ) / 20 := by rw [hn4]; ring

end LB

theorem erdos_394.variants.lower_bound :
    (fun x ↦ x ^ 2 / Real.log x) ≪
    (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2400 ?_
  filter_upwards [eventually_ge_atTop (160 ^ 4)] with n hn
  have hfl : ⌊n⌋₊ = n := Nat.floor_natCast (R := ℕ) n
  rw [hfl]
  obtain ⟨y, hy⟩ : ∃ y, y = n / 100 := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by omega
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- counts
  have hN := LB.pi_lower n (by omega)
  have hsp := LB.split' n y
  have hA := LB.split y (Nat.sqrt n)
  have hB := LB.B_bound n y hn1
  have hz := LB.z_bound n hn
  have hS := LB.sum_lower n y
  have hy1 : n ≤ 100 * (y + 1) := by omega
  have hy2 : 100 * y ≤ n := by omega
  have hl4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  set N := Nat.count Nat.Prime (n + 1)
  set A := Nat.count Nat.Prime (y + 1)
  set P := (LB.Q n y).card
  set B := (LB.Q y (Nat.sqrt n)).card
  have hspR : (N : ℝ) ≤ A + P := by exact_mod_cast hsp
  have hAR : (A : ℝ) ≤ (Nat.sqrt n + 1 : ℝ) + B := by exact_mod_cast hA
  have hy1R : (n : ℝ) ≤ 100 * (y + 1) := by exact_mod_cast hy1
  have hy2R : 100 * (y : ℝ) ≤ n := by exact_mod_cast hy2
  have hnR : (160 : ℝ) ^ 4 ≤ n := by exact_mod_cast hn
  have hSR : (P : ℝ) * y ≤ ∑ k ∈ Icc 1 n, (t 2 k : ℝ) := by
    have : ((P * y : ℕ) : ℝ) ≤ ((∑ k ∈ Icc 1 n, t 2 k : ℕ) : ℝ) := by exact_mod_cast hS
    push_cast at this
    exact this
  have hN' : (n : ℝ) ≤ 6 * N * Real.log n := by
    rw [div_le_iff₀ hL] at hN; linarith
  have e1 := mul_le_mul_of_nonneg_right hspR hL.le
  have e2 := mul_le_mul_of_nonneg_right hAR hL.le
  have hlog4 : (y : ℝ) * Real.log 4 ≤ y * 1.3863 :=
    mul_le_mul_of_nonneg_left hl4.le (by positivity)
  have hPL : (n : ℝ) / 12 ≤ P * Real.log n := by linarith
  have hyn : (n : ℝ) / 200 ≤ y := by linarith
  have hprod := mul_le_mul hPL hyn (by positivity) (by positivity)
  have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Icc 1 n, (t 2 k : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hsum0,
    div_le_iff₀ hL]
  have e3 := mul_le_mul_of_nonneg_right hSR hL.le
  linarith

end Erdos394

#print axioms Erdos394.erdos_394.variants.lower_bound
