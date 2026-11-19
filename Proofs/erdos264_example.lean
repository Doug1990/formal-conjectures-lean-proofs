import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

open Filter

namespace Erdos264

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop := ∀ b : ℕ → ℤ,
  BddAbove (Set.range b) → BddBelow (Set.range b) →
  0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → 0 ∉ Set.range b →
  Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))

namespace Ex

def x (n : ℕ) : ℤ := 2 ^ (2 ^ n)

lemma x_succ (n : ℕ) : x (n + 1) = x n ^ 2 := by
  unfold x; rw [pow_succ, pow_mul]

lemma x_ge_two (n : ℕ) : 2 ≤ x n := by
  unfold x
  calc (2:ℤ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (2 ^ n) := pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow

lemma xR_ge_two (n : ℕ) : (2:ℝ) ≤ x n := by exact_mod_cast x_ge_two n

lemma lt_x (n : ℕ) : (n : ℤ) < x n := by
  unfold x
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : (2:ℤ) ^ n ≤ 2 ^ (2 ^ n) := pow_le_pow_right₀ (by norm_num) h1.le
  have h3 : (n:ℤ) < 2 ^ n := by exact_mod_cast h1
  linarith

lemma X_mul (N n : ℕ) : 2 ^ n * (x N : ℝ) ≤ x (n + N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 := xR_ge_two (n + N)
    have hx : (x (n + 1 + N) : ℝ) = (x (n + N) : ℝ) ^ 2 := by
      rw [show n + 1 + N = (n + N) + 1 by ring, x_succ]; push_cast; ring
    rw [hx]
    calc (2:ℝ) ^ (n + 1) * x N = 2 * (2 ^ n * x N) := by ring
      _ ≤ 2 * x (n + N) := by linarith
      _ ≤ x (n + N) * x (n + N) := by nlinarith
      _ = (x (n + N) : ℝ) ^ 2 := by ring

lemma prod_X (N : ℕ) : 2 * ∏ n ∈ Finset.range N, (x n : ℝ) = x N := by
  induction N with
  | zero => simp [x]
  | succ N ih =>
    rw [Finset.prod_range_succ, x_succ]; push_cast
    rw [← ih]; ring

lemma prod_X1 (N : ℕ) : ∏ n ∈ Finset.range N, ((x n : ℝ) + 1) + 1 = x N := by
  induction N with
  | zero => norm_num [x]
  | succ N ih =>
    rw [Finset.prod_range_succ, x_succ]; push_cast
    linear_combination ((x N : ℝ) + 1) * ih

lemma bern (t : ℝ) (ht : 0 ≤ t) (C : ℕ) : (t + C + 1) * t ^ C ≤ (t + 1) ^ (C + 1) := by
  induction C with
  | zero => simp
  | succ C ih =>
    push_cast
    have h1 : 0 ≤ t ^ C := pow_nonneg ht C
    have h2 : 0 ≤ (C:ℝ) + 1 := by positivity
    calc (t + ((C:ℝ) + 1) + 1) * t ^ (C + 1) ≤ (t + C + 1) * t ^ C * (t + 1) := by
          rw [pow_succ]; nlinarith [mul_nonneg h1 h2]
      _ ≤ (t + 1) ^ (C + 1) * (t + 1) := by gcongr
      _ = (t + 1) ^ (C + 1 + 1) := by ring

lemma prod_bound (N C : ℕ) :
    ∏ n ∈ Finset.range N, ((x n : ℝ) + C + 1) ≤
      2 ^ (C + 1) * ∏ n ∈ Finset.range N, (x n : ℝ) := by
  have hxpos : ∀ n, (0:ℝ) ≤ x n := fun n => by linarith [xR_ge_two n]
  have hPpos : 0 < ∏ n ∈ Finset.range N, (x n : ℝ) :=
    Finset.prod_pos (fun n _ => by linarith [xR_ge_two n])
  have h1 : (∏ n ∈ Finset.range N, ((x n : ℝ) + C + 1)) * (∏ n ∈ Finset.range N, (x n : ℝ)) ^ C
      ≤ (∏ n ∈ Finset.range N, ((x n : ℝ) + 1)) ^ (C + 1) := by
    calc (∏ n ∈ Finset.range N, ((x n : ℝ) + C + 1)) * (∏ n ∈ Finset.range N, (x n : ℝ)) ^ C
        = ∏ n ∈ Finset.range N, (((x n : ℝ) + C + 1) * (x n : ℝ) ^ C) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow]
      _ ≤ ∏ n ∈ Finset.range N, (((x n : ℝ) + 1) ^ (C + 1)) := by
          apply Finset.prod_le_prod
          · intro n _; have := hxpos n; positivity
          · intro n _; exact bern _ (hxpos n) C
      _ = _ := Finset.prod_pow _ _ _
  have h2 : (∏ n ∈ Finset.range N, ((x n : ℝ) + 1)) ≤ 2 * ∏ n ∈ Finset.range N, (x n : ℝ) := by
    have := prod_X1 N; have := prod_X N; linarith
  have h3 : (∏ n ∈ Finset.range N, ((x n : ℝ) + 1)) ^ (C + 1) ≤
      (2 * ∏ n ∈ Finset.range N, (x n : ℝ)) ^ (C + 1) :=
    pow_le_pow_left₀ (Finset.prod_nonneg fun n _ => by have := hxpos n; positivity) h2 _
  have h4 : (2 * ∏ n ∈ Finset.range N, (x n : ℝ)) ^ (C + 1) =
      (2 ^ (C + 1) * ∏ n ∈ Finset.range N, (x n : ℝ)) * (∏ n ∈ Finset.range N, (x n : ℝ)) ^ C := by
    ring
  exact le_of_mul_le_mul_right (by linarith) (pow_pos hPpos C)

lemma bound_of (b : ℕ → ℤ) (hu : BddAbove (Set.range b)) (hl : BddBelow (Set.range b)) :
    ∃ C : ℕ, ∀ n, |b n| ≤ C + 1 := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨l, hl⟩ := hl
  refine ⟨(|u| + |l|).toNat, fun n => ?_⟩
  have h1 : b n ≤ u := hu ⟨n, rfl⟩
  have h2 : l ≤ b n := hl ⟨n, rfl⟩
  have h3 : (((|u| + |l|).toNat : ℕ) : ℤ) = |u| + |l| := Int.toNat_of_nonneg (by positivity)
  rw [h3, abs_le]
  constructor <;> linarith [le_abs_self u, neg_abs_le l, abs_nonneg u, abs_nonneg l]

/-! ## the integer elimination step -/

lemma abs3 (a b c : ℤ) : |a - b - c| ≤ |a| + |b| + |c| := by
  rw [abs_le]; constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c]

lemma abs2 (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

lemma absadd (a b : ℤ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

lemma elim (y c c' k0 k1 k2 K B : ℤ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hc : |c| ≤ B) (hc' : |c'| ≤ B) (h0 : |k0| ≤ K) (h1 : |k1| ≤ K) (h2 : |k2| ≤ K)
    (hy : 1 + 2 * K + 4 * B * K + B * B * K ≤ y)
    (e : k2 = y ^ 2 * (k1 - k0) + y * (k1 - 2 * c * k0) + (c' + c) * k1 - c ^ 2 * k0) :
    k0 = 0 := by
  have hBK : 0 ≤ B * K := mul_nonneg hB hK
  have hBBK : 0 ≤ B * B * K := mul_nonneg (mul_nonneg hB hB) hK
  have hy1 : 0 ≤ y - 1 := by linarith
  have hcc : |c' + c| ≤ B + B := (absadd _ _).trans (add_le_add hc' hc)
  have hR : |(c' + c) * k1 - c ^ 2 * k0| ≤ (B + B) * K + (B * B) * K := by
    refine (abs2 _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul hcc h1 (abs_nonneg _) (by linarith)
    · rw [sq, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hc hc (abs_nonneg _) hB) h0 (abs_nonneg _) (mul_nonneg hB hB)
  have hL : |k1 - 2 * c * k0| ≤ K + 2 * B * K := by
    refine (abs2 _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_mul]
    have h22 : |(2:ℤ)| = 2 := by norm_num
    rw [h22]
    have := mul_le_mul hc h0 (abs_nonneg _) hB
    linarith
  by_cases hne : k1 = k0
  · rw [hne] at e hR
    by_contra hk
    have hodd : 1 - 2 * c ≠ 0 := by omega
    have h1' : 1 ≤ |k0 * (1 - 2 * c)| := Int.one_le_abs (mul_ne_zero hk hodd)
    have hE : y * (k0 * (1 - 2 * c)) = k2 - ((c' + c) * k0 - c ^ 2 * k0) := by rw [e]; ring
    have h3 : |y * (k0 * (1 - 2 * c))| ≤ K + ((B + B) * K + B * B * K) := by
      rw [hE]; exact (abs2 _ _).trans (add_le_add h2 hR)
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℤ) ≤ y)] at h3
    have h4 : y * 1 ≤ y * |k0 * (1 - 2 * c)| := mul_le_mul_of_nonneg_left h1' (by linarith)
    nlinarith
  · exfalso
    have hd : 1 ≤ |k1 - k0| := Int.one_le_abs (sub_ne_zero.2 hne)
    have hE : y ^ 2 * (k1 - k0) =
        k2 - y * (k1 - 2 * c * k0) - ((c' + c) * k1 - c ^ 2 * k0) := by rw [e]; ring
    have h3 : |y ^ 2 * (k1 - k0)| ≤ K + y * (K + 2 * B * K) + ((B + B) * K + B * B * K) := by
      rw [hE]
      refine (abs3 _ _ _).trans (add_le_add (add_le_add h2 ?_) hR)
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℤ) ≤ y)]
      exact mul_le_mul_of_nonneg_left hL (by linarith)
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)] at h3
    have h4 : y ^ 2 ≤ y ^ 2 * |k1 - k0| := by nlinarith [sq_nonneg y]
    have h5 : y * (1 + 2 * K + 4 * B * K + B * B * K) ≤ y * y :=
      mul_le_mul_of_nonneg_left hy (by linarith)
    nlinarith [mul_nonneg hy1 hK, mul_nonneg hy1 hBK, mul_nonneg hy1 hBBK]

/-! ## analytic part -/

lemma tail (b : ℕ → ℤ) (C : ℕ) (hC : ∀ n, |b n| ≤ C + 1) (A : ℕ → ℤ)
    (hAd : ∀ n, A n = x n + b n) (N : ℕ) (hN : 2 * ((C:ℝ) + 1) ≤ x N) :
    Summable (fun n => (1:ℝ) / A (n + N)) ∧ 0 < ∑' n, (1:ℝ) / A (n + N) ∧
      ∑' n, (1:ℝ) / A (n + N) ≤ 4 / x N := by
  have hxN : (0:ℝ) < x N := by linarith [xR_ge_two N]
  have hlow : ∀ n, (x (n + N) : ℝ) / 2 ≤ A (n + N) := by
    intro n
    have h1 := X_mul N n
    have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h3 : |(b (n + N) : ℝ)| ≤ C + 1 := by exact_mod_cast hC (n + N)
    have h4 := (abs_le.1 h3).1
    have h5 : (A (n + N) : ℝ) = x (n + N) + b (n + N) := by rw [hAd]; push_cast; ring
    nlinarith [mul_le_mul_of_nonneg_right h2 hxN.le]
  have hxp : ∀ n, (0:ℝ) < x (n + N) := fun n => by linarith [xR_ge_two (n + N)]
  have hpos : ∀ n, (0:ℝ) < 1 / A (n + N) := by
    intro n; have := hlow n; have := hxp n
    apply div_pos one_pos; linarith
  have hle : ∀ n, (1:ℝ) / A (n + N) ≤ (2 / x N) * (1 / 2) ^ n := by
    intro n
    have hl := hlow n
    have h1 := X_mul N n
    have hx2 : (0:ℝ) < x (n + N) / 2 := by linarith [hxp n]
    calc (1:ℝ) / A (n + N) ≤ 1 / ((x (n + N) : ℝ) / 2) := one_div_le_one_div_of_le hx2 hl
      _ = 2 / x (n + N) := by rw [one_div_div]
      _ ≤ 2 / (2 ^ n * x N) := div_le_div_of_nonneg_left (by norm_num) (mul_pos (by positivity) hxN) h1
      _ = (2 / x N) * (1 / 2) ^ n := by
          rw [one_div_pow]; field_simp
  have hg : Summable (fun n : ℕ => (2 / (x N : ℝ)) * (1 / 2) ^ n) :=
    summable_geometric_two.mul_left _
  have hs : Summable (fun n => (1:ℝ) / A (n + N)) :=
    Summable.of_nonneg_of_le (fun n => (hpos n).le) hle hg
  refine ⟨hs, hs.tsum_pos (fun n => (hpos n).le) 0 (hpos 0), ?_⟩
  calc ∑' n, (1:ℝ) / A (n + N) ≤ ∑' n : ℕ, (2 / (x N : ℝ)) * (1 / 2) ^ n :=
        hs.tsum_le_tsum hle hg
    _ = 4 / x N := by rw [tsum_mul_left, tsum_geometric_two]; ring

def Q (A : ℕ → ℤ) (N : ℕ) : ℤ := ∏ n ∈ Finset.range N, A n

def kk (A : ℕ → ℤ) (p q : ℤ) : ℕ → ℤ
  | 0 => p
  | N + 1 => A N * kk A p q N - q * Q A N

lemma Q_succ (A : ℕ → ℤ) (N : ℕ) : Q A (N + 1) = Q A N * A N := Finset.prod_range_succ _ _

lemma main (b : ℕ → ℤ) (C : ℕ) (hC : ∀ n, |b n| ≤ C + 1) (A : ℕ → ℤ)
    (hAd : ∀ n, A n = x n + b n) (hA : ∀ n, A n ≠ 0) :
    Irrational (∑' n, (1:ℝ) / A n) := by
  have hbig : ∀ M : ℕ, ∀ N, M ≤ N → (M:ℝ) ≤ x N := by
    intro M N h
    have := lt_x N
    have : (M:ℤ) ≤ x N := by omega
    exact_mod_cast this
  have hN1 : ∀ N, 2 * (C + 1) ≤ N → 2 * ((C:ℝ) + 1) ≤ x N := by
    intro N h; have := hbig (2 * (C + 1)) N h; push_cast at this; linarith
  have hs : Summable (fun n => (1:ℝ) / A n) :=
    (summable_nat_add_iff (f := fun n => (1:ℝ) / A n) (2 * (C + 1))).1
      (tail b C hC A hAd _ (hN1 _ le_rfl)).1
  rintro ⟨r, hr⟩
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hpq : (r.num : ℝ) = ((r.den : ℤ) : ℝ) * ∑' n, (1:ℝ) / A n := by
    rw [← hr, Rat.cast_def]; push_cast
    rw [mul_div_assoc']; exact (mul_div_cancel_left₀ _ hd).symm
  have htail : ∀ N, ∑' n, (1:ℝ) / A (n + N) =
      ∑' n, (1:ℝ) / A n - ∑ j ∈ Finset.range N, (1:ℝ) / A j := by
    intro N
    have e : ∑ j ∈ Finset.range N, (1:ℝ) / A j + ∑' n, (1:ℝ) / A (n + N) = ∑' n, (1:ℝ) / A n :=
      hs.sum_add_tsum_nat_add N
    linarith
  have hkk : ∀ N, (kk A r.num r.den N : ℝ) = ((r.den : ℤ) : ℝ) * Q A N *
      (∑' n, (1:ℝ) / A n - ∑ j ∈ Finset.range N, (1:ℝ) / A j) := by
    intro N
    induction N with
    | zero =>
      simp only [kk, Q, Finset.prod_range_zero, Finset.sum_range_zero, Int.cast_one, mul_one,
        sub_zero]
      exact hpq
    | succ N ih =>
      have hAN : (A N : ℝ) ≠ 0 := by exact_mod_cast hA N
      simp only [kk]
      rw [Q_succ, Finset.sum_range_succ]
      push_cast
      rw [ih]
      field_simp
      push_cast
      ring
  have hkt : ∀ N, (kk A r.num r.den N : ℝ) = ((r.den : ℤ) : ℝ) * Q A N *
      ∑' n, (1:ℝ) / A (n + N) := by
    intro N; rw [hkk, htail]
  have hbR : ∀ n, |(b n : ℝ)| ≤ C + 1 := fun n => by exact_mod_cast hC n
  have hQ : ∀ N, |(Q A N : ℝ)| ≤ 2 ^ (C + 1) * ∏ n ∈ Finset.range N, (x n : ℝ) := by
    intro N
    simp only [Q]; push_cast; rw [Finset.abs_prod]
    refine le_trans (Finset.prod_le_prod (fun n _ => abs_nonneg _) (fun n _ => ?_)) (prod_bound N C)
    rw [show (A n : ℝ) = x n + b n by rw [hAd]; push_cast; ring]
    have := abs_le.1 (hbR n); have := xR_ge_two n
    rw [abs_le]; constructor <;> linarith
  have hqpos : (0:ℝ) < ((r.den : ℤ) : ℝ) := by
    have : (0:ℤ) < r.den := by exact_mod_cast r.pos
    exact_mod_cast this
  have hKb : ∀ N, 2 * (C + 1) ≤ N → |kk A r.num r.den N| ≤ (r.den : ℤ) * 2 ^ (C + 2) := by
    intro N hN
    obtain ⟨_, hT0, hT⟩ := tail b C hC A hAd N (hN1 N hN)
    have h1 := hQ N
    have h2 := prod_X N
    have hP : 0 < ∏ n ∈ Finset.range N, (x n : ℝ) :=
      Finset.prod_pos (fun n _ => by linarith [xR_ge_two n])
    have hreal : |(kk A r.num r.den N : ℝ)| ≤ ((r.den : ℤ) : ℝ) * 2 ^ (C + 2) := by
      rw [hkt N, abs_mul, abs_mul, abs_of_pos hT0, abs_of_pos hqpos]
      calc ((r.den : ℤ) : ℝ) * |(Q A N : ℝ)| * ∑' n, (1:ℝ) / A (n + N)
          ≤ ((r.den : ℤ) : ℝ) * (2 ^ (C + 1) * ∏ n ∈ Finset.range N, (x n : ℝ)) * (4 / x N) := by
            gcongr
        _ = ((r.den : ℤ) : ℝ) * 2 ^ (C + 2) := by
            rw [← h2]; field_simp; ring
    exact_mod_cast hreal
  -- choose a large N
  set K : ℤ := (r.den : ℤ) * 2 ^ (C + 2) with hKdef
  set B : ℤ := (C : ℤ) + 1 with hBdef
  have hK0 : 0 ≤ K := by positivity
  have hB0 : 0 ≤ B := by positivity
  set M : ℤ := 1 + 2 * K + 4 * B * K + B * B * K with hMdef
  set N : ℕ := 2 * (C + 1) + M.toNat with hNdef
  have hMN : M ≤ x N := by
    have h1 := Int.self_le_toNat M
    have h2 := lt_x N
    have h3 : (N : ℤ) = 2 * ((C : ℤ) + 1) + (M.toNat : ℤ) := by rw [hNdef]; push_cast; ring
    have h4 : (0:ℤ) ≤ C := by positivity
    linarith
  have hk1 : kk A r.num r.den (N + 1) = A N * kk A r.num r.den N - (r.den : ℤ) * Q A N := rfl
  have hk2 : kk A r.num r.den (N + 2) =
      A (N + 1) * kk A r.num r.den (N + 1) - (r.den : ℤ) * Q A (N + 1) := rfl
  rw [Q_succ, hAd (N + 1), x_succ, hAd N] at hk2
  rw [hAd N] at hk1
  have h0 := elim (x N) (b N) (b (N + 1)) (kk A r.num r.den N) (kk A r.num r.den (N + 1))
    (kk A r.num r.den (N + 2)) K B hB0 hK0 (hC N) (hC (N + 1))
    (hKb N (by omega)) (hKb (N + 1) (by omega)) (hKb (N + 2) (by omega)) hMN
    (by linear_combination hk2 - (x N + b N) * hk1)
  have hz := hkt N
  rw [h0] at hz
  obtain ⟨_, hT0, _⟩ := tail b C hC A hAd N (hN1 N (by omega))
  have hQ0 : (Q A N : ℝ) ≠ 0 := by
    have : Q A N ≠ 0 := Finset.prod_ne_zero_iff.2 (fun n _ => hA n)
    exact_mod_cast this
  have : ((r.den : ℤ) : ℝ) * Q A N * ∑' n, (1:ℝ) / A (n + N) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hqpos.ne' hQ0) hT0.ne'
  apply this
  rw [← hz]; simp

end Ex

theorem erdos_264.variants.example : IsIrrationalitySequence (fun n ↦ 2 ^ (2 ^ n)) := by
  intro b hu hl h0 _
  obtain ⟨C, hC⟩ := Ex.bound_of b hu hl
  have hA : ∀ n, Ex.x n + b n ≠ 0 := by
    intro n h
    apply h0
    refine ⟨n, ?_⟩
    show (((2 ^ 2 ^ n : ℕ) : ℤ)) + b n = 0
    simp only [Ex.x] at h
    push_cast
    exact h
  have H := Ex.main b C hC (fun n => Ex.x n + b n) (fun n => rfl) hA
  convert H using 3 with n
  simp [Ex.x]

end Erdos264

#print axioms Erdos264.erdos_264.variants.example
