import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

namespace Erdos878

/-- The function $f(n)=\sum_{p\mid n}p^{\lfloor\log_p n\rfloor}$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- The function $H(x)=\sum_{1\le n<x}f(n)/n$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

namespace LS

/-- Simultaneous Dirichlet approximation with `M` buckets. -/
lemma bucket (a b : ℝ) (M : ℕ) (hM : 0 < M)
    (h : ⌊(M : ℝ) * Int.fract a⌋₊ = ⌊(M : ℝ) * Int.fract b⌋₊) :
    |(b - a) - ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ)| < 1 / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have ha0 := Int.fract_nonneg a
  have hb0 := Int.fract_nonneg b
  have h1 := Nat.floor_le (show 0 ≤ (M : ℝ) * Int.fract a by positivity)
  have h2 := Nat.lt_floor_add_one ((M : ℝ) * Int.fract a)
  have h3 := Nat.floor_le (show 0 ≤ (M : ℝ) * Int.fract b by positivity)
  have h4 := Nat.lt_floor_add_one ((M : ℝ) * Int.fract b)
  rw [h] at h1 h2
  have ea := Int.floor_add_fract a
  have eb := Int.floor_add_fract b
  have key : (b - a) - ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) = Int.fract b - Int.fract a := by
    push_cast; linarith
  rw [key, abs_lt, lt_div_iff₀ hM', div_eq_mul_inv, one_mul]
  constructor
  · rw [neg_lt]
    have : (M : ℝ) * (Int.fract a - Int.fract b) < 1 := by linarith
    have := (lt_div_iff₀ hM').mpr (by linarith : (Int.fract a - Int.fract b) * M < 1)
    rw [one_div] at this; linarith
  · have := (lt_div_iff₀ hM').mpr (by linarith : (Int.fract b - Int.fract a) * M < 1)
    rw [one_div] at this; linarith

lemma dir (S : Finset ℝ) (M : ℕ) (hM : 0 < M) (a : ℕ) :
    ∃ k : ℕ, a ≤ k ∧ ∀ y ∈ S, ∃ z : ℤ, |(k : ℝ) * y - z| < 1 / M := by
  let L : ℕ := a + 1
  let g : Fin (Fintype.card (S → Fin M) + 1) → (S → Fin M) := fun j y =>
    ⟨⌊(M : ℝ) * Int.fract (((j : ℕ) : ℝ) * L * (y : ℝ))⌋₊, by
      have h1 := Int.fract_lt_one (((j : ℕ) : ℝ) * L * (y : ℝ))
      have h0 := Int.fract_nonneg (((j : ℕ) : ℝ) * L * (y : ℝ))
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      rw [Nat.floor_lt (by positivity)]
      nlinarith⟩
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have hfl : ∀ y ∈ S, ⌊(M : ℝ) * Int.fract (((i : ℕ) : ℝ) * L * y)⌋₊
      = ⌊(M : ℝ) * Int.fract (((j : ℕ) : ℝ) * L * y)⌋₊ := by
    intro y hy
    have := congrArg Fin.val (congrFun hg ⟨y, hy⟩)
    simpa [g] using this
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨((j : ℕ) - i) * L, ?_, ?_⟩
    · have : L ≤ ((j : ℕ) - i) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    · intro y hy
      refine ⟨⌊((j : ℕ) : ℝ) * L * y⌋ - ⌊((i : ℕ) : ℝ) * L * y⌋, ?_⟩
      have := bucket _ _ M hM (hfl y hy)
      convert this using 3
      push_cast [Nat.cast_sub hlt.le]
      ring
  · refine ⟨((i : ℕ) - j) * L, ?_, ?_⟩
    · have : L ≤ ((i : ℕ) - j) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    · intro y hy
      refine ⟨⌊((i : ℕ) : ℝ) * L * y⌋ - ⌊((j : ℕ) : ℝ) * L * y⌋, ?_⟩
      have := bucket _ _ M hM (hfl y hy).symm
      convert this using 3
      push_cast [Nat.cast_sub hlt.le]
      ring

lemma u_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- From a good approximation of `k / log p` to a power of `p` near `x`. -/
lemma approx (p N M k : ℕ) (z : ℤ) (hp : 2 ≤ p) (hpN : p < N) (hM : 0 < M)
    (hMN : 2 * Real.log N ≤ M) (hk : 1 ≤ k)
    (hz : |(k : ℝ) * (1 / Real.log p) - z| < 1 / M) :
    ∃ j : ℕ, 1 ≤ j ∧ 2 * p ^ j ≤ ⌈4 * Real.exp k⌉₊ ∧ ⌈4 * Real.exp k⌉₊ ≤ 8 * p ^ j := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlN : Real.log p ≤ Real.log N :=
    Real.log_le_log (by positivity) (by exact_mod_cast hpN.le)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e1 : (k : ℝ) - z * Real.log p = Real.log p * ((k : ℝ) * (1 / Real.log p) - z) := by
    field_simp
  have hb : |(k : ℝ) - z * Real.log p| < 1 / 2 := by
    rw [e1, abs_mul, abs_of_pos hlp]
    calc Real.log p * |(k : ℝ) * (1 / Real.log p) - z| < Real.log p * (1 / M) :=
          mul_lt_mul_of_pos_left hz hlp
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ hM']; linarith
  rw [abs_lt] at hb
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz0 : (0 : ℝ) < z := by
    by_contra hc
    push Not at hc
    nlinarith
  have hz0' : 0 < z := by exact_mod_cast hz0
  refine ⟨z.toNat, by omega, ?_⟩
  have hj : ((z.toNat : ℕ) : ℝ) = z := by
    have : ((z.toNat : ℤ)) = z := Int.toNat_of_nonneg hz0'.le
    exact_mod_cast this
  have hpow : ((p : ℝ) ^ z.toNat) = Real.exp (z * Real.log p) := by
    rw [← hj, Real.exp_nat_mul, Real.exp_log (by positivity)]
  set E := Real.exp k with hE
  set u := Real.exp (1 / 2) with hu
  have hu2 := u_lt_two
  have hu0 : 0 < u := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hup : (p : ℝ) ^ z.toNat < E * u := by
    rw [hpow, hE, hu, ← Real.exp_add]; exact Real.exp_lt_exp.mpr (by linarith)
  have hlo : E < (p : ℝ) ^ z.toNat * u := by
    rw [hpow, hE, hu, ← Real.exp_add]; exact Real.exp_lt_exp.mpr (by linarith)
  have hx1 := Nat.le_ceil (4 * E)
  have hx2 := Nat.ceil_lt_add_one (show 0 ≤ 4 * E by positivity)
  have hP0 : 0 < (p : ℝ) ^ z.toNat := by positivity
  constructor
  · have : ((2 * p ^ z.toNat : ℕ) : ℝ) ≤ (⌈4 * E⌉₊ : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this
  · have : (⌈4 * E⌉₊ : ℝ) < ((8 * p ^ z.toNat + 1 : ℕ) : ℝ) := by
      push_cast; nlinarith
    have : ⌈4 * E⌉₊ < 8 * p ^ z.toNat + 1 := by exact_mod_cast this
    omega

/-- Contribution of the multiples of `p` in `[p^j, 2p^j)`. -/
lemma contrib (p j x : ℕ) (hp : 2 ≤ p) (hj : 1 ≤ j) (h1 : 2 * p ^ j ≤ x)
    (h2 : x ≤ 8 * p ^ j) :
    (x : ℝ) / (16 * p) ≤
      ∑ n ∈ (Ico 1 x).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / n := by
  set q := p ^ (j - 1) with hq
  have hpq : p ^ j = p * q := by
    rw [hq, ← pow_succ']; congr 1; omega
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by omega)
  have hp0 : 0 < p := by omega
  have hT : (Ico q (2 * q)).image (p * ·) ⊆ (Ico 1 x).filter (p ∣ ·) := by
    intro n hn
    simp only [mem_image, mem_Ico] at hn
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hn
    simp only [mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · have : 1 ≤ p * i := Nat.mul_pos hp0 (by omega)
      omega
    · have : p * i < p * (2 * q) := Nat.mul_lt_mul_of_pos_left hi2 hp0
      have : p * (2 * q) = 2 * p ^ j := by rw [hpq]; ring
      omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  calc (x : ℝ) / (16 * p) ≤ (q : ℝ) * (1 / 2) := by
        rw [div_le_iff₀ (by positivity)]
        have : (x : ℝ) ≤ 8 * ((p : ℝ) * q) := by
          have := h2; rw [hpq] at this; exact_mod_cast this
        nlinarith
    _ = ∑ i ∈ Ico q (2 * q), (1 / 2 : ℝ) := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        congr 1
        have : 2 * q - q = q := by omega
        rw [this]
    _ ≤ ∑ i ∈ Ico q (2 * q), (p : ℝ) ^ (Nat.log p (p * i)) / ((p * i : ℕ) : ℝ) := by
        apply sum_le_sum
        intro i hi
        rw [mem_Ico] at hi
        have hlow : p ^ j ≤ p * i := by
          rw [hpq]; exact Nat.mul_le_mul_left _ hi.1
        have hhigh : p * i < 2 * p ^ j := by
          have : p * i < p * (2 * q) := Nat.mul_lt_mul_of_pos_left hi.2 hp0
          have : p * (2 * q) = 2 * p ^ j := by rw [hpq]; ring
          omega
        have hhigh' : p * i < p ^ (j + 1) := by
          rw [pow_succ]
          have : 2 * p ^ j ≤ p ^ j * p := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hp
          omega
        rw [Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh']
        have hpi : (0 : ℝ) < ((p * i : ℕ) : ℝ) := by
          have : 0 < p * i := by omega
          exact_mod_cast this
        rw [le_div_iff₀ hpi]
        have : ((p * i : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ j := by
          have := hhigh.le; exact_mod_cast this
        linarith
    _ = ∑ n ∈ (Ico q (2 * q)).image (p * ·), (p : ℝ) ^ (Nat.log p n) / n := by
        rw [sum_image]
        intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left hp0 hab
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hT
        intro n _ _
        positivity

lemma swap (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ) :
    ∑ p ∈ P, ∑ n ∈ (Ico 1 x).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / n ≤ H x := by
  have e1 : H x = ∑ n ∈ Ico 1 x, ∑ p ∈ n.primeFactors, (p : ℝ) ^ (Nat.log p n) / n := by
    unfold H f
    refine sum_congr rfl fun n _ => ?_
    push_cast
    rw [Finset.sum_div]
  rw [e1]
  calc ∑ p ∈ P, ∑ n ∈ (Ico 1 x).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / n
      = ∑ n ∈ Ico 1 x, ∑ p ∈ P.filter (· ∣ n), (p : ℝ) ^ (Nat.log p n) / n := by
        apply Finset.sum_comm'
        intro p n
        simp only [mem_filter]
        tauto
    _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp
          rw [mem_Ico] at hn
          exact Nat.mem_primeFactors.mpr ⟨hP p hp.1, hp.2, by omega⟩
        · intro p _ _
          positivity

lemma primes_big (B : ℝ) : ∃ N : ℕ, B ≤ ∑ p ∈ (range N).filter Nat.Prime, (1 : ℝ) / p := by
  have h := not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg] at h
  · obtain ⟨N, hN⟩ := (h.eventually_ge_atTop B).exists
    refine ⟨N, hN.trans_eq ?_⟩
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp [Set.indicator_apply]
  · intro n
    simp only [Set.indicator_apply]
    split_ifs <;> positivity

end LS

/-- Erdős [Er84e] showed that $\limsup_{x\to\infty}H(x)/x=\infty$. -/
theorem erdos_878.variants.H_div_self_limsup_infinite :
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C ≤ H x / (x : ℝ) := by
  intro C
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨N, hN⟩ := LS.primes_big (16 * (|C| + 1))
  set P := (range N).filter Nat.Prime with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ p < N := by
    intro p hp
    rw [hPdef, mem_filter, mem_range] at hp
    exact ⟨hp.2, hp.1⟩
  set M : ℕ := ⌈2 * Real.log N⌉₊ + 1 with hMdef
  have hM : 0 < M := by omega
  have hMN : 2 * Real.log N ≤ M := by
    rw [hMdef]; push_cast
    linarith [Nat.le_ceil (2 * Real.log N)]
  obtain ⟨k, hk, hS⟩ := LS.dir (P.image fun p : ℕ => 1 / Real.log p) M hM (a + 1)
  set x := ⌈4 * Real.exp k⌉₊ with hx
  have hj : ∀ p ∈ P, ∃ j : ℕ, 1 ≤ j ∧ 2 * p ^ j ≤ x ∧ x ≤ 8 * p ^ j := by
    intro p hp
    obtain ⟨z, hz⟩ := hS _ (mem_image_of_mem _ hp)
    exact LS.approx p N M k z (hP p hp).1.two_le (hP p hp).2 hM hMN (by omega) hz
  have hxa : a ≤ x := by
    have h1 := Real.add_one_le_exp (k : ℝ)
    have h2 := Nat.le_ceil (4 * Real.exp k)
    have h3 : (a : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have h4 : (a : ℝ) ≤ (x : ℝ) := by
      rw [hx]; nlinarith [Real.exp_pos (k : ℝ)]
    exact_mod_cast h4
  refine ⟨x, hxa, ?_⟩
  have hx0 : (0 : ℝ) < x := by
    have := Nat.le_ceil (4 * Real.exp k)
    rw [hx]; nlinarith [Real.exp_pos (k : ℝ)]
  have hlow : ∑ p ∈ P, (x : ℝ) / (16 * p) ≤ H x := by
    refine le_trans ?_ (LS.swap P (fun p hp => (hP p hp).1) x)
    apply sum_le_sum
    intro p hp
    obtain ⟨j, hj1, hj2, hj3⟩ := hj p hp
    exact LS.contrib p j x (hP p hp).1.two_le hj1 hj2 hj3
  have e2 : ∑ p ∈ P, (x : ℝ) / (16 * p) = (x : ℝ) / 16 * ∑ p ∈ P, (1 : ℝ) / p := by
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    field_simp
  rw [le_div_iff₀ hx0]
  have hC : C * x ≤ (|C| + 1) * x := by
    have := le_abs_self C
    nlinarith
  have : (|C| + 1) * x ≤ (x : ℝ) / 16 * ∑ p ∈ P, (1 : ℝ) / p := by
    have := mul_le_mul_of_nonneg_left hN (show (0 : ℝ) ≤ x / 16 by positivity)
    nlinarith
  linarith

end Erdos878

#print axioms Erdos878.erdos_878.variants.H_div_self_limsup_infinite
