import Mathlib.NumberTheory.EulerProduct.Basic
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

namespace QL

noncomputable def inv : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; exact mul_inv _ _

lemma inv_apply (n : ℕ) : inv n = (n : ℝ)⁻¹ := rfl

lemma harm (b : ℕ) :
    Real.log ((b : ℝ) + 1) ≤ ∑ x ∈ range b, (1 : ℝ) / ((x : ℝ) + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ]
    have key : Real.log ((b : ℝ) + 1 + 1) - Real.log ((b : ℝ) + 1) ≤ 1 / ((b : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) by positivity)
      have e : ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) - 1 = 1 / ((b : ℝ) + 1) := by
        field_simp
        ring
      linarith
    push_cast
    linarith

/-- Euler product: the harmonic sum up to `N` is at most `∏_{p<N} (1 - 1/p)⁻¹`. -/
lemma harm_le_prod (N : ℕ) :
    ∑ m ∈ Ico 1 N, (m : ℝ)⁻¹ ≤ ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := inv) (fun {p} hp => by
      rw [inv_apply, norm_inv, Real.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) N).2
  have h2 := sum_le_hasSum ((Ico 1 N).subtype (· ∈ N.smoothNumbers))
    (fun i _ => by rw [inv_apply]; positivity) h
  rw [Finset.sum_subtype_eq_sum_filter] at h2
  have hf : (Ico 1 N).filter (· ∈ N.smoothNumbers) = Ico 1 N := by
    apply filter_true_of_mem
    intro m hm
    rw [mem_Ico] at hm
    exact Nat.mem_smoothNumbers_of_lt (by omega) hm.2
  rw [hf] at h2
  simpa [inv_apply] using h2

lemma factor_le (p : ℕ) (hp : 2 ≤ p) : (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (1 / (p : ℝ))) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have e : (1 - (p : ℝ)⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
    have hpne : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    have e2 : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
    rw [e2, inv_div, div_add_one hp1]
    congr 1; ring
  rw [e]
  refine le_trans (Real.add_one_le_exp _) (Real.exp_le_exp.mpr ?_)
  rw [div_le_iff₀ (by linarith), mul_one_div, mul_comm, ← mul_div_assoc, le_div_iff₀ (by linarith)]
  linarith

/-- MERTENS-TYPE LOWER BOUND: `log log N ≤ 2 Σ_{p<N} 1/p`. -/
lemma loglog_le (N : ℕ) (hN : 2 ≤ N) :
    Real.log (Real.log N) ≤ 2 * ∑ p ∈ (range N).filter Nat.Prime, (1 : ℝ) / p := by
  have h1 : Real.log N ≤ ∑ m ∈ Ico 1 N, (m : ℝ)⁻¹ := by
    have := harm (N - 1)
    have e1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1] at this
    refine this.trans (le_of_eq ?_)
    rw [range_eq_Ico]
    have := sum_Ico_add' (fun m : ℕ => (m : ℝ)⁻¹) 0 (N - 1) 1
    rw [show N - 1 + 1 = N by omega, zero_add] at this
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    push_cast; rw [one_div]
  have h3 : ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ ≤
      ∏ p ∈ N.primesBelow, Real.exp (2 * (1 / (p : ℝ))) := by
    apply Finset.prod_le_prod
    · intro p hp
      have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt)
      have : 0 < 1 - (p : ℝ)⁻¹ := by linarith
      positivity
    · intro p hp
      exact factor_le p (Nat.prime_of_mem_primesBelow hp).two_le
  rw [← Real.exp_sum, ← mul_sum] at h3
  have h4 := h1.trans ((harm_le_prod N).trans h3)
  have hpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have := Real.log_le_log hpos h4
  rw [Real.log_exp] at this
  simpa [Nat.primesBelow] using this

end QL

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

/-- QUANTITATIVE SIMULTANEOUS DIRICHLET: `a ≤ k ≤ (a+1) M^|S|`. -/
lemma dirq (S : Finset ℝ) (M : ℕ) (hM : 0 < M) (a : ℕ) :
    ∃ k : ℕ, a ≤ k ∧ k ≤ (a + 1) * M ^ S.card ∧
      ∀ y ∈ S, ∃ z : ℤ, |(k : ℝ) * y - z| < 1 / M := by
  let L : ℕ := a + 1
  let g : Fin (Fintype.card (S → Fin M) + 1) → (S → Fin M) := fun j y =>
    ⟨⌊(M : ℝ) * Int.fract (((j : ℕ) : ℝ) * L * (y : ℝ))⌋₊, by
      have h1 := Int.fract_lt_one (((j : ℕ) : ℝ) * L * (y : ℝ))
      have h0 := Int.fract_nonneg (((j : ℕ) : ℝ) * L * (y : ℝ))
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      rw [Nat.floor_lt (by positivity)]
      nlinarith⟩
  have hc : Fintype.card (S → Fin M) = M ^ S.card := by simp
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have hfl : ∀ y ∈ S, ⌊(M : ℝ) * Int.fract (((i : ℕ) : ℝ) * L * y)⌋₊
      = ⌊(M : ℝ) * Int.fract (((j : ℕ) : ℝ) * L * y)⌋₊ := by
    intro y hy
    have := congrArg Fin.val (congrFun hg ⟨y, hy⟩)
    simpa [g] using this
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hi : (i : ℕ) < M ^ S.card + 1 := lt_of_lt_of_eq i.isLt (by rw [hc])
  have hj : (j : ℕ) < M ^ S.card + 1 := lt_of_lt_of_eq j.isLt (by rw [hc])
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨((j : ℕ) - i) * L, ?_, ?_, ?_⟩
    · have : L ≤ ((j : ℕ) - i) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    · calc ((j : ℕ) - i) * L ≤ M ^ S.card * L := Nat.mul_le_mul_right _ (by omega)
        _ = (a + 1) * M ^ S.card := by rw [mul_comm]
    · intro y hy
      refine ⟨⌊((j : ℕ) : ℝ) * L * y⌋ - ⌊((i : ℕ) : ℝ) * L * y⌋, ?_⟩
      have := bucket _ _ M hM (hfl y hy)
      convert this using 3
      push_cast [Nat.cast_sub hlt.le]
      ring
  · refine ⟨((i : ℕ) - j) * L, ?_, ?_, ?_⟩
    · have : L ≤ ((i : ℕ) - j) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    · calc ((i : ℕ) - j) * L ≤ M ^ S.card * L := Nat.mul_le_mul_right _ (by omega)
        _ = (a + 1) * M ^ S.card := by rw [mul_comm]
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

end LS

/-- Erdős [Er84e] proved that $x\log\log\log\log x\ll H(x)$;
this entry records the infinitely-often consequence. -/
theorem erdos_878.variants.H_lower_quadruple_log_infinitely_often :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ H x := by
  refine ⟨1 / 96, by norm_num, ?_⟩
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = a + 16 := ⟨_, rfl⟩
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
  set S := P.image fun p : ℕ => 1 / Real.log p with hSdef
  obtain ⟨k, hk, hkup, hS⟩ := LS.dirq S M hM (a + 3)
  set x := ⌈4 * Real.exp k⌉₊ with hx
  have hj : ∀ p ∈ P, ∃ j : ℕ, 1 ≤ j ∧ 2 * p ^ j ≤ x ∧ x ≤ 8 * p ^ j := by
    intro p hp
    obtain ⟨z, hz⟩ := hS _ (mem_image_of_mem _ hp)
    exact LS.approx p N M k z (hP p hp).1.two_le (hP p hp).2 hM hMN (by omega) hz
  have hxa : a ≤ x := by
    have h1 := Real.add_one_le_exp (k : ℝ)
    have h2 := Nat.le_ceil (4 * Real.exp k)
    have h3 : (a : ℝ) + 3 ≤ k := by exact_mod_cast hk
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
  -- the prime sum
  have hPS : Real.log (Real.log N) ≤ 2 * ∑ p ∈ P, (1 : ℝ) / p := QL.loglog_le N (by omega)
  have hN16 : (16 : ℝ) ≤ N := by
    rw [hNdef]; push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogN : Real.exp 1 ≤ Real.log N := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hN16
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    linarith
  have hLLN : 1 ≤ Real.log (Real.log N) := by
    have := Real.log_le_log (Real.exp_pos 1) hlogN
    rwa [Real.log_exp] at this
  -- size of k
  have hcard : S.card ≤ N :=
    card_image_le.trans ((card_filter_le _ _).trans (card_range N).le)
  have hM3 : M ≤ 3 * N := by
    have : ⌈2 * Real.log N⌉₊ ≤ 2 * N := by
      rw [Nat.ceil_le]; push_cast
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by positivity)
      linarith
    omega
  have hk2 : k + 2 ≤ (3 * N) ^ (N + 2) := by
    have h1 : M ^ S.card ≤ (3 * N) ^ N :=
      (Nat.pow_le_pow_left hM3 _).trans (Nat.pow_le_pow_right (by omega) hcard)
    have h2 : k ≤ N * (3 * N) ^ N := hkup.trans (Nat.mul_le_mul (by omega) h1)
    have h3 : N * (3 * N) ^ N ≤ (3 * N) ^ (N + 1) := by
      rw [pow_succ']; exact Nat.mul_le_mul_right _ (by omega)
    have h4 : 1 ≤ (3 * N) ^ (N + 1) := Nat.one_le_pow _ _ (by omega)
    have h5 : k ≤ (3 * N) ^ (N + 1) := h2.trans h3
    calc k + 2 ≤ (3 * N) ^ (N + 1) * 3 := by
          generalize (3 * N) ^ (N + 1) = A at h4 h5 ⊢; omega
      _ ≤ (3 * N) ^ (N + 1) * (3 * N) := Nat.mul_le_mul_left _ (by omega)
      _ = (3 * N) ^ (N + 2) := (pow_succ _ _).symm
  set T : ℝ := 3 * (N : ℝ) with hTdef
  have hk2R : (k : ℝ) + 2 ≤ T ^ (N + 2) := by
    rw [hTdef]; exact_mod_cast hk2
  have hT : 48 ≤ T := by rw [hTdef]; linarith
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT : Real.log T ≤ 2 * Real.log N := by
    rw [hTdef, Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ N)
    linarith
  -- bounds on x
  have hk3 : (3 : ℝ) ≤ k := by
    have : a + 3 ≤ k := hk
    have : ((a + 3 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
    push_cast at this
    linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hEk := Real.one_le_exp (show (0 : ℝ) ≤ k by linarith)
  have hxlo : Real.exp k ≤ x := by
    have := Nat.le_ceil (4 * Real.exp k)
    rw [hx]; linarith
  have hxup : (x : ℝ) ≤ Real.exp ((k : ℝ) + 2) := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.exp k by positivity)
    have h2 : Real.exp ((k : ℝ) + 2) = Real.exp k * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h3 := Real.exp_one_gt_d9
    have h4 : 7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    rw [h2, hx]
    nlinarith
  have L1 : Real.log x ≤ k + 2 := by
    have := Real.log_le_log hx0 hxup
    rwa [Real.log_exp] at this
  have L1lo : (k : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hxlo
    rwa [Real.log_exp] at this
  have L2 : Real.log (Real.log x) ≤ (N + 2) * Real.log T := by
    have := Real.log_le_log (by linarith) (L1.trans hk2R)
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have L2' : ((N : ℝ) + 2) * Real.log T ≤ T * T := by
    have h1 : (N : ℝ) + 2 ≤ T := by rw [hTdef]; linarith
    have h2 : Real.log T ≤ T := by
      have := Real.log_le_sub_one_of_pos (show 0 < T by linarith); linarith
    calc ((N : ℝ) + 2) * Real.log T ≤ T * Real.log T :=
          mul_le_mul_of_nonneg_right h1 hlogTpos.le
      _ ≤ T * T := mul_le_mul_of_nonneg_left h2 (by linarith)
  have L2lo : 1 < Real.log (Real.log x) := by
    have h3 : 1 < Real.log 3 := by
      have := Real.log_lt_log (Real.exp_pos 1) (show Real.exp 1 < 3 by
        have := Real.exp_one_lt_d9; linarith)
      rwa [Real.log_exp] at this
    have := Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ Real.log x by linarith)
    linarith
  have L3 : Real.log (Real.log (Real.log x)) ≤ 2 * Real.log T := by
    have := Real.log_le_log (by linarith) (L2.trans L2')
    rw [← pow_two, Real.log_pow] at this
    push_cast at this
    exact this
  have L3lo : 0 < Real.log (Real.log (Real.log x)) := Real.log_pos L2lo
  have L4 : Real.log (Real.log (Real.log (Real.log x))) ≤ 3 * Real.log (Real.log N) := by
    have h1 := Real.log_le_log L3lo L3
    rw [Real.log_mul (by norm_num) hlogTpos.ne'] at h1
    have h2 := Real.log_le_log hlogTpos hlogT
    rw [Real.log_mul (by norm_num) hlogNpos.ne'] at h2
    have := Real.log_two_lt_d9
    linarith
  calc 1 / 96 * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ)))))
      ≤ 1 / 96 * ((x : ℝ) * (3 * Real.log (Real.log N))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left L4 hx0.le
    _ = (x : ℝ) / 16 * (Real.log (Real.log N) / 2) := by ring
    _ ≤ (x : ℝ) / 16 * ∑ p ∈ P, (1 : ℝ) / p :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ∑ p ∈ P, (x : ℝ) / (16 * p) := e2.symm
    _ ≤ H x := hlow

end Erdos878

#print axioms Erdos878.erdos_878.variants.H_lower_quadruple_log_infinitely_often
