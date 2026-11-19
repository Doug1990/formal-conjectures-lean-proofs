import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Polynomial Finset
open scoped Real

namespace Erdos990

namespace CE

lemma key_sum (n : ℕ) (e : ℕ → ℕ) (he : Set.InjOn (fun j => (e j : ℂ)) (range n))
    (m : ℕ) (hm : m < n) :
    ∑ j ∈ range n, ((e j).descFactorial m : ℂ) / ∏ i ∈ (range n).erase j, ((e j : ℂ) - e i)
      = (descPochhammer ℂ m).coeff (n - 1) := by
  have hdeg : (descPochhammer ℂ m).degree < (#(range n) : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_descPochhammer ℂ m).ne_zero, descPochhammer_natDegree,
      card_range]
    exact_mod_cast hm
  have h := Lagrange.coeff_eq_sum (s := range n) (v := fun j => (e j : ℂ)) he hdeg
  rw [card_range] at h
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  rw [descPochhammer_eval_eq_descFactorial]

lemma eval_iter (s : Finset ℕ) (a : ℕ → ℂ) (e : ℕ → ℕ) (m : ℕ) (t : ℂ) :
    (derivative^[m] (∑ j ∈ s, C (a j) * X ^ (e j))).eval t * t ^ m
      = ∑ j ∈ s, a j * t ^ (e j) * ((e j).descFactorial m : ℂ) := by
  rw [iterate_derivative_sum, eval_finsetSum, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rcases le_or_gt m (e j) with h | h
  · have : t ^ (e j) = t ^ (e j - m) * t ^ m := by rw [← pow_add, Nat.sub_add_cancel h]
    rw [this]; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

/-- The sparse polynomial with exponents `e j` and divided-difference weights, rescaled
so that `t` becomes the multiple root. -/
noncomputable def poly (n : ℕ) (e : ℕ → ℕ) (t : ℂ) : ℂ[X] :=
  ∑ j ∈ range n, C ((∏ i ∈ (range n).erase j, ((e j : ℂ) - e i))⁻¹ / t ^ (e j)) * X ^ (e j)

lemma mult (n : ℕ) (hn : 2 ≤ n) (e : ℕ → ℕ) (he : Set.InjOn (fun j => (e j : ℂ)) (range n))
    (t : ℂ) (ht : t ≠ 0) :
    poly n e t ≠ 0 ∧ (poly n e t).rootMultiplicity t = n - 1 := by
  have hval : ∀ m < n, (derivative^[m] (poly n e t)).eval t * t ^ m
      = (descPochhammer ℂ m).coeff (n - 1) := by
    intro m hm
    rw [poly, eval_iter, ← key_sum n e he m hm]
    refine sum_congr rfl fun j _ => ?_
    rw [div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    ring
  have htop : (derivative^[n-1] (poly n e t)).eval t ≠ 0 := by
    intro h0
    have := hval (n-1) (by omega)
    rw [h0, zero_mul] at this
    have h1 : (descPochhammer ℂ (n-1)).coeff (n-1) = 1 := by
      have := (monic_descPochhammer ℂ (n-1)).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    rw [h1] at this
    exact zero_ne_one this
  have hf : poly n e t ≠ 0 := by
    intro h; apply htop; rw [h]; simp
  refine ⟨hf, ?_⟩
  have hlt : n - 2 < (poly n e t).rootMultiplicity t := by
    rw [lt_rootMultiplicity_iff_isRoot_iterate_derivative hf]
    intro m hm
    have := hval m (by omega)
    have hc : (descPochhammer ℂ m).coeff (n - 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [descPochhammer_natDegree]; omega
    rw [hc] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ ht)
  have hle : ¬ (n - 1 < (poly n e t).rootMultiplicity t) := by
    rw [lt_rootMultiplicity_iff_isRoot_iterate_derivative hf]
    intro h; exact htop (h (n-1) le_rfl)
  omega

/-! ### Coefficients of a sparse polynomial -/

section sparse
variable (n : ℕ) (a : ℕ → ℂ) (e : ℕ → ℕ)

lemma coeff_sparse (he : Set.InjOn e (range n)) (j : ℕ) (hj : j < n) :
    (∑ i ∈ range n, C (a i) * X ^ (e i)).coeff (e j) = a j := by
  rw [finsetSum_coeff, sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro i hi hij
    rw [coeff_C_mul_X_pow, if_neg]
    intro h
    exact hij (he (mem_coe.2 hi) (mem_coe.2 (mem_range.2 hj)) h.symm)
  · intro h; exact absurd (mem_range.2 hj) h

lemma coeff_sparse_out (k : ℕ) (hk : k ∉ (range n).image e) :
    (∑ i ∈ range n, C (a i) * X ^ (e i)).coeff k = 0 := by
  rw [finsetSum_coeff]
  refine sum_eq_zero fun i hi => ?_
  rw [coeff_C_mul_X_pow, if_neg]
  intro h; exact hk (mem_image.2 ⟨i, hi, h.symm⟩)

lemma support_sparse (he : Set.InjOn e (range n)) (ha : ∀ j < n, a j ≠ 0) :
    (∑ i ∈ range n, C (a i) * X ^ (e i)).support = (range n).image e := by
  ext k
  rw [mem_support_iff]
  constructor
  · intro h
    by_contra h'
    exact h (coeff_sparse_out n a e k h')
  · intro hk
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
    rw [coeff_sparse n a e he j (mem_range.1 hj)]
    exact ha j (mem_range.1 hj)

lemma natDegree_sparse (he : Set.InjOn e (range n)) (D : ℕ) (hD : ∀ j < n, e j ≤ D)
    (j0 : ℕ) (hj0 : j0 < n) (hej0 : e j0 = D) (ha : a j0 ≠ 0) :
    (∑ i ∈ range n, C (a i) * X ^ (e i)).natDegree = D := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (hD i (mem_range.1 hi))
  · rw [← hej0, coeff_sparse n a e he j0 hj0]; exact ha

lemma normsum_sparse (he : Set.InjOn e (range n)) (D : ℕ) (hD : ∀ j < n, e j ≤ D) :
    ∑ i ∈ range (D + 1), ‖(∑ j ∈ range n, C (a j) * X ^ (e j)).coeff i‖
      = ∑ j ∈ range n, ‖a j‖ := by
  have hsub : (range n).image e ⊆ range (D + 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
    exact mem_range.2 (Nat.lt_succ_of_le (hD j (mem_range.1 hj)))
  rw [← sum_subset hsub (fun k _ hk => by rw [coeff_sparse_out n a e k hk, norm_zero])]
  rw [sum_image (fun x hx y hy h => he hx hy h)]
  exact sum_congr rfl fun j hj => by rw [coeff_sparse n a e he j (mem_range.1 hj)]

end sparse

/-! ### Ratio of the end weight to a middle weight -/

lemma ratio_fac {K a b : ℝ} (hK : 2 ≤ K) (hb : 0 < b) (hab : K * b ≤ a) :
    a / (a - b) ≤ 1 + 2 / K ∧ b / (a - b) ≤ 2 / K := by
  have ha : 0 < a - b := by nlinarith
  have hKpos : 0 < K := by linarith
  have key : b ≤ 2 / K * (a - b) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]; nlinarith
  constructor
  · rw [div_le_iff₀ ha]; nlinarith [key]
  · rw [div_le_iff₀ ha]; exact key

lemma ratio_prod (n : ℕ) (x : ℕ → ℝ) (K : ℝ) (hK : 2 ≤ K) (h0 : x 0 = 0)
    (hpos : ∀ i, 1 ≤ i → i < n → 0 < x i)
    (hord : ∀ i j, 1 ≤ i → i < j → j < n → K * x i ≤ x j)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < n) :
    |∏ i ∈ (range n).erase 0, (x 0 - x i)| / |∏ i ∈ (range n).erase j, (x j - x i)|
      ≤ (1 + 2 / K) ^ n ∧
    (2 ≤ j → |∏ i ∈ (range n).erase 0, (x 0 - x i)| / |∏ i ∈ (range n).erase j, (x j - x i)|
      ≤ 2 / K * (1 + 2 / K) ^ n) := by
  have hj0 : j ∈ (range n).erase 0 := mem_erase.2 ⟨by omega, mem_range.2 hjn⟩
  have h0j : 0 ∈ (range n).erase j := mem_erase.2 ⟨by omega, mem_range.2 (by omega)⟩
  have hxj : 0 < x j := hpos j hj1 hjn
  have hA : |∏ i ∈ (range n).erase 0, (x 0 - x i)|
      = x j * ∏ i ∈ ((range n).erase 0).erase j, x i := by
    rw [abs_prod, ← mul_prod_erase _ _ hj0, h0]
    simp only [zero_sub, abs_neg]
    rw [abs_of_pos hxj]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_erase.1 hi
    have hi'' := mem_erase.1 hi'.2
    exact abs_of_pos (hpos i (Nat.one_le_iff_ne_zero.mpr hi''.1) (mem_range.1 hi''.2))
  have hB : |∏ i ∈ (range n).erase j, (x j - x i)|
      = x j * ∏ i ∈ ((range n).erase 0).erase j, |x j - x i| := by
    rw [abs_prod, ← mul_prod_erase _ _ h0j, h0, sub_zero, abs_of_pos hxj, erase_right_comm]
  have hT : ∀ i ∈ ((range n).erase 0).erase j, 1 ≤ i ∧ i < n ∧ i ≠ j := by
    intro i hi
    have hi' := mem_erase.1 hi
    have hi'' := mem_erase.1 hi'.2
    exact ⟨Nat.one_le_iff_ne_zero.mpr hi''.1, mem_range.1 hi''.2, hi'.1⟩
  have hfac : ∀ i ∈ ((range n).erase 0).erase j,
      0 ≤ x i / |x j - x i| ∧ x i / |x j - x i| ≤ 1 + 2 / K := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hT i hi
    refine ⟨div_nonneg (hpos i h1 h2).le (abs_nonneg _), ?_⟩
    rcases lt_or_gt_of_ne h3 with hlt | hgt
    · have := hord i j h1 hlt hjn
      rw [abs_of_pos (by nlinarith [hpos i h1 h2])]
      have := (ratio_fac hK (hpos i h1 h2) this).2
      have : (0:ℝ) ≤ 1 := zero_le_one
      linarith
    · have := hord j i hj1 hgt h2
      rw [abs_sub_comm, abs_of_pos (by nlinarith)]
      exact (ratio_fac hK hxj this).1
  have hratio : |∏ i ∈ (range n).erase 0, (x 0 - x i)| / |∏ i ∈ (range n).erase j, (x j - x i)|
      = ∏ i ∈ ((range n).erase 0).erase j, (x i / |x j - x i|) := by
    rw [hA, hB, mul_div_mul_left _ _ hxj.ne', prod_div_distrib]
  have hcard : #(((range n).erase 0).erase j) ≤ n := by
    calc #(((range n).erase 0).erase j) ≤ #((range n).erase 0) := card_erase_le
      _ ≤ #(range n) := card_erase_le
      _ = n := card_range n
  have h1K : (1 : ℝ) ≤ 1 + 2 / K := by
    have : 0 ≤ 2 / K := div_nonneg (by norm_num) (by linarith)
    linarith
  have hprod : ∀ S ⊆ ((range n).erase 0).erase j,
      ∏ i ∈ S, (x i / |x j - x i|) ≤ (1 + 2 / K) ^ n := by
    intro S hS
    calc ∏ i ∈ S, (x i / |x j - x i|) ≤ ∏ _i ∈ S, (1 + 2 / K) :=
          prod_le_prod (fun i hi => (hfac i (hS hi)).1) (fun i hi => (hfac i (hS hi)).2)
      _ = (1 + 2 / K) ^ #S := prod_const _
      _ ≤ (1 + 2 / K) ^ n := pow_le_pow_right₀ h1K ((card_le_card hS).trans hcard)
  refine ⟨by rw [hratio]; exact hprod _ subset_rfl, fun hj2 => ?_⟩
  have h1T : 1 ∈ ((range n).erase 0).erase j :=
    mem_erase.2 ⟨by omega, mem_erase.2 ⟨by omega, mem_range.2 (by omega)⟩⟩
  rw [hratio, ← mul_prod_erase _ _ h1T]
  have hord1 := hord 1 j le_rfl (by omega) hjn
  have hx1 : 0 < x 1 := hpos 1 le_rfl (by omega)
  have hf1 : x 1 / |x j - x 1| ≤ 2 / K := by
    rw [abs_of_pos (by nlinarith)]
    exact (ratio_fac hK hx1 hord1).2
  exact mul_le_mul hf1 (hprod _ (erase_subset _ _))
    (prod_nonneg fun i hi => (hfac i (erase_subset _ _ hi)).1)
    (div_nonneg (by norm_num) (by linarith))

lemma pow_le_lin (δ : ℝ) (hδ : 0 ≤ δ) : ∀ k : ℕ, k * δ ≤ 1 / 2 →
    (1 + δ) ^ k ≤ 1 + 2 * k * δ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    push_cast at hk ⊢
    have hk' : (k : ℝ) * δ ≤ 1 / 2 := by nlinarith
    have := ih hk'
    rw [pow_succ]
    have hkδ : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
    nlinarith

/-! ### The explicit exponents -/

def KK (m : ℕ) : ℕ := 200 * (m + 2)
def cc (m : ℕ) : ℕ := 100 * (m + 2) ^ 2 * KK m ^ (m + 1)
def rr (m : ℕ) : ℕ := 4 * cc m
def ex (m j : ℕ) : ℕ := if j = 0 then 0 else if j ≤ m then KK m ^ j else 2 ^ rr m

lemma KK_ge (m : ℕ) : 2 ≤ KK m := by unfold KK; omega

lemma cc_ge (m : ℕ) : 2 ≤ cc m := by
  unfold cc
  have h1 : 1 ≤ KK m ^ (m + 1) := Nat.one_le_pow _ _ (by have := KK_ge m; omega)
  have h2 : 1 ≤ (m + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

lemma two_pow_rr (m : ℕ) : 4 * cc m * cc m ≤ 2 ^ rr m := by
  have h := cc_ge m
  have h2 : cc m < 2 ^ cc m := Nat.lt_two_pow_self
  have h3 : cc m ^ 4 ≤ (2 ^ cc m) ^ 4 := Nat.pow_le_pow_left h2.le 4
  have h5 : 4 ≤ cc m * cc m := by nlinarith
  calc 4 * cc m * cc m = 4 * (cc m * cc m) := by ring
    _ ≤ (cc m * cc m) * (cc m * cc m) := Nat.mul_le_mul_right _ h5
    _ = cc m ^ 4 := by ring
    _ ≤ (2 ^ cc m) ^ 4 := h3
    _ = 2 ^ rr m := by rw [← pow_mul, rr, mul_comm]

lemma KKpow_le (m : ℕ) : KK m ^ (m + 1) ≤ 2 ^ rr m := by
  have h1 : KK m ^ (m + 1) ≤ cc m := by
    unfold cc; exact Nat.le_mul_of_pos_left _ (by positivity)
  have h2 := two_pow_rr m
  have h3 := cc_ge m
  nlinarith

lemma ex_zero (m : ℕ) : ex m 0 = 0 := by simp [ex]
lemma ex_mid (m j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) : ex m j = KK m ^ j := by
  simp [ex, h2, show j ≠ 0 by omega]
lemma ex_top (m : ℕ) : ex m (m + 1) = 2 ^ rr m := by simp [ex]

lemma ex_pos (m j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m + 1) : 1 ≤ ex m j := by
  rcases Nat.lt_or_ge j (m + 1) with h | h
  · rw [ex_mid m j h1 (by omega)]; exact Nat.one_le_pow _ _ (by have := KK_ge m; omega)
  · obtain rfl : j = m + 1 := by omega
    rw [ex_top]; exact Nat.one_le_two_pow

lemma ex_le (m j : ℕ) (h2 : j ≤ m + 1) : ex m j ≤ 2 ^ rr m := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · rw [ex_zero]; exact Nat.zero_le _
  rcases Nat.lt_or_ge j (m + 1) with h | h
  · rw [ex_mid m j h1 (by omega)]
    exact (Nat.pow_le_pow_right (by have := KK_ge m; omega) (by omega)).trans (KKpow_le m)
  · obtain rfl : j = m + 1 := by omega
    rw [ex_top]

lemma ex_ord (m i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ m + 1) :
    KK m * ex m i ≤ ex m j := by
  have hK := KK_ge m
  rw [ex_mid m i hi (by omega), ← pow_succ']
  rcases Nat.lt_or_ge j (m + 1) with h | h
  · rw [ex_mid m j (by omega) (by omega)]; exact Nat.pow_le_pow_right (by omega) (by omega)
  · obtain rfl : j = m + 1 := by omega
    rw [ex_top]; exact (Nat.pow_le_pow_right (by omega) (by omega)).trans (KKpow_le m)

lemma ex_lt (m i j : ℕ) (hij : i < j) (hj : j ≤ m + 1) : ex m i < ex m j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [ex_zero]; exact ex_pos m j (by omega) hj
  · have h1 := ex_pos m i hi (by omega)
    have h2 := ex_ord m i j hi hij hj
    have := KK_ge m
    nlinarith

lemma ex_inj (m : ℕ) : Set.InjOn (ex m) (range (m + 2)) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ex_lt m i j hlt (by omega)).ne h
  · exact (ex_lt m j i hgt (by omega)).ne h.symm

/-! ### Weights and the root -/

noncomputable def W (m j : ℕ) : ℝ := ∏ i ∈ (range (m + 2)).erase j, ((ex m j : ℝ) - ex m i)
noncomputable def qq (m : ℕ) : ℝ := |W m 0| / (2 * |W m (m + 1)|)
noncomputable def tt (m : ℕ) : ℝ := qq m ^ (((2 ^ rr m : ℕ) : ℝ)⁻¹)
noncomputable def aa (m j : ℕ) : ℂ :=
  (∏ i ∈ (range (m + 2)).erase j, ((ex m j : ℂ) - ex m i))⁻¹ / (tt m : ℂ) ^ (ex m j)

lemma W_ne (m j : ℕ) (hj : j < m + 2) : W m j ≠ 0 := by
  unfold W
  rw [prod_ne_zero_iff]
  intro i hi h
  have hi' := mem_erase.1 hi
  have : ex m j = ex m i := by exact_mod_cast sub_eq_zero.mp h
  exact hi'.1 (ex_inj m (mem_coe.2 hi'.2) (mem_coe.2 (mem_range.2 hj)) this.symm)

lemma W0_ge (m : ℕ) : 1 ≤ |W m 0| := by
  unfold W
  rw [abs_prod]
  calc (1:ℝ) = ∏ _i ∈ (range (m + 2)).erase 0, (1:ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one) (fun i hi => by
        have hi' := mem_erase.1 hi
        rw [ex_zero, Nat.cast_zero, zero_sub, abs_neg]
        have := ex_pos m i (Nat.one_le_iff_ne_zero.mpr hi'.1)
          (by have := mem_range.1 hi'.2; omega)
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast this)

lemma Wtop_le (m : ℕ) : |W m (m + 1)| ≤ ((2 : ℝ) ^ rr m) ^ (m + 1) := by
  unfold W
  rw [abs_prod]
  calc ∏ i ∈ (range (m + 2)).erase (m + 1), |(ex m (m + 1) : ℝ) - ex m i|
      ≤ ∏ _i ∈ (range (m + 2)).erase (m + 1), (2 : ℝ) ^ rr m :=
        prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => by
          have hi' := mem_erase.1 hi
          have h1 := ex_le m i (by have := mem_range.1 hi'.2; omega)
          have h1' : (ex m i : ℝ) ≤ (2 : ℝ) ^ rr m := by exact_mod_cast h1
          have h0 : (0 : ℝ) ≤ ex m i := Nat.cast_nonneg _
          rw [ex_top]; push_cast
          rw [abs_of_nonneg (by linarith)]
          linarith)
    _ = ((2 : ℝ) ^ rr m) ^ (m + 1) := by
        rw [prod_const, card_erase_of_mem (mem_range.2 (by omega)), card_range,
          show m + 2 - 1 = m + 1 by omega]

lemma qq_pos (m : ℕ) : 0 < qq m := by
  unfold qq
  have h1 := W0_ge m
  have h2 : 0 < |W m (m + 1)| := abs_pos.2 (W_ne m (m + 1) (by omega))
  positivity

lemma tt_pos (m : ℕ) : 0 < tt m := Real.rpow_pos_of_pos (qq_pos m) _

lemma tfac (m j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) :
    1 / tt m ^ (ex m j) ≤ 1 + 2 / (KK m : ℝ) := by
  have hq := qq_pos m
  have hEpos : (0 : ℝ) < ((2 ^ rr m : ℕ) : ℝ) := by positivity
  have hE2 : (2 : ℝ) ≤ (2 : ℝ) ^ rr m := by
    have : 1 ≤ rr m := by have := cc_ge m; unfold rr; omega
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rr m := pow_le_pow_right₀ (by norm_num) this
  have hKpos : (0 : ℝ) < (KK m : ℝ) := Nat.cast_pos.2 (by have := KK_ge m; omega)
  have hqinv : (qq m)⁻¹ ≤ (2 : ℝ) ^ (rr m * (m + 2)) := by
    have hW0 := W0_ge m
    have hWt := Wtop_le m
    have hWt0 : 0 < |W m (m + 1)| := abs_pos.2 (W_ne m (m + 1) (by omega))
    unfold qq
    rw [inv_div, div_le_iff₀ (by linarith)]
    have hpow : (2 : ℝ) ^ (rr m * (m + 2)) = ((2 : ℝ) ^ rr m) ^ (m + 1) * (2 : ℝ) ^ rr m := by
      rw [← pow_succ, ← pow_mul]
    rw [hpow]
    have hP : 0 ≤ ((2 : ℝ) ^ rr m) ^ (m + 1) := by positivity
    calc 2 * |W m (m + 1)| ≤ 2 * ((2 : ℝ) ^ rr m) ^ (m + 1) := by linarith
      _ ≤ (2 : ℝ) ^ rr m * ((2 : ℝ) ^ rr m) ^ (m + 1) := mul_le_mul_of_nonneg_right hE2 hP
      _ = ((2 : ℝ) ^ rr m) ^ (m + 1) * (2 : ℝ) ^ rr m * 1 := by ring
      _ ≤ ((2 : ℝ) ^ rr m) ^ (m + 1) * (2 : ℝ) ^ rr m * |W m 0| :=
          mul_le_mul_of_nonneg_left hW0 (by positivity)
  -- the exponent
  have hN : rr m * (m + 2) * ex m j * KK m ≤ 2 * 2 ^ rr m := by
    rw [ex_mid m j h1 h2]
    have hKj : KK m ^ j ≤ KK m ^ m := Nat.pow_le_pow_right (by have := KK_ge m; omega) h2
    have hcc : 100 * (m + 2) ^ 2 * KK m ^ m ≤ cc m := by
      calc 100 * (m + 2) ^ 2 * KK m ^ m ≤ 100 * (m + 2) ^ 2 * KK m ^ m * KK m :=
            Nat.le_mul_of_pos_right _ (by have := KK_ge m; omega)
        _ = cc m := by unfold cc; ring
    have hc : 100 * (m + 2) * (rr m * (m + 2) * KK m ^ m) ≤ 4 * cc m * cc m := by
      calc 100 * (m + 2) * (rr m * (m + 2) * KK m ^ m)
          = 4 * cc m * (100 * (m + 2) ^ 2 * KK m ^ m) := by unfold rr; ring
        _ ≤ 4 * cc m * cc m := Nat.mul_le_mul_left _ hcc
    calc rr m * (m + 2) * KK m ^ j * KK m ≤ rr m * (m + 2) * KK m ^ m * KK m := by gcongr
      _ = 2 * (100 * (m + 2) * (rr m * (m + 2) * KK m ^ m)) := by unfold KK; ring
      _ ≤ 2 * 2 ^ rr m := Nat.mul_le_mul_left 2 (hc.trans (two_pow_rr m))
  have hNR : ((rr m * (m + 2) : ℕ) : ℝ) * (ex m j : ℝ) * (KK m : ℝ)
      ≤ 2 * ((2 ^ rr m : ℕ) : ℝ) := by exact_mod_cast hN
  set p : ℝ := ((rr m * (m + 2) : ℕ) : ℝ) * ((((2 ^ rr m : ℕ) : ℝ))⁻¹ * (ex m j : ℝ)) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 2 / (KK m : ℝ) := by
    rw [le_div_iff₀ hKpos]
    calc p * KK m = (((rr m * (m + 2) : ℕ) : ℝ) * (ex m j : ℝ) * (KK m : ℝ))
          * (((2 ^ rr m : ℕ) : ℝ))⁻¹ := by rw [hp]; ring
      _ ≤ (2 * ((2 ^ rr m : ℕ) : ℝ)) * (((2 ^ rr m : ℕ) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hNR (inv_nonneg.2 hEpos.le)
      _ = 2 := by field_simp
  have hδ1 : 2 / (KK m : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hKpos]
    have : (2 : ℝ) ≤ KK m := by exact_mod_cast KK_ge m
    linarith
  have ht : 1 / tt m ^ (ex m j) = (qq m)⁻¹ ^ ((((2 ^ rr m : ℕ) : ℝ))⁻¹ * (ex m j : ℝ)) := by
    rw [tt, ← Real.rpow_mul_natCast hq.le, Real.inv_rpow hq.le, one_div]
  rw [ht]
  calc (qq m)⁻¹ ^ ((((2 ^ rr m : ℕ) : ℝ))⁻¹ * (ex m j : ℝ))
      ≤ ((2 : ℝ) ^ (rr m * (m + 2))) ^ ((((2 ^ rr m : ℕ) : ℝ))⁻¹ * (ex m j : ℝ)) :=
        Real.rpow_le_rpow (inv_nonneg.2 hq.le) hqinv (by positivity)
    _ = (1 + 1 : ℝ) ^ p := by
        rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ 1 + p * 1 := rpow_one_add_le_one_add_mul_self (by norm_num) hp0 (hp1.trans hδ1)
    _ ≤ 1 + 2 / (KK m : ℝ) := by linarith

end CE

open CE in
noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

open CE in
theorem erdos_990.variants.counterexample :
    ∀ n : ℕ, 1 ≤ n → ∃ f : ℂ[X], f.coeff 0 ≠ 0 ∧ f.support.card = n ∧ M f < 3 ∧
      ∃ x : ℝ, 0 < x ∧ f.rootMultiplicity (x : ℂ) = n - 1 := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    refine ⟨C 1, by simp, by rw [support_C one_ne_zero, card_singleton], ?_, 1, one_pos,
      by simp⟩
    simp [M]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpoly : poly (m + 2) (ex m) (tt m : ℂ) = ∑ j ∈ range (m + 2), C (aa m j) * X ^ (ex m j) :=
    rfl
  have ht := tt_pos m
  have hinj := ex_inj m
  have hnorm : ∀ j, ‖aa m j‖ = |W m j|⁻¹ / tt m ^ (ex m j) := by
    intro j
    have : aa m j = (((W m j)⁻¹ / tt m ^ (ex m j) : ℝ) : ℂ) := by
      simp only [aa, W]; push_cast; first | done | ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_inv, abs_pow, abs_of_pos ht]
  have hane : ∀ j < m + 2, aa m j ≠ 0 := by
    intro j hj h0
    have := hnorm j
    rw [h0, norm_zero] at this
    have hW := abs_pos.2 (W_ne m j hj)
    have : 0 < |W m j|⁻¹ / tt m ^ (ex m j) := by positivity
    linarith
  have hD : ∀ j < m + 2, ex m j ≤ 2 ^ rr m := fun j hj => ex_le m j (by omega)
  have hc0 : (poly (m + 2) (ex m) (tt m : ℂ)).coeff 0 = aa m 0 := by
    have := coeff_sparse (m + 2) (aa m) (ex m) hinj 0 (by omega)
    rw [ex_zero] at this
    rw [hpoly, this]
  have hdeg : (poly (m + 2) (ex m) (tt m : ℂ)).natDegree = 2 ^ rr m := by
    rw [hpoly]
    exact natDegree_sparse (m + 2) (aa m) (ex m) hinj _ hD (m + 1) (by omega) (ex_top m)
      (hane (m + 1) (by omega))
  have hlead : (poly (m + 2) (ex m) (tt m : ℂ)).leadingCoeff = aa m (m + 1) := by
    rw [leadingCoeff, hdeg, ← ex_top m, hpoly, coeff_sparse (m + 2) (aa m) (ex m) hinj (m + 1)
      (by omega)]
  have hinjC : Set.InjOn (fun j => (ex m j : ℂ)) (range (m + 2)) :=
    fun i hi j hj h => hinj hi hj (by simpa using h)
  obtain ⟨_, hmult⟩ := mult (m + 2) (by omega) (ex m) hinjC (tt m : ℂ)
    (Complex.ofReal_ne_zero.2 ht.ne')
  refine ⟨poly (m + 2) (ex m) (tt m : ℂ), ?_, ?_, ?_, tt m, ht, hmult⟩
  · rw [hc0]; exact hane 0 (by omega)
  · rw [hpoly, support_sparse (m + 2) (aa m) (ex m) hinj hane, card_image_of_injOn hinj,
      card_range]
  -- the bound on M
  set A := |W m 0|⁻¹ with hA
  have hW0 := W0_ge m
  have hApos : 0 < A := by positivity
  have hN0 : ‖aa m 0‖ = A := by rw [hnorm, ex_zero, pow_zero, div_one]
  have hNt : ‖aa m (m + 1)‖ = 2 * A := by
    rw [hnorm, ex_top, tt, Real.rpow_inv_natCast_pow (qq_pos m).le (by positivity), qq, hA]
    have hWt0 : 0 < |W m (m + 1)| := abs_pos.2 (W_ne m (m + 1) (by omega))
    field_simp
  set δ : ℝ := 2 / (KK m : ℝ) with hδ
  have hKR : (KK m : ℝ) = 200 * ((m : ℝ) + 2) := by unfold KK; push_cast; ring
  have hδ0 : 0 ≤ δ := by rw [hδ, hKR]; positivity
  have hmδ : (m : ℝ) * δ ≤ 1 / 100 := by
    rw [hδ, hKR, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hB : (1 + δ) ^ (m + 3) ≤ 103 / 100 := by
    have h3 : ((m + 3 : ℕ) : ℝ) * δ ≤ 3 / 200 := by
      rw [hδ, hKR, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      push_cast; nlinarith
    have := pow_le_lin δ hδ0 (m + 3) (by linarith)
    have h4 : 2 * ((m + 3 : ℕ) : ℝ) * δ ≤ 3 / 100 := by nlinarith
    linarith
  have hmid : ∀ j < m, ‖aa m (j + 1)‖ ≤ A * (103 / 100) * δ + (if j = 0 then A * (103 / 100) else 0) := by
    intro j hj
    obtain ⟨hr1, hr2⟩ := ratio_prod (m + 2) (fun i => (ex m i : ℝ)) (KK m : ℝ)
      (by exact_mod_cast KK_ge m) (by simp [ex_zero])
      (fun i h1 h2 => by have := ex_pos m i h1 (by omega); exact_mod_cast (show 0 < ex m i by omega))
      (fun i k h1 h2 h3 => by exact_mod_cast ex_ord m i k h1 h2 (by omega))
      (j + 1) (by omega) (by omega)
    have hW : ∀ k, W m k = ∏ i ∈ (range (m + 2)).erase k, ((ex m k : ℝ) - ex m i) := fun k => rfl
    rw [← hW 0, ← hW (j + 1)] at hr1 hr2
    have htf := tfac m (j + 1) (by omega) (by omega)
    have hWj : 0 < |W m (j + 1)| := abs_pos.2 (W_ne m (j + 1) (by omega))
    have hT : 0 < tt m ^ (ex m (j + 1)) := pow_pos ht _
    have hsplit : ‖aa m (j + 1)‖ = A * (|W m 0| / |W m (j + 1)|) * (1 / tt m ^ (ex m (j + 1))) := by
      rw [hnorm, hA]; field_simp
    have hRnn : 0 ≤ |W m 0| / |W m (j + 1)| := by positivity
    have hF0 : 0 ≤ 1 / tt m ^ (ex m (j + 1)) := by positivity
    have hpow : (1 + δ) ^ (m + 2) * (1 + δ) = (1 + δ) ^ (m + 3) := by ring
    rw [hsplit]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [if_true]
      have : A * (|W m 0| / |W m (0 + 1)|) * (1 / tt m ^ (ex m (0 + 1)))
          ≤ A * ((1 + δ) ^ (m + 2)) * (1 + δ) := by
        gcongr
      have hAδ : 0 ≤ A * (103 / 100) * δ := by positivity
      nlinarith
    · rw [if_neg (by omega)]
      have hr := hr2 (by omega)
      have : A * (|W m 0| / |W m (j + 1)|) * (1 / tt m ^ (ex m (j + 1)))
          ≤ A * (δ * (1 + δ) ^ (m + 2)) * (1 + δ) := by
        gcongr
      have he : A * (δ * (1 + δ) ^ (m + 2)) * (1 + δ) = (A * δ) * (1 + δ) ^ (m + 3) := by ring
      have hle := mul_le_mul_of_nonneg_left hB (show 0 ≤ A * δ by positivity)
      linarith
  have hsum : ∑ j ∈ range (m + 2), ‖aa m j‖
      = ‖aa m 0‖ + ∑ j ∈ range m, ‖aa m (j + 1)‖ + ‖aa m (m + 1)‖ := by
    rw [sum_range_succ, sum_range_succ', add_comm (∑ j ∈ range m, _) _]
  have hmidsum : ∑ j ∈ range m, ‖aa m (j + 1)‖ ≤ m * (A * (103 / 100) * δ) + A * (103 / 100) := by
    calc ∑ j ∈ range m, ‖aa m (j + 1)‖
        ≤ ∑ j ∈ range m, (A * (103 / 100) * δ + (if j = 0 then A * (103 / 100) else 0)) :=
          sum_le_sum fun j hj => hmid j (mem_range.1 hj)
      _ = m * (A * (103 / 100) * δ) + (if 0 ∈ range m then A * (103 / 100) else 0) := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_ite_eq']
      _ ≤ m * (A * (103 / 100) * δ) + A * (103 / 100) := by
          split_ifs <;> nlinarith
  unfold M
  rw [hdeg, hpoly, normsum_sparse (m + 2) (aa m) (ex m) hinj _ hD, ← hpoly, hc0, hlead, hsum,
    hN0, hNt]
  have hsq : 136 / 100 * A ≤ Real.sqrt (A * (2 * A)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  have hsqpos : 0 < Real.sqrt (A * (2 * A)) := by positivity
  rw [div_lt_iff₀ hsqpos]
  have : (m : ℝ) * (A * (103 / 100) * δ) ≤ A * (103 / 100) / 100 := by
    have := mul_le_mul_of_nonneg_left hmδ (show 0 ≤ A * (103 / 100) by positivity)
    nlinarith
  nlinarith

open scoped Classical in
noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

lemma CE.countP_card {α : Type*} (p : α → Prop) (inst : DecidablePred p) (s : Multiset α)
    (h : ∀ a ∈ s, p a) : @Multiset.countP α p inst s = Multiset.card s :=
  Multiset.countP_eq_card.mpr h

lemma CE.count_ge (f : ℂ[X]) (x : ℝ) (hx : 0 < x) :
    f.rootMultiplicity (x : ℂ) ≤ rootArgCount f (Set.Icc 0 0) := by
  classical
  have hle : Multiset.replicate (f.rootMultiplicity (x : ℂ)) (x : ℂ) ≤ f.roots :=
    Multiset.le_count_iff_replicate_le.mp (by rw [count_roots])
  unfold rootArgCount
  convert Multiset.countP_le_of_le _ hle using 1
  rw [CE.countP_card _ _ _ ?_]
  · simp
  · intro a ha
    rw [Multiset.eq_of_mem_replicate ha, Complex.arg_ofReal_of_nonneg hx.le]
    simp

lemma CE.M_nonneg (f : ℂ[X]) : 0 ≤ M f := by
  unfold M
  exact div_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (Real.sqrt_nonneg _)

lemma CE.log_le (y : ℝ) (h0 : 0 ≤ y) (h3 : y < 3) : Real.log y ≤ 3 := by
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; norm_num
  · have := Real.log_le_sub_one_of_pos h
    linarith

theorem erdos_990 :
    ¬ ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
  rintro ⟨C, hC⟩
  set N : ℕ := ⌈3 * C ^ 2⌉₊ with hN
  have hN3 : 3 * C ^ 2 ≤ N := Nat.le_ceil _
  obtain ⟨f, hf0, hcard, hM, x, hx, hmult⟩ :=
    erdos_990.variants.counterexample (N + 2) (by omega)
  have h := hC f hf0 0 0 le_rfl le_rfl (by positivity)
  have hcnt := CE.count_ge f x hx
  rw [hmult, show N + 2 - 1 = N + 1 by omega] at hcnt
  have hcntR : (N : ℝ) + 1 ≤ (rootArgCount f (Set.Icc 0 0) : ℝ) := by exact_mod_cast hcnt
  simp only [sub_self, zero_div, zero_mul, sub_zero] at h
  rw [abs_of_nonneg (Nat.cast_nonneg _), hcard] at h
  push_cast at h
  have hlog := CE.log_le (M f) (CE.M_nonneg f) hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hS : Real.sqrt (((N : ℝ) + 2) * Real.log (M f)) ≤ Real.sqrt (((N : ℝ) + 2) * 3) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hS0 : 0 ≤ Real.sqrt (((N : ℝ) + 2) * Real.log (M f)) := Real.sqrt_nonneg _
  have h1 : (N : ℝ) + 1 ≤ |C| * Real.sqrt (((N : ℝ) + 2) * 3) := by
    calc (N : ℝ) + 1 ≤ C * Real.sqrt (((N : ℝ) + 2) * Real.log (M f)) := hcntR.trans h
      _ ≤ |C| * Real.sqrt (((N : ℝ) + 2) * Real.log (M f)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * Real.sqrt (((N : ℝ) + 2) * 3) := mul_le_mul_of_nonneg_left hS (abs_nonneg C)
  have h2 : ((N : ℝ) + 1) ^ 2 ≤ (|C| * Real.sqrt (((N : ℝ) + 2) * 3)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow, sq_abs, Real.sq_sqrt (by positivity)] at h2
  nlinarith

end Erdos990

#print axioms Erdos990.erdos_990.variants.counterexample
#print axioms Erdos990.erdos_990
