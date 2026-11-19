import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Statements restated from FormalConjectures/ErdosProblems/350.lean (Erdos350). -/

namespace Erdos350

def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M] (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id

namespace HS

open Finset

/-- Abel summation. -/
lemma abel (c d D : ℕ → ℝ) (hD : ∀ j, D (j + 1) = D j + d j) (hD0 : D 0 = 0) (k : ℕ) :
    ∑ i ∈ range k, c i * d i =
      ∑ j ∈ range k, (c j - c (j + 1)) * D (j + 1) + c k * D k := by
  induction k with
  | zero => simp [hD0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun j => (c j - c (j + 1)) * D (j + 1)), hD k]
    ring

/-- Chord slope. -/
noncomputable def S (φ : ℝ → ℝ) (u v : ℝ) : ℝ := (φ u - φ v) / (u - v)

lemma S_symm (φ : ℝ → ℝ) (u v : ℝ) : S φ u v = S φ v u := by
  unfold S
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

lemma S_mono (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Ioi 0) φ) {x y x' y' : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x') (hyy : y ≤ y') (hxy : x ≠ y) (hxy' : x' ≠ y') :
    S φ x y ≤ S φ x' y' := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  by_cases h : x' = y
  · have h2 : y' ≠ x := by
      intro h2; apply hxy; linarith
    have e1 : S φ y x ≤ S φ y' x :=
      hφ.secant_mono (a := x) hx hy hy' (Ne.symm hxy) h2 hyy
    have e2 : S φ x y' ≤ S φ x' y' :=
      hφ.secant_mono (a := y') hy' hx hx' (Ne.symm h2) hxy' hxx
    rw [S_symm φ x y, S_symm φ y' x] at *
    linarith [S_symm φ y' x, S_symm φ x y']
  · have e1 : S φ x y ≤ S φ x' y :=
      hφ.secant_mono (a := y) hy hx hx' hxy h hxx
    have e2 : S φ y x' ≤ S φ y' x' :=
      hφ.secant_mono (a := x') hx' hy hy' (Ne.symm h) (Ne.symm hxy') hyy
    rw [S_symm φ y x', S_symm φ y' x'] at e2
    linarith

lemma S_nonpos (φ : ℝ → ℝ) (hanti : ∀ x y, 0 < x → x ≤ y → φ y ≤ φ x) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) : S φ x y ≤ 0 := by
  unfold S
  rcases lt_or_gt_of_ne hxy with h | h
  · have := hanti x y hx h.le
    exact div_nonpos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
  · have := hanti y x hy h.le
    exact div_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)

/-- Weak majorization against the powers of two. -/
lemma core (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Ioi 0) φ)
    (hanti : ∀ x y, 0 < x → x ≤ y → φ y ≤ φ x) (a : ℕ → ℝ) (k : ℕ)
    (ha : ∀ i < k, 1 ≤ a i) (hm : ∀ i, i + 1 < k → a i ≤ a (i + 1))
    (hS : ∀ j ≤ k, ∑ i ∈ range j, (2 : ℝ) ^ i ≤ ∑ i ∈ range j, a i) :
    ∑ i ∈ range k, φ (a i) ≤ ∑ i ∈ range k, φ ((2 : ℝ) ^ i) := by
  set b : ℕ → ℝ := fun i => (2 : ℝ) ^ i with hb
  have hbpos : ∀ i, 0 < b i := fun i => by positivity
  have hb2 : ∀ i, b (i + 1) = 2 * b i := fun i => by simp only [hb, pow_succ]; ring
  set q : ℕ → ℝ := fun i => if a i = b i then 2 * b i else b i with hq
  have hq1 : ∀ i, b i ≤ q i := fun i => by
    simp only [hq]; split_ifs <;> linarith [hbpos i]
  have hq2 : ∀ i, q i ≤ b (i + 1) := fun i => by
    simp only [hq]; split_ifs <;> linarith [hbpos i, hb2 i]
  have hq3 : ∀ i, a i ≠ q i := fun i => by
    simp only [hq]; split_ifs with h
    · intro h2; have := hbpos i; linarith
    · exact h
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (hbpos i) (hq1 i)
  set c : ℕ → ℝ := fun i => if i < k then -S φ (a i) (q i) else 0 with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    simp only [hc]; split_ifs with h
    · have := S_nonpos φ hanti (by linarith [ha i h]) (hqpos i) (hq3 i); linarith
    · exact le_rfl
  have hcanti : ∀ j, c (j + 1) ≤ c j := fun j => by
    by_cases hj : j + 1 < k
    · simp only [hc, if_pos hj, if_pos (by omega : j < k)]
      have := S_mono φ hφ (by linarith [ha j (by omega)]) (hqpos j) (hm j hj)
        ((hq2 j).trans (hq1 (j + 1))) (hq3 j) (hq3 (j + 1))
      linarith
    · have : c (j + 1) = 0 := by simp only [hc, if_neg hj]
      rw [this]; exact hc0 j
  have hkey : ∀ i < k, φ (a i) - φ (b i) = c i * (b i - a i) := fun i hi => by
    simp only [hc, if_pos hi]
    by_cases h : a i = b i
    · rw [h]; ring
    · have hqi : q i = b i := by simp only [hq, if_neg h]
      rw [hqi]
      unfold S
      have hne : a i - b i ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring
  set d : ℕ → ℝ := fun i => b i - a i with hd
  set D : ℕ → ℝ := fun j => ∑ i ∈ range j, d i with hD
  have hDle : ∀ j ≤ k, D j ≤ 0 := fun j hj => by
    simp only [hD, hd, Finset.sum_sub_distrib]
    have := hS j hj
    simp only [hb]
    linarith
  have hab := abel c d D (fun j => by simp only [hD, Finset.sum_range_succ]) (by simp [hD]) k
  have hck : c k = 0 := by simp only [hc, if_neg (lt_irrefl k)]
  rw [hck, zero_mul, add_zero] at hab
  have hsum : ∑ i ∈ range k, φ (a i) - ∑ i ∈ range k, φ (b i) =
      ∑ i ∈ range k, c i * d i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hkey i (Finset.mem_range.mp hi)
  have hnp : ∑ j ∈ range k, (c j - c (j + 1)) * D (j + 1) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have h1 : 0 ≤ c j - c (j + 1) := by linarith [hcanti j]
    have h2 := hDle (j + 1) (Finset.mem_range.mp hj)
    nlinarith
  have : ∑ i ∈ range k, φ (a i) - ∑ i ∈ range k, φ (b i) ≤ 0 := by
    rw [hsum, hab]; exact hnp
  simp only [hb] at this
  linarith

/-- `x ↦ x ^ (-s)` is convex on `(0, ∞)`. -/
lemma convex_rpow_neg (s : ℝ) (hs : 0 < s) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ (-s)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ioi] at hx hy
  simp only [smul_eq_mul]
  have hxy : 0 < a * x + b * y := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_add] at hab; rw [hab]; simp; exact hy
    · have : 0 ≤ b * y := by positivity
      have : 0 < a * x := by positivity
      linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
    ha hb hab
  simp only [smul_eq_mul] at hlog
  rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  have hexp := convexOn_exp.2 (Set.mem_univ (Real.log x * -s)) (Set.mem_univ (Real.log y * -s))
    ha hb hab
  simp only [smul_eq_mul] at hexp
  calc Real.exp (Real.log (a * x + b * y) * -s)
      ≤ Real.exp (a * (Real.log x * -s) + b * (Real.log y * -s)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
    _ ≤ _ := hexp

lemma anti_rpow_neg (s : ℝ) (hs : 0 < s) :
    ∀ x y : ℝ, 0 < x → x ≤ y → y ^ (-s) ≤ x ^ (-s) := by
  intro x y hx hxy
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hx.le hxy hs.le)

lemma two_pow_sum (j : ℕ) : ∑ i ∈ range j, 2 ^ i + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

end HS

open Finset in
theorem erdos_350.variants.strengthening (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A)
    (s : ℝ) (hs : 0 < s) : ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s)) := by
  obtain ⟨k, hk⟩ : ∃ k, A.card = k := ⟨_, rfl⟩
  set E := A.orderEmbOfFin hk
  set e : ℕ → ℕ := fun i => if h : i < k then E ⟨i, h⟩ else 0 with he
  have hemem : ∀ i < k, e i ∈ A := fun i hi => by
    simp only [he, dif_pos hi]; exact Finset.orderEmbOfFin_mem A hk _
  have helt : ∀ i j, i < j → j < k → e i < e j := by
    intro i j hij hj
    simp only [he, dif_pos hj, dif_pos (hij.trans hj)]
    exact E.strictMono (Fin.mk_lt_mk.mpr hij)
  have hinj : ∀ i j, i < k → j < k → e i = e j → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (helt i j h hj).ne
    · exact h
    · exact absurd hij (helt j i h hi).ne'
  have h0 : 0 ∉ A := by
    intro h0
    have := hA {0} (by simpa using h0) ∅ (Finset.empty_subset _) (by simp)
    simp at this
  have hpos : ∀ i < k, 1 ≤ e i := fun i hi =>
    Nat.one_le_iff_ne_zero.mpr (fun h => h0 (h ▸ hemem i hi))
  -- the image of `e` is `A`
  have himg : (range k).image e = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hemem i hi
    · rw [hk, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  -- partial sums
  have hpart : ∀ j ≤ k, 2 ^ j ≤ ∑ i ∈ range j, e i + 1 := by
    intro j hj
    set T := (range j).image e with hT
    have hTA : T ⊆ A := by
      intro x hx
      simp only [hT, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hemem i (by omega)
    have hTcard : T.card = j := by
      rw [hT, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j' hj' hij
      exact hinj i j' (by simp at hi; omega) (by simp at hj'; omega) hij
    have hTsum : T.sum id = ∑ i ∈ range j, e i := by
      rw [hT, Finset.sum_image]
      · rfl
      · intro i hi j' hj' hij
        exact hinj i j' (by simp at hi; omega) (by simp at hj'; omega) hij
    have hc : T.powerset.card ≤ (range (T.sum id + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun X => X.sum id)
      · intro X hX
        simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
          Finset.coe_subset] at hX
        simp only [Finset.coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Finset.sum_le_sum_of_subset hX)
      · intro X hX Y hY hXY
        simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
          Finset.coe_subset] at hX hY
        by_contra hne
        exact hA X (hX.trans hTA) Y (hY.trans hTA) hne hXY
    rw [Finset.card_powerset, hTcard, Finset.card_range, hTsum] at hc
    exact hc
  -- real data
  set a : ℕ → ℝ := fun i => (e i : ℝ) with ha
  have hcore := HS.core (fun x : ℝ => x ^ (-s)) (HS.convex_rpow_neg s hs)
    (HS.anti_rpow_neg s hs) a k
    (fun i hi => by simp only [ha]; exact_mod_cast hpos i hi)
    (fun i hi => by simp only [ha]; exact_mod_cast (helt i (i + 1) (by omega) hi).le)
    (fun j hj => by
      have h1 := hpart j hj
      have h2 := HS.two_pow_sum j
      have h3 : (∑ i ∈ range j, 2 ^ i : ℕ) ≤ ∑ i ∈ range j, e i := by omega
      simp only [ha]
      exact_mod_cast h3)
  have hsumA : ∑ n ∈ A, (1 / n : ℝ) ^ s = ∑ i ∈ range k, (a i) ^ (-s) := by
    rw [← himg, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      have hp : (0 : ℝ) < e i := by exact_mod_cast hpos i (Finset.mem_range.mp hi)
      simp only [ha]
      rw [one_div, Real.inv_rpow hp.le, Real.rpow_neg hp.le]
    · intro i hi j hj hij
      exact hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  rw [hsumA]
  refine lt_of_le_of_lt hcore ?_
  -- geometric sum
  set r : ℝ := (2 : ℝ) ^ (-s) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ i : ℕ, ((2 : ℝ) ^ i) ^ (-s) = r ^ i := by
    intro i
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  simp only [hterm]
  rw [geom_sum_eq hr1.ne k]
  have hrk : 0 < r ^ k := by positivity
  have h1r : 0 < 1 - r := by linarith
  rw [show (r ^ k - 1) / (r - 1) = (1 - r ^ k) / (1 - r) by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]]
  rw [div_lt_div_iff_of_pos_right h1r]
  linarith

theorem erdos_350 (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) :
    ∑ n ∈ A, (1 / n : ℝ) < 2 := by
  have h := erdos_350.variants.strengthening A hA 1 one_pos
  simp only [Real.rpow_one, Real.rpow_neg_one] at h
  norm_num at h
  simpa only [one_div] using h

end Erdos350

#print axioms Erdos350.erdos_350.variants.strengthening
#print axioms Erdos350.erdos_350
