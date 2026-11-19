import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Filter

namespace Erdos999

def IsApproximable (f : ℕ → ℝ) (x : ℝ) : Prop :=
  {q : ℕ | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}.Infinite

lemma card_T (q : ℕ) :
    ((Finset.range (3 * q)).filter (fun n => Nat.Coprime q n)).card ≤ 3 * Nat.totient q := by
  have hsub : (Finset.range (3 * q)).filter (fun n => Nat.Coprime q n) ⊆
      ((Finset.Ico 0 (0 + q)).filter (fun n => Nat.Coprime q n) ∪
        (Finset.Ico q (q + q)).filter (fun n => Nat.Coprime q n)) ∪
        (Finset.Ico (q + q) (q + q + q)).filter (fun n => Nat.Coprime q n) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    by_cases h1 : n < q
    · left; left; exact ⟨⟨by omega, by omega⟩, hn.2⟩
    by_cases h2 : n < q + q
    · left; right; exact ⟨⟨by omega, by omega⟩, hn.2⟩
    right; exact ⟨⟨by omega, by omega⟩, hn.2⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  rw [Nat.filter_coprime_Ico_eq_totient, Nat.filter_coprime_Ico_eq_totient,
    Nat.filter_coprime_Ico_eq_totient]
  omega

theorem erdos_999.variants.easy_direction (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (h : ∀ᵐ x : ℝ, IsApproximable f x) :
    ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q := by
  intro hs
  set g := fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => by
    simp only [hg]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf q)) (Nat.cast_nonneg _)
  have hev : ∀ᶠ q : ℕ in atTop, g q < 1 / 2 :=
    hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨Q0, hQ0⟩ := eventually_atTop.1 hev
  set Q1 := max Q0 1 with hQ1
  let S : ℕ → Set ℝ := fun q => if Q1 ≤ q then
    ⋃ p ∈ (Finset.range (3 * q)).filter (fun n => Nat.Coprime q n),
      Metric.ball ((p : ℝ) / q) (f q / q) else ∅
  have hmeas : ∀ q, volume (S q) ≤ ENNReal.ofReal (6 * g q) := by
    intro q
    by_cases hq : Q1 ≤ q
    · simp only [S, if_pos hq]
      refine (measure_biUnion_finset_le _ _).trans ?_
      simp only [Real.volume_ball, Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hc : (((Finset.range (3 * q)).filter (fun n => Nat.Coprime q n)).card : ℝ)
          ≤ 3 * (Nat.totient q : ℝ) := by exact_mod_cast card_T q
      have hfq : 0 ≤ 2 * (f q / q) :=
        mul_nonneg (by norm_num) (div_nonneg (hf q) (Nat.cast_nonneg _))
      have := mul_le_mul_of_nonneg_right hc hfq
      have he : 6 * g q = 3 * (Nat.totient q : ℝ) * (2 * (f q / q)) := by
        simp only [hg]; ring
      rw [he]; exact this
    · simp only [S, if_neg hq, measure_empty]
      exact zero_le
  have hsum : ∑' q, volume (S q) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeas)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => mul_nonneg (by norm_num) (hg0 q))
      (hs.mul_left 6)]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem hsum
  have mem : ∀ q, Q1 ≤ q → ∀ x : ℝ, x ∈ Set.Ico (1 : ℝ) 2 → ∀ p : ℤ, Int.gcd p q = 1 →
      |x - p / q| < f q / q → x ∈ S q := by
    intro q hq x hx p hp hxp
    have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hgq : g q < 1 / 2 := hQ0 q (le_trans (le_max_left _ _) hq)
    have htot : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.2 hq1
    have hfq : f q / q < 1 / 2 := by
      have h1 : f q / q ≤ g q := by
        simp only [hg]
        rw [mul_div_assoc]
        have : 0 ≤ f q / q := div_nonneg (hf q) (Nat.cast_nonneg _)
        nlinarith
      linarith
    rw [abs_lt] at hxp
    obtain ⟨hx1, hx2⟩ := hx
    have hp1 : (1 : ℝ) / 2 < p / q := by linarith [hxp.2]
    have hp2 : (p : ℝ) / q < 5 / 2 := by linarith [hxp.1]
    have hp1' : (0 : ℝ) < p := by
      have := (lt_div_iff₀ hqpos).1 hp1
      linarith
    have hp2' : (p : ℝ) < 3 * q := by
      have := (div_lt_iff₀ hqpos).1 hp2
      linarith
    have hp0 : 0 ≤ p := by exact_mod_cast hp1'.le
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, (Int.toNat_of_nonneg hp0).symm⟩
    simp only [Int.cast_natCast] at hp2' hxp
    simp only [S, if_pos hq]
    rw [Set.mem_iUnion₂]
    refine ⟨n, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by exact_mod_cast hp2', ?_⟩
      have : Nat.gcd n q = 1 := by
        rw [← Int.gcd_natCast_natCast]; exact hp
      exact Nat.Coprime.symm this
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hxp.1, hxp.2]
  have hzero : volume (Set.Ico (1 : ℝ) 2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h, hae] with x hx hx2 hmem
    obtain ⟨Q2, hQ2⟩ := eventually_atTop.1 hx2
    obtain ⟨q, hq, hqgt⟩ := hx.exists_gt (max Q1 Q2)
    obtain ⟨_, p, hp, hxp⟩ := hq
    exact hQ2 q (by omega) (mem q (by omega) x hmem p hp hxp)
  rw [Real.volume_Ico] at hzero
  norm_num at hzero

end Erdos999

#print axioms Erdos999.erdos_999.variants.easy_direction
