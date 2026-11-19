import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.Linarith

/-- Restated from FormalConjecturesForMathlib/NumberTheory/DiophantineApproximation/ZNumber.lean -/
def IsZNumber (ξ : ℝ) : Prop :=
  0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Int.fract (ξ * (3 / 2 : ℝ) ^ n) < 1 / 2

namespace Bugeaud09

/-- Mahler's recursion: the integer part at step `n+1` is determined by the one at step `n`. -/
lemma step (x : ℝ) (h0 : Int.fract x < 1 / 2) (h1 : Int.fract (x * (3 / 2)) < 1 / 2) :
    ⌊x * (3 / 2)⌋ = (3 * ⌊x⌋ + 1) / 2 := by
  obtain ⟨m, e, he, hm⟩ : ∃ m e : ℤ, (e = 0 ∨ e = 1) ∧ 3 * ⌊x⌋ + 1 = 2 * m + e :=
    ⟨(3 * ⌊x⌋ + 1) / 2, (3 * ⌊x⌋ + 1) % 2, by omega, by omega⟩
  have hdiv : (3 * ⌊x⌋ + 1) / 2 = m := by omega
  rw [hdiv]
  have hm' : (3 : ℝ) * ⌊x⌋ + 1 = 2 * m + e := by exact_mod_cast hm
  have he' : (0 : ℝ) ≤ e ∧ (e : ℝ) ≤ 1 := by
    rcases he with rfl | rfl
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
  unfold Int.fract at h0 h1
  have hg := Int.floor_le x
  have hF := Int.floor_le (x * (3 / 2))
  have a : (⌊x * (3 / 2)⌋ : ℝ) < m + 1 := by linarith [he'.1, he'.2]
  have b : (m : ℝ) - 1 < ⌊x * (3 / 2)⌋ := by linarith [he'.1, he'.2]
  have a' : ⌊x * (3 / 2)⌋ < m + 1 := by exact_mod_cast a
  have b' : m - 1 < ⌊x * (3 / 2)⌋ := by exact_mod_cast b
  omega

lemma rec {ξ : ℝ} (hξ : IsZNumber ξ) (n : ℕ) (hn : 1 ≤ n) :
    ⌊ξ * (3 / 2 : ℝ) ^ (n + 1)⌋ = (3 * ⌊ξ * (3 / 2 : ℝ) ^ n⌋ + 1) / 2 := by
  have e : ξ * (3 / 2 : ℝ) ^ (n + 1) = ξ * (3 / 2 : ℝ) ^ n * (3 / 2) := by
    rw [pow_succ, mul_assoc]
  rw [e]
  refine step _ (hξ.2 n hn) ?_
  rw [← e]
  exact hξ.2 (n + 1) (by omega)

lemma floor_eq {ξ η : ℝ} (hξ : IsZNumber ξ) (hη : IsZNumber η)
    (h : ⌊ξ * (3 / 2 : ℝ) ^ 1⌋ = ⌊η * (3 / 2 : ℝ) ^ 1⌋) :
    ∀ n : ℕ, ⌊ξ * (3 / 2 : ℝ) ^ (n + 1)⌋ = ⌊η * (3 / 2 : ℝ) ^ (n + 1)⌋ := by
  intro n
  induction n with
  | zero => exact h
  | succ k ih => rw [rec hξ (k + 1) (by omega), rec hη (k + 1) (by omega), ih]

lemma diff_lt {ξ η : ℝ} (hξ : IsZNumber ξ) (hη : IsZNumber η)
    (h : ⌊ξ * (3 / 2 : ℝ) ^ 1⌋ = ⌊η * (3 / 2 : ℝ) ^ 1⌋) (n : ℕ) :
    |ξ - η| * (3 / 2 : ℝ) ^ (n + 1) < 1 := by
  have h1 := hξ.2 (n + 1) (by omega)
  have h2 := hη.2 (n + 1) (by omega)
  have h3 := Int.fract_nonneg (ξ * (3 / 2 : ℝ) ^ (n + 1))
  have h4 := Int.fract_nonneg (η * (3 / 2 : ℝ) ^ (n + 1))
  unfold Int.fract at h1 h2 h3 h4
  rw [floor_eq hξ hη h n] at h1 h3
  have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (n + 1) := pow_nonneg (by norm_num) _
  rw [← abs_of_nonneg hp, ← abs_mul, abs_lt, sub_mul]
  constructor <;> linarith

lemma injOn : Set.InjOn (fun ξ : ℝ => ⌊ξ * (3 / 2 : ℝ) ^ 1⌋) {ξ | IsZNumber ξ} := by
  intro ξ hξ η hη h
  by_contra hne
  have hd : 0 < |ξ - η| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |ξ - η|) (by norm_num : (1 : ℝ) < 3 / 2)
  have key := diff_lt hξ hη h n
  have hpow : (3 / 2 : ℝ) ^ n ≤ (3 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : 1 < |ξ - η| * (3 / 2 : ℝ) ^ n := by
    rw [div_lt_iff₀ hd] at hn
    linarith
  have h6 : |ξ - η| * (3 / 2 : ℝ) ^ n ≤ |ξ - η| * (3 / 2 : ℝ) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hpow hd.le
  linarith

/-- Mahler: there are only countably many Z-numbers. -/
lemma countable : {ξ : ℝ | IsZNumber ξ}.Countable :=
  Set.MapsTo.countable_of_injOn (Set.mapsTo_univ _ _) injOn Set.countable_univ

theorem problem_10_9.variants.measure_zero :
    MeasureTheory.volume {ξ : ℝ | IsZNumber ξ} = 0 :=
  countable.measure_zero _

theorem problem_10_9.variants.dimH_lt_one :
    dimH {ξ : ℝ | IsZNumber ξ} < 1 := by
  rw [countable.dimH_zero]
  exact zero_lt_one

end Bugeaud09

#print axioms Bugeaud09.problem_10_9.variants.measure_zero
#print axioms Bugeaud09.problem_10_9.variants.dimH_lt_one
