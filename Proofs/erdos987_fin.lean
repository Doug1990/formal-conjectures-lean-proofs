import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

/-- Restated from FormalConjecturesForMathlib/Analysis/SpecialFunctions/AdditiveCharacter.lean. -/
noncomputable def additiveChar (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[inherit_doc]
scoped[ExponentialSum] notation "e" => additiveChar

open scoped ExponentialSum

namespace Erdos987

noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

namespace FD

lemma re_e (t : ℝ) : (e t).re = Real.cos (2 * Real.pi * t) := by
  unfold additiveChar
  exact Complex.exp_ofReal_mul_I_re _

lemma cos_pos_of (a b : ℝ) (h : ⌊4 * Int.fract a⌋₊ = ⌊4 * Int.fract b⌋₊) :
    0 < Real.cos (2 * Real.pi * (b - a)) := by
  have ha0 := Int.fract_nonneg a
  have hb0 := Int.fract_nonneg b
  have h1 := Nat.floor_le (show 0 ≤ 4 * Int.fract a by positivity)
  have h2 := Nat.lt_floor_add_one (4 * Int.fract a)
  have h3 := Nat.floor_le (show 0 ≤ 4 * Int.fract b by positivity)
  have h4 := Nat.lt_floor_add_one (4 * Int.fract b)
  rw [h] at h1 h2
  set δ := Int.fract b - Int.fract a with hδ
  have hd1 : δ < 1 / 4 := by linarith
  have hd2 : -(1 / 4) < δ := by linarith
  have ea := Int.floor_add_fract a
  have eb := Int.floor_add_fract b
  have key : 2 * Real.pi * (b - a) = 2 * Real.pi * δ + ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [hδ]
    linear_combination (2 * Real.pi) * (ea - eb)
  rw [key, Real.cos_add_int_mul_two_pi]
  have hpi := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith

lemma key (S : Finset ℝ) (L i j : ℕ) (hij : i < j)
    (h : ∀ y ∈ S, ⌊4 * Int.fract ((i : ℝ) * L * y)⌋₊ = ⌊4 * Int.fract ((j : ℝ) * L * y)⌋₊) :
    ∀ y ∈ S, 0 < Real.cos (2 * Real.pi * ((((j - i) * L : ℕ) : ℝ) * y)) := by
  intro y hy
  have := cos_pos_of _ _ (h y hy)
  convert this using 2
  push_cast [Nat.cast_sub hij.le]
  ring

lemma exists_k (S : Finset ℝ) (a : ℕ) :
    ∃ k : ℕ, a ≤ k ∧ ∀ y ∈ S, 0 < Real.cos (2 * Real.pi * ((k : ℝ) * y)) := by
  let L : ℕ := a + 1
  let g : Fin (Fintype.card (S → Fin 4) + 1) → (S → Fin 4) := fun j y =>
    ⟨⌊4 * Int.fract (((j : ℕ) : ℝ) * L * (y : ℝ))⌋₊, by
      have h1 := Int.fract_lt_one (((j : ℕ) : ℝ) * L * (y : ℝ))
      have h0 := Int.fract_nonneg (((j : ℕ) : ℝ) * L * (y : ℝ))
      rw [Nat.floor_lt (by positivity)]
      push_cast
      linarith⟩
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have hfl : ∀ y ∈ S, ⌊4 * Int.fract (((i : ℕ) : ℝ) * L * y)⌋₊
      = ⌊4 * Int.fract (((j : ℕ) : ℝ) * L * y)⌋₊ := by
    intro y hy
    have := congrArg Fin.val (congrFun hg ⟨y, hy⟩)
    simpa [g] using this
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨((j : ℕ) - i) * L, ?_, key S L i j hlt hfl⟩
    have : L ≤ ((j : ℕ) - i) * L := Nat.le_mul_of_pos_left L (by omega)
    omega
  · refine ⟨((i : ℕ) - j) * L, ?_, key S L j i hlt (fun y hy => (hfl y hy).symm)⟩
    have : L ≤ ((i : ℕ) - j) * L := Nat.le_mul_of_pos_left L (by omega)
    omega

end FD

theorem erdos_987.variants.finite_distinct_points
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : (Set.range x).Finite) :
    ∃ᶠ k : ℕ in atTop, A x k = ⊤ := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨k, hk, hpos⟩ := FD.exists_k hfin.toFinset a
  refine ⟨k, hk, ?_⟩
  have hne : hfin.toFinset.Nonempty := ⟨x 0, by simp⟩
  obtain ⟨y0, hy0, hmin⟩ :=
    hfin.toFinset.exists_min_image (fun y => Real.cos (2 * Real.pi * ((k : ℝ) * y))) hne
  set c := Real.cos (2 * Real.pi * ((k : ℝ) * y0)) with hc
  have cpos : 0 < c := hpos y0 hy0
  have hlow : ∀ n : ℕ, (n : ℝ) * c ≤ ‖∑ j ∈ range n, e (k * x j)‖ := by
    intro n
    calc (n : ℝ) * c = ∑ j ∈ range n, c := by simp
      _ ≤ ∑ j ∈ range n, Real.cos (2 * Real.pi * ((k : ℝ) * x j)) :=
          Finset.sum_le_sum (fun j _ => hmin (x j) (by simp))
      _ = (∑ j ∈ range n, e (k * x j)).re := by
          rw [Complex.re_sum]; simp only [FD.re_e]
      _ ≤ _ := Complex.re_le_norm _
  unfold A
  refine (EReal.eq_top_iff_forall_lt _).2 (fun M => ?_)
  have hev : ∀ᶠ n : ℕ in atTop,
      ((M + 1 : ℝ) : EReal) ≤ (‖∑ j ∈ range n, e (k * x j)‖ : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈(M + 1) / c⌉₊] with n hn
    rw [EReal.coe_le_coe_iff]
    have h1 : (M + 1) / c ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ cpos] at h1
    linarith [hlow n]
  have := Filter.le_limsup_of_frequently_le hev.frequently
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) this

end Erdos987

#print axioms Erdos987.erdos_987.variants.finite_distinct_points
