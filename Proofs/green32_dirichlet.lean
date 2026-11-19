import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.LinearCombination

open Asymptotics Filter
open scoped Pointwise

namespace Green32

def HasGap {p : ℕ} (A : Finset (ZMod p)) (L : ℕ) : Prop :=
  ∃ x : ZMod p, ∀ (i : ℕ), i < L → x + (i : ZMod p) ∉ A

def HasLargeGapDilate (ω : ℕ → ℝ) : Prop :=
  ∀ᶠ p in atTop, p.Prime →
    100 < ω p ∧ ω p < p ∧
    ∀ A : Finset (ZMod p), A.card = ⌊ω p⌋₊ →
    ∃ c : (ZMod p)ˣ, HasGap (c • A) ⌊100 * (p : ℝ) / ω p⌋₊

lemma bucket202 {p v v' : ℕ} (hp : 0 < p) (h : v * 202 / p = v' * 202 / p) :
    202 * ((v : ℤ) - v') < p ∧ 202 * ((v' : ℤ) - v) < p := by
  have h1 := Nat.div_add_mod (v * 202) p
  have h2 := Nat.div_add_mod (v' * 202) p
  have h3 := Nat.mod_lt (v * 202) hp
  have h4 := Nat.mod_lt (v' * 202) hp
  rw [h] at h1
  generalize p * (v' * 202 / p) = X at h1 h2
  generalize v * 202 % p = r at h1 h3
  generalize v' * 202 % p = r' at h2 h4
  omega

/-- Dirichlet-type dilation: if `202^|A| < p` then some dilate of `A` misses an interval of
length `L` whenever `101 L ≤ 100 p`. -/
lemma core {p : ℕ} [hp : Fact p.Prime] (A : Finset (ZMod p)) (L : ℕ)
    (hA : 202 ^ A.card < p) (hL : 101 * L ≤ 100 * p) :
    ∃ c : (ZMod p)ˣ, HasGap (c • A) L := by
  have hp0 : 0 < p := hp.out.pos
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let f : ℕ → (A → ℕ) := fun t a => ((t : ZMod p) * (a : ZMod p)).val * 202 / p
  obtain ⟨t, ht, t', ht', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (202 ^ A.card + 1)) (t := Fintype.piFinset fun _ : A => Finset.range 202)
    (f := f) (by simp) (by
      intro t _
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro a
      rw [Finset.mem_range]
      exact (Nat.div_lt_iff_lt_mul hp0).2
        (by have := ZMod.val_lt ((t : ZMod p) * (a : ZMod p)); omega))
  simp only [Finset.mem_range] at ht ht'
  set u : ZMod p := (t : ZMod p) - t' with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, sub_ne_zero]
    intro e
    apply hne
    have := congrArg ZMod.val e
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
  let d : ZMod p → ℤ := fun a => (((t : ZMod p) * a).val : ℤ) - (((t' : ZMod p) * a).val : ℤ)
  have hd_cast : ∀ a, ((d a : ℤ) : ZMod p) = u * a := by
    intro a
    simp only [d, hu_def, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_mul]
  have hd_bd : ∀ a ∈ A, 202 * d a < p ∧ 202 * (- d a) < p := by
    intro a ha
    have := bucket202 hp0 (congrFun heq ⟨a, ha⟩)
    simp only [d]
    constructor <;> linarith [this.1, this.2]
  refine ⟨Units.mk0 u hu, ((p / 202 + 1 : ℕ) : ZMod p), fun i hi hmem => ?_⟩
  rw [Finset.mem_smul_finset] at hmem
  obtain ⟨a, ha, hax⟩ := hmem
  rw [Units.smul_def, Units.val_mk0, smul_eq_mul] at hax
  have key : ((((p / 202 + 1 : ℕ) : ℤ) + (i : ℤ) - d a : ℤ) : ZMod p) = 0 := by
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, hd_cast]
    linear_combination -hax
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at key
  have b := hd_bd a ha
  have hz := Int.eq_zero_of_abs_lt_dvd key (by rw [abs_lt]; constructor <;> omega)
  omega

theorem green_32.variants.dirichlet_regime :
    ∃ c > 0, ∀ ω : ℕ → ℝ, (∀ᶠ p in atTop, 101 ≤ ω p ∧ ω p ≤ c * Real.log p) →
      HasLargeGapDilate ω := by
  have h203 : (0 : ℝ) < Real.log 203 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 203, div_pos one_pos h203, fun ω hω => ?_⟩
  unfold HasLargeGapDilate
  filter_upwards [hω] with p hpω hp
  obtain ⟨h1, h2⟩ := hpω
  have : Fact p.Prime := ⟨hp⟩
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hω0 : (0 : ℝ) < ω p := by linarith
  have hk101 : 101 ≤ ⌊ω p⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hkp : 203 ^ ⌊ω p⌋₊ ≤ p := by
    have h3 : (⌊ω p⌋₊ : ℝ) ≤ Real.log p / Real.log 203 := by
      calc (⌊ω p⌋₊ : ℝ) ≤ ω p := Nat.floor_le hω0.le
        _ ≤ 1 / Real.log 203 * Real.log p := h2
        _ = Real.log p / Real.log 203 := by ring
    rw [le_div_iff₀ h203, ← Real.log_pow] at h3
    have h4 := (Real.log_le_log_iff (pow_pos (by norm_num) _) hp').1 h3
    exact_mod_cast h4
  have hlt : 202 ^ ⌊ω p⌋₊ < p :=
    lt_of_lt_of_le (Nat.pow_lt_pow_left (by norm_num) (by omega)) hkp
  have hkl : ⌊ω p⌋₊ < 203 ^ ⌊ω p⌋₊ := Nat.lt_pow_self (by norm_num)
  refine ⟨by linarith, ?_, ?_⟩
  · have hk1 : ⌊ω p⌋₊ + 1 ≤ p := by omega
    calc ω p < ⌊ω p⌋₊ + 1 := Nat.lt_floor_add_one _
      _ ≤ p := by exact_mod_cast hk1
  · intro A hA
    apply core A
    · rw [hA]; exact hlt
    · have hL : (⌊100 * (p : ℝ) / ω p⌋₊ : ℝ) ≤ 100 * p / 101 :=
        (Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) hp'.le) hω0.le)).trans
          (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hp'.le) (by norm_num) h1)
      rw [le_div_iff₀ (by norm_num)] at hL
      have : ((101 * ⌊100 * (p : ℝ) / ω p⌋₊ : ℕ) : ℝ) ≤ ((100 * p : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this

end Green32

#print axioms Green32.green_32.variants.dirichlet_regime
