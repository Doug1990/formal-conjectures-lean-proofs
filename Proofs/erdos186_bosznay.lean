import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

namespace Erdos186

/-- Restated from the checkout (ErdosProblems/186.lean). -/
def NonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, 2 ≤ S.card → (∑ x ∈ S, x) ≠ S.card * a

instance (A : Finset ℕ) : Decidable (NonAveraging A) := by
  unfold NonAveraging; infer_instance

def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonAveraging).sup Finset.card

theorem card_le_F {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    A.card ≤ F N :=
  Finset.le_sup (f := Finset.card) (by simp [hA, hna])

namespace BZ

/-- Core: no `i` is the average of a nonempty set of other `j ∈ [1,k]` under `j ↦ j² + k³ j`. -/
theorem core (k i : ℕ) (T : Finset ℕ) (hT : T ⊆ (Icc 1 k).erase i) (hi : i ∈ Icc 1 k)
    (hne : T.Nonempty)
    (h : (∑ j ∈ T, ((j : ℤ) ^ 2 + (k : ℤ) ^ 3 * j)) = (T.card : ℤ) * ((i : ℤ) ^ 2 + (k : ℤ) ^ 3 * i)) :
    False := by
  have hi' := Finset.mem_Icc.1 hi
  have hk : 1 ≤ k := le_trans hi'.1 hi'.2
  set E : ℤ := ∑ j ∈ T, ((j : ℤ) ^ 2 - (i : ℤ) ^ 2) with hE
  set D : ℤ := ∑ j ∈ T, ((j : ℤ) - i) with hD
  have hED : E + (k : ℤ) ^ 3 * D = 0 := by
    have : E + (k : ℤ) ^ 3 * D
        = ∑ j ∈ T, (((j : ℤ) ^ 2 + (k : ℤ) ^ 3 * j) - ((i : ℤ) ^ 2 + (k : ℤ) ^ 3 * i)) := by
      rw [hE, hD, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [this, Finset.sum_sub_distrib, h, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard : T.card ≤ k - 1 := by
    have := Finset.card_le_card hT
    rw [Finset.card_erase_of_mem hi, Nat.card_Icc] at this
    omega
  have hterm : ∀ j ∈ T, |(j : ℤ) ^ 2 - (i : ℤ) ^ 2| ≤ (k : ℤ) ^ 2 - 1 := by
    intro j hj
    have hj' := Finset.mem_Icc.1 (Finset.mem_of_mem_erase (hT hj))
    have a1 : (1 : ℤ) ≤ j := by exact_mod_cast hj'.1
    have a2 : (j : ℤ) ≤ k := by exact_mod_cast hj'.2
    have b1 : (1 : ℤ) ≤ i := by exact_mod_cast hi'.1
    have b2 : (i : ℤ) ≤ k := by exact_mod_cast hi'.2
    rw [abs_le]
    constructor <;> nlinarith
  have hEb : |E| ≤ ((k : ℤ) - 1) * ((k : ℤ) ^ 2 - 1) := by
    calc |E| ≤ ∑ j ∈ T, |(j : ℤ) ^ 2 - (i : ℤ) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ T, ((k : ℤ) ^ 2 - 1) := Finset.sum_le_sum hterm
      _ = (T.card : ℤ) * ((k : ℤ) ^ 2 - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℤ) - 1) * ((k : ℤ) ^ 2 - 1) := by
        have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
        have : (T.card : ℤ) ≤ (k : ℤ) - 1 := by
          have := hcard
          have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by push_cast [Nat.cast_sub hk]; ring
          omega
        apply mul_le_mul_of_nonneg_right this
        nlinarith
  have hD0 : D = 0 := by
    by_contra hD0
    have h1 : 1 ≤ |D| := Int.one_le_abs hD0
    have h2 : |E| = (k : ℤ) ^ 3 * |D| := by
      have : E = -((k : ℤ) ^ 3 * D) := by linarith
      rw [this, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
    have h3 : (k : ℤ) ^ 3 ≤ (k : ℤ) ^ 3 * |D| := by nlinarith [pow_pos (by linarith : (0:ℤ) < k) 3]
    nlinarith
  have hE0 : E = 0 := by rw [hD0] at hED; linarith
  have hsq : ∑ j ∈ T, ((j : ℤ) - i) ^ 2 = E - 2 * i * D := by
    rw [hE, hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hpos : 0 < ∑ j ∈ T, ((j : ℤ) - i) ^ 2 := by
    apply Finset.sum_pos _ hne
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase (hT hj)
    have : (j : ℤ) - i ≠ 0 := by
      intro h0; apply hji; exact_mod_cast (sub_eq_zero.1 h0)
    positivity
  rw [hsq, hE0, hD0] at hpos
  simp at hpos

/-- The construction. -/
def f (k i : ℕ) : ℕ := i ^ 2 + k ^ 3 * i

theorem f_strictMono (k : ℕ) : StrictMono (f k) := by
  intro a b hab
  unfold f
  have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have : k ^ 3 * a ≤ k ^ 3 * b := Nat.mul_le_mul_left _ hab.le
  omega

theorem nonAveraging (k : ℕ) : NonAveraging ((Icc 1 k).image (f k)) := by
  intro a ha S hS hS2 hsum
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
  have hinj : Function.Injective (f k) := (f_strictMono k).injective
  have hS' : S ⊆ ((Icc 1 k).erase i).image (f k) := by
    intro x hx
    have hx' := hS hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hx')
    have hji : j ≠ i := by
      intro e; subst e; exact (Finset.ne_of_mem_erase hx') rfl
    exact Finset.mem_image.2 ⟨j, Finset.mem_erase.2 ⟨hji, hj⟩, rfl⟩
  obtain ⟨T, hT, rfl⟩ := Finset.subset_image_iff.1 hS'
  rw [Finset.card_image_of_injective _ hinj] at hS2 hsum
  rw [Finset.sum_image (fun x _ y _ e => hinj e)] at hsum
  refine core k i T hT hi (Finset.card_pos.1 (by omega)) ?_
  have := congrArg (fun n : ℕ => (n : ℤ)) hsum
  simp only [f] at this
  push_cast at this
  exact this

theorem subset_Icc (k N : ℕ) (hN : 2 * k ^ 4 ≤ N) : (Icc 1 k).image (f k) ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  have hi' := Finset.mem_Icc.1 hi
  apply Finset.mem_Icc.2
  unfold f
  constructor
  · have : 1 ≤ i ^ 2 := Nat.one_le_pow _ _ hi'.1
    omega
  · have h1 : i ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hi'.2 2
    have h2 : k ^ 3 * i ≤ k ^ 3 * k := Nat.mul_le_mul_left _ hi'.2
    have h3 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : k ^ 3 * k = k ^ 4 := by ring
    omega

theorem k_le_F (k N : ℕ) (hN : 2 * k ^ 4 ≤ N) : k ≤ F N := by
  have := card_le_F (subset_Icc k N hN) (nonAveraging k)
  rwa [Finset.card_image_of_injective _ (f_strictMono k).injective, Nat.card_Icc,
    Nat.add_sub_cancel] at this

end BZ

theorem erdos_186.variants.bosznay :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 4) ≤ F N := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 256] with N hN
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ^ 4 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hN' : (256 : ℝ) ≤ N := by exact_mod_cast hN
  have hx_ge : 4 ≤ x := by
    by_contra hlt
    push Not at hlt
    have : x ^ 4 < 4 ^ 4 := pow_lt_pow_left₀ hlt hx0 (by norm_num)
    norm_num at this
    linarith
  set k : ℕ := ⌊x / 2⌋₊ with hk
  have hk1 : (k : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hk2 : x / 2 < k + 1 := Nat.lt_floor_add_one _
  have hk4 : 2 * k ^ 4 ≤ N := by
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have : ((k : ℝ)) ^ 4 ≤ (x / 2) ^ 4 := pow_le_pow_left₀ h0 hk1 4
    have : (2 * k ^ 4 : ℕ) ≤ (N : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have := BZ.k_le_F k N hk4
  have hcast : (k : ℝ) ≤ F N := by exact_mod_cast this
  linarith

end Erdos186

#print axioms Erdos186.erdos_186.variants.bosznay
