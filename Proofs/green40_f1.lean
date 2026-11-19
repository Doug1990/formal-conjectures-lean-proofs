import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Common

abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

open Filter Fintype
open scoped ENNReal Pointwise

namespace Green40

def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- syndrome map -/
def syn {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] W where
  toFun x := ∑ i, x i • σ i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

lemma syn_single {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (i : Fin n) : syn σ (Pi.single i 1) = σ i := by
  simp [syn, Pi.single_apply, ite_smul]

lemma small {n : ℕ} (x : Fin n → ZMod 2) (hx : hammingNorm x ≤ 1) :
    x = 0 ∨ ∃ i, x = Pi.single i 1 := by
  by_cases h : x = 0
  · exact Or.inl h
  right
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  refine ⟨i, funext fun j => ?_⟩
  unfold hammingNorm at hx
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same]
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact key _ hi
  · rw [Pi.single_eq_of_ne hj]
    by_contra hc
    exact hj (Finset.card_le_one.1 hx j (by simp [hc]) i (by simp [hi]))

lemma single_mem {n : ℕ} (i : Fin n) : (Pi.single i 1 : 𝔽₂ n) ∈ hammingBall n 1 := by
  show hammingNorm _ ≤ 1
  unfold hammingNorm
  apply Finset.card_le_one.2
  intro a ha b hb
  simp [Pi.single_apply] at ha hb
  rw [ha, hb]

lemma cover {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hsurj : ∀ w ≠ 0, ∃ i, σ i = w) : IsCoveringSubspace n 1 (LinearMap.ker (syn σ)) := by
  unfold IsCoveringSubspace
  ext x
  simp only [Set.mem_univ, iff_true]
  by_cases h : syn σ x = 0
  · exact ⟨x, LinearMap.mem_ker.2 h, 0, by simp [hammingBall], add_zero x⟩
  · obtain ⟨i, hi⟩ := hsurj _ h
    refine ⟨x - Pi.single i 1, ?_, Pi.single i 1, single_mem i, sub_add_cancel _ _⟩
    show x - Pi.single i 1 ∈ LinearMap.ker (syn σ)
    rw [LinearMap.mem_ker, map_sub, syn_single, hi, sub_self]

lemma inj {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hinj : Function.Injective σ) (hne : ∀ i, σ i ≠ 0) :
    Function.Injective (fun p : LinearMap.ker (syn σ) × hammingBall n 1 =>
      (p.1 : Fin n → ZMod 2) + p.2) := by
  rintro ⟨⟨v, hv⟩, ⟨h, hh⟩⟩ ⟨⟨v', hv'⟩, ⟨h', hh'⟩⟩ heq
  simp only at heq
  have hs : syn σ h = syn σ h' := by
    have := congrArg (syn σ) heq
    rw [map_add, map_add, LinearMap.mem_ker.1 hv, LinearMap.mem_ker.1 hv', zero_add,
      zero_add] at this
    exact this
  have hhh : h = h' := by
    rcases small h hh with rfl | ⟨i, rfl⟩ <;> rcases small h' hh' with rfl | ⟨j, rfl⟩
    · rfl
    · rw [map_zero, syn_single] at hs; exact absurd hs.symm (hne j)
    · rw [map_zero, syn_single] at hs; exact absurd hs (hne i)
    · rw [syn_single, syn_single] at hs; rw [hinj hs]
  subst hhh
  have : v = v' := add_right_cancel heq
  subst this
  rfl

lemma card_space (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma dens_le {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hinj : Function.Injective σ) (hne : ∀ i, σ i ≠ 0) (hsurj : ∀ w ≠ 0, ∃ i, σ i = w) :
    minDensity n 1 ≤ 1 := by
  refine le_trans (iInf₂_le (LinearMap.ker (syn σ)) (cover σ hsurj)) ?_
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  have h1 := Nat.card_le_card_of_injective _ (inj σ hinj hne)
  rw [Nat.card_prod, card_space] at h1
  exact_mod_cast h1

lemma one_le (n : ℕ) : 1 ≤ minDensity n 1 := by
  refine le_iInf₂ fun V hV => ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  have hV' : (V : Set (𝔽₂ n)) + hammingBall n 1 = Set.univ := hV
  have hs : Function.Surjective (fun p : V × hammingBall n 1 => (p.1 : 𝔽₂ n) + p.2) := by
    intro x
    have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n 1 := hV' ▸ Set.mem_univ x
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  have h1 := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_prod, card_space] at h1
  exact_mod_cast h1

lemma exists_sigma (k : ℕ) : ∃ σ : Fin (2 ^ k - 1) → (Fin k → ZMod 2),
    Function.Injective σ ∧ (∀ i, σ i ≠ 0) ∧ ∀ w ≠ 0, ∃ i, σ i = w := by
  classical
  have hc : Fintype.card {w : Fin k → ZMod 2 // w ≠ 0} = 2 ^ k - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => (e i).1, ?_, fun i => (e i).2, fun w hw => ⟨e.symm ⟨w, hw⟩, by simp⟩⟩
  intro i j h
  exact e.injective (Subtype.ext h)

theorem green_40.sanity_f_one : f 1 = 1 := by
  show liminf (fun n ↦ minDensity n 1) atTop = 1
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le'
    rw [Filter.frequently_atTop]
    intro m
    obtain ⟨σ, h1, h2, h3⟩ := exists_sigma m
    refine ⟨2 ^ m - 1, ?_, dens_le σ h1 h2 h3⟩
    have := Nat.lt_two_pow_self (n := m)
    omega
  · exact Filter.le_liminf_of_le (h := Filter.Eventually.of_forall one_le)

end Green40

#print axioms Green40.green_40.sanity_f_one
