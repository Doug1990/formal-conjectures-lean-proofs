import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination

open Asymptotics Filter

/-- restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean -/
def allUniqueSums {α : Type*} [AddCommMonoid α] (A : Set α) : Set α :=
  { n | ∃ p : α × α, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
      ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n → (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1) }

def HasNoUniqueRepresentation {α : Type*} [AddCommMonoid α] (A : Finset α) : Prop :=
  allUniqueSums (A : Set α) = ∅

namespace Green27

noncomputable def m (p : ℕ) : ℝ :=
  (sInf { (A.card) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card) (_ : HasNoUniqueRepresentation A) } : ℝ)

def primesAtTop : Filter ℕ := atTop ⊓ 𝓟 {p : ℕ | p.Prime}

lemma bucket {p v v' : ℕ} (hp : 0 < p) (h : v * 4 / p = v' * 4 / p) :
    4 * ((v : ℤ) - v') < p ∧ 4 * ((v' : ℤ) - v) < p := by
  have h1 := Nat.div_add_mod (v * 4) p
  have h2 := Nat.div_add_mod (v' * 4) p
  have h3 := Nat.mod_lt (v * 4) hp
  have h4 := Nat.mod_lt (v' * 4) hp
  rw [h] at h1
  generalize p * (v' * 4 / p) = X at h1 h2
  generalize v * 4 % p = r at h1 h3
  generalize v' * 4 % p = r' at h2 h4
  omega

lemma card_bound {p : ℕ} [hp : Fact p.Prime] (A : Finset (ZMod p)) (hA : A.Nonempty)
    (h : HasNoUniqueRepresentation A) : p ≤ 4 ^ A.card := by
  by_contra hlt
  push Not at hlt
  have hp0 : 0 < p := hp.out.pos
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let f : ℕ → (A → ℕ) := fun t a => ((t : ZMod p) * a).val * 4 / p
  obtain ⟨t, ht, t', ht', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (4 ^ A.card + 1)) (t := Fintype.piFinset fun _ : A => Finset.range 4)
    (f := f) (by simp) (by
      intro t _
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro a
      rw [Finset.mem_range]
      exact (Nat.div_lt_iff_lt_mul hp0).2 (by have := ZMod.val_lt ((t : ZMod p) * (a : ZMod p)); omega))
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
  have hd_bd : ∀ a ∈ A, 4 * d a < p ∧ 4 * (- d a) < p := by
    intro a ha
    have := bucket hp0 (congrFun heq ⟨a, ha⟩)
    simp only [d]
    constructor <;> linarith [this.1, this.2]
  obtain ⟨M, hM, hmax⟩ := A.exists_max_image d hA
  have hmem : M + M ∈ allUniqueSums (A : Set (ZMod p)) := by
    refine ⟨(M, M), hM, hM, rfl, ?_⟩
    intro a₁ h1 a₂ h2 hs
    left
    have key : ((d a₁ + d a₂ - 2 * d M : ℤ) : ZMod p) = 0 := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, hd_cast, Int.cast_ofNat]
      linear_combination u * hs
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at key
    have b1 := hd_bd a₁ h1
    have b2 := hd_bd a₂ h2
    have bM := hd_bd M hM
    have m1 := hmax a₁ h1
    have m2 := hmax a₂ h2
    have hz := Int.eq_zero_of_abs_lt_dvd key (by rw [abs_lt]; constructor <;> omega)
    have e1 : d a₁ = d M := by omega
    have e2 : d a₂ = d M := by omega
    constructor
    · apply mul_left_cancel₀ hu
      rw [← hd_cast, ← hd_cast, e1]
    · apply mul_left_cancel₀ hu
      rw [← hd_cast, ← hd_cast, e2]
  rw [h] at hmem
  simp at hmem

lemma univ_good {p : ℕ} [hp : Fact p.Prime] (h3 : 3 ≤ p) :
    HasNoUniqueRepresentation (Finset.univ : Finset (ZMod p)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨a, b⟩, -, -, hab, hu⟩
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, x ≠ a ∧ x ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ {a, b} := fun x _ => by
      by_cases hxa : x = a
      · simp [hxa]
      · simp [hcon x hxa]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at h1
    have h2 := Finset.card_insert_le a ({b} : Finset (ZMod p))
    rw [Finset.card_singleton] at h2
    omega
  rcases hu x (by simp) (s - x) (by simp) (by ring) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hx.1 h1
  · exact hx.2 h1

theorem green_27.variants.previous_lower :
  (fun p ↦ Real.log (p : ℝ)) =O[primesAtTop] m := by
  refine IsBigO.of_bound (Real.log 4) ?_
  unfold primesAtTop
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop 3] with p h3 hp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlow : Real.log p / Real.log 4 ≤ m p := by
    unfold m
    apply le_csInf
    · exact ⟨_, Finset.univ, by rw [Finset.card_univ, ZMod.card]; omega, univ_good h3, rfl⟩
    · rintro x ⟨A, hA2, hA, rfl⟩
      have hb := card_bound A (Finset.card_pos.1 (by omega)) hA
      rw [div_le_iff₀ h4]
      calc Real.log p ≤ Real.log ((4 : ℝ) ^ A.card) :=
            Real.log_le_log hp' (by exact_mod_cast hb)
        _ = A.card * Real.log 4 := by rw [Real.log_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))]
  rw [div_le_iff₀ h4] at hlow
  calc Real.log p ≤ m p * Real.log 4 := hlow
    _ = Real.log 4 * m p := mul_comm _ _
    _ ≤ Real.log 4 * ‖m p‖ := mul_le_mul_of_nonneg_left (Real.le_norm_self _) h4.le

end Green27

#print axioms Green27.green_27.variants.previous_lower
