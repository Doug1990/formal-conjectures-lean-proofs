import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Pointwise

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Finset

variable {α : Type*} [AddCommMonoid α]

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end Finset

namespace Erdos30

noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

open Filter

/-- Additive energy of a Sidon set with an interval `[0, M)`. -/
lemma energy_le (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (M : ℕ) :
    Finset.addEnergy S (Finset.range M) ≤ S.card * M + M * M := by
  unfold Finset.addEnergy
  set F := ((S ×ˢ S) ×ˢ Finset.range M ×ˢ Finset.range M).filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2) with hF
  rw [← Finset.card_filter_add_card_filter_not (s := F) (p := fun x => x.1.1 = x.1.2)]
  apply add_le_add
  · rw [← Finset.card_range M, ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun x => (x.1.1, x.2.1)) (fun x hx => ?_) ?_
    · simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.coe_filter] at hx
      exact Finset.mem_product.2 ⟨hx.1.1.1.1, hx.1.1.2.1⟩
    · intro x hx y hy hxy
      obtain ⟨⟨a1, a2⟩, b1, b2⟩ := x
      obtain ⟨⟨a1', a2'⟩, b1', b2'⟩ := y
      simp only [hF, Finset.mem_filter, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only [Prod.mk.injEq] at hxy ⊢
      omega
  · rw [← Finset.card_range M, ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun x => x.2) (fun x hx => ?_) ?_
    · simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.coe_filter] at hx
      exact Finset.mem_product.2 ⟨hx.1.1.2.1, hx.1.1.2.2⟩
    · intro x hx y hy hxy
      obtain ⟨⟨a1, a2⟩, b1, b2⟩ := x
      obtain ⟨⟨a1', a2'⟩, b1', b2'⟩ := y
      simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.coe_filter,
        Set.mem_ofPred_eq] at hx hy
      simp only [Prod.mk.injEq] at hxy ⊢
      obtain ⟨rfl, rfl⟩ := hxy
      have hs := hS a1 hx.1.1.1.1 a1' hy.1.1.1.1 a2' hy.1.1.1.2 a2 hx.1.1.1.2 (by omega)
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨h1, h2.symm⟩, rfl, rfl⟩
      · exact absurd h1 hx.2

lemma key_nat (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (N M : ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hM : 0 < M) :
    S.card ^ 2 * M ≤ (N + M) * (S.card + M) := by
  have h1 := Finset.le_card_add_mul_addEnergy S (Finset.range M)
  have h2 : (S + Finset.range M).card ≤ N + M := by
    calc (S + Finset.range M).card ≤ (Finset.Icc 1 (N + M)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
          have := hsub ha
          simp only [Finset.mem_Icc, Finset.mem_range] at this hb ⊢
          omega
      _ = N + M := by simp
  have h3 := energy_le S hS M
  rw [Finset.card_range] at h1
  have h4 : S.card ^ 2 * M ^ 2 ≤ (N + M) * (S.card * M + M * M) :=
    h1.trans (Nat.mul_le_mul h2 h3)
  have h5 : S.card ^ 2 * M * M ≤ (N + M) * (S.card + M) * M := by
    calc S.card ^ 2 * M * M = S.card ^ 2 * M ^ 2 := by ring
      _ ≤ (N + M) * (S.card * M + M * M) := h4
      _ = (N + M) * (S.card + M) * M := by ring
  exact Nat.le_of_mul_le_mul_right h5 hM

lemma sqrt_bound (x b c : ℝ) (_hx : 0 ≤ x) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ b * x + c) : x ≤ b + √c := by
  by_contra hlt
  have hlt' : b + √c < x := lt_of_not_ge hlt
  have hs := Real.sq_sqrt hc
  have h0 := Real.sqrt_nonneg c
  nlinarith [mul_pos (sub_pos.2 hlt') (show 0 < x by linarith),
    mul_nonneg (show 0 ≤ x - √c by linarith) h0]

/-- Sharper real form: `|S| ≤ N/M + 1 + √N + M/(2√N)`. -/
lemma key_real2 (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (N M : ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hM : 0 < M) (hN : 0 < N) :
    (S.card : ℝ) ≤ (N : ℝ) / M + 1 + √(N : ℝ) + (M : ℝ) / (2 * √(N : ℝ)) := by
  have h := key_nat S hS N M hsub hM
  have hR : (S.card : ℝ) ^ 2 * M ≤ ((N : ℝ) + M) * (S.card + M) := by exact_mod_cast h
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : (S.card : ℝ) ^ 2 ≤ ((N : ℝ) / M + 1) * S.card + ((N : ℝ) + M) := by
    have e : ((N : ℝ) / M + 1) * S.card + ((N : ℝ) + M) = ((N : ℝ) + M) * (S.card + M) / M := by
      field_simp
    rw [e, le_div_iff₀ hMpos]
    exact hR
  have h3 := sqrt_bound _ _ _ (Nat.cast_nonneg _) (by positivity) (by positivity) h2
  have ht : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have ht2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h4 : √((N : ℝ) + M) ≤ √(N : ℝ) + (M : ℝ) / (2 * √(N : ℝ)) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    set t := √(N : ℝ)
    set u := (M : ℝ) / (2 * t) with hu
    have hu2 : 2 * t * u = M := by rw [hu]; field_simp
    nlinarith [sq_nonneg u]
  linarith

theorem erdos_30.variants.erdos_turan :
    ∃ C : ℝ, ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + C * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  refine ⟨3, ?_⟩
  rw [eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  -- a maximal Sidon subset
  have hne : ((Finset.Icc 1 N).powerset.filter
      fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hBsub, hBS⟩ := Finset.mem_filter.1 hB
  have hhB : h N = B.card := hBeq
  rw [hhB]
  set q : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ) with hq
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1 (by norm_num)
  have hq4 : q ^ 4 = (N : ℝ) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hsq : √(N : ℝ) = q ^ 2 := by
    rw [← hq4, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  set M : ℕ := ⌈q ^ 3⌉₊ with hM
  have hMge : q ^ 3 ≤ (M : ℝ) := Nat.le_ceil _
  have hMlt : (M : ℝ) < q ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast this
  have hk := key_real2 B hBS N M (Finset.mem_powerset.1 hBsub) hMpos (by omega)
  have hA : (N : ℝ) / M ≤ q := by
    rw [div_le_iff₀ (by exact_mod_cast hMpos), ← hq4]
    nlinarith [mul_le_mul_of_nonneg_left hMge (show 0 ≤ q by linarith)]
  have hB2 : (M : ℝ) / (2 * √(N : ℝ)) ≤ q := by
    rw [div_le_iff₀ (by positivity), hsq]
    nlinarith
  linarith

end Erdos30

#print axioms Erdos30.erdos_30.variants.erdos_turan
