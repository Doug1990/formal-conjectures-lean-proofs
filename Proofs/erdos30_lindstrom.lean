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

/-- Sharp additive energy bound of a Sidon set with an interval `[0, m]`. -/
lemma energy_le' (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (m : ℕ) :
    Finset.addEnergy S (Finset.range (m + 1)) ≤ S.card * (m + 1) + (m + 1) * m := by
  unfold Finset.addEnergy
  set F := ((S ×ˢ S) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2) with hF
  rw [← Finset.card_filter_add_card_filter_not (s := F) (p := fun x => x.1.1 = x.1.2)]
  apply add_le_add
  · rw [← Finset.card_range (m + 1), ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun x => (x.1.1, x.2.1)) (fun x hx => ?_) ?_
    · simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.coe_filter] at hx
      exact Finset.mem_product.2 ⟨hx.1.1.1.1, hx.1.1.2.1⟩
    · intro x hx y hy hxy
      obtain ⟨⟨a1, a2⟩, b1, b2⟩ := x
      obtain ⟨⟨a1', a2'⟩, b1', b2'⟩ := y
      simp only [hF, Finset.mem_filter, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only [Prod.mk.injEq] at hxy ⊢
      omega
  · have hoff : ((Finset.range (m + 1)).offDiag).card = (m + 1) * m := by
      rw [Finset.offDiag_card, Finset.card_range]
      have e : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      rw [e, Nat.add_sub_cancel]
    rw [← hoff]
    refine Finset.card_le_card_of_injOn (fun x => x.2) (fun x hx => ?_) ?_
    · obtain ⟨⟨a1, a2⟩, b1, b2⟩ := x
      simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.coe_filter,
        Set.mem_ofPred_eq] at hx
      obtain ⟨⟨⟨⟨_, _⟩, h3, h4⟩, h5⟩, h6⟩ := hx
      refine Finset.mem_offDiag.2 ⟨h3, h4, ?_⟩
      try dsimp only at h5 h6
      try dsimp only
      omega
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

/-- Lindström / Erdős–Turán counting: `k² (m+1) ≤ (N + m)(k + m)`. -/
lemma key_nat' (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (N m : ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) :
    S.card ^ 2 * (m + 1) ≤ (N + m) * (S.card + m) := by
  have h1 := Finset.le_card_add_mul_addEnergy S (Finset.range (m + 1))
  have h2 : (S + Finset.range (m + 1)).card ≤ N + m := by
    calc (S + Finset.range (m + 1)).card ≤ (Finset.Icc 1 (N + m)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
          have := hsub ha
          simp only [Finset.mem_Icc, Finset.mem_range] at this hb ⊢
          omega
      _ = N + m := by simp
  have h3 := energy_le' S hS m
  rw [Finset.card_range] at h1
  have h4 : S.card ^ 2 * (m + 1) ^ 2 ≤ (N + m) * (S.card * (m + 1) + (m + 1) * m) :=
    h1.trans (Nat.mul_le_mul h2 h3)
  have h5 : S.card ^ 2 * (m + 1) * (m + 1) ≤ (N + m) * (S.card + m) * (m + 1) := by
    calc S.card ^ 2 * (m + 1) * (m + 1) = S.card ^ 2 * (m + 1) ^ 2 := by ring
      _ ≤ (N + m) * (S.card * (m + 1) + (m + 1) * m) := h4
      _ = (N + m) * (S.card + m) * (m + 1) := by ring
  exact Nat.le_of_mul_le_mul_right h5 (Nat.succ_pos m)

/-- The real-variable step: from the counting inequality with `m + 1 ≈ q³`
we get `k ≤ q² + q + 1`. -/
lemma real_step (k q mm : ℝ) (hq : 1 ≤ q) (_hk : 0 ≤ k)
    (hlo : q ^ 3 ≤ mm + 1) (hhi : mm + 1 < q ^ 3 + 1)
    (hR : k ^ 2 * (mm + 1) ≤ (q ^ 4 + mm) * (k + mm)) :
    k ≤ q ^ 2 + q + 1 := by
  by_contra hlt
  have hlt' : q ^ 2 + q + 1 < k := lt_of_not_ge hlt
  set x0 := q ^ 2 + q + 1 with hx0
  have hq0 : 0 ≤ q := by linarith
  have p2 : 0 ≤ q ^ 2 := pow_nonneg hq0 2
  have p3 : 1 ≤ q ^ 3 := one_le_pow₀ hq
  have p4 : 0 ≤ q ^ 4 := pow_nonneg hq0 4
  have p5 : 0 ≤ q ^ 5 := pow_nonneg hq0 5
  obtain ⟨δ, hδ⟩ : ∃ δ, mm = q ^ 3 + δ - 1 := ⟨mm + 1 - q ^ 3, by ring⟩
  have hδ0 : 0 ≤ δ := by linarith
  have hδ1 : δ < 1 := by linarith
  have e : x0 ^ 2 * (mm + 1) - (q ^ 4 + mm) * (x0 + mm)
      = q ^ 5 + q ^ 4 + 2 * q ^ 3 + q ^ 2 + q + δ * (2 * q ^ 2 + q + 2) - δ ^ 2 := by
    rw [hδ, hx0]; ring
  have hδ2 : δ ^ 2 < 1 := by nlinarith
  have hδ3 : 0 ≤ δ * (2 * q ^ 2 + q + 2) := mul_nonneg hδ0 (by linarith)
  have hf0 : 0 < x0 ^ 2 * (mm + 1) - (q ^ 4 + mm) * (x0 + mm) := by
    rw [e]; linarith
  have hx0pos : 0 < x0 := by rw [hx0]; linarith
  have a1 : q ^ 3 * (k + x0) ≤ (mm + 1) * (k + x0) :=
    mul_le_mul_of_nonneg_right hlo (by linarith)
  have a2 : q ^ 3 * (2 * x0) < q ^ 3 * (k + x0) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  have a3 : q ^ 3 * (2 * x0) = 2 * q ^ 5 + 2 * q ^ 4 + 2 * q ^ 3 := by rw [hx0]; ring
  have hpos : 0 < (mm + 1) * (k + x0) - (q ^ 4 + mm) := by linarith
  have iden : k ^ 2 * (mm + 1) - (q ^ 4 + mm) * (k + mm)
      = (x0 ^ 2 * (mm + 1) - (q ^ 4 + mm) * (x0 + mm))
        + (k - x0) * ((mm + 1) * (k + x0) - (q ^ 4 + mm)) := by ring
  have := mul_pos (sub_pos.2 hlt') hpos
  linarith

theorem erdos_30.variants.lindstrom (N : ℕ) :
    (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  have hne : ((Finset.Icc 1 N).powerset.filter
      fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hBsub, hBS⟩ := Finset.mem_filter.1 hB
  have hhB : h N = B.card := hBeq
  rw [hhB]
  have hBsub' := Finset.mem_powerset.1 hBsub
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : B = ∅ := Finset.subset_empty.1 (by simpa using hBsub')
    subst this
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
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
  obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hmR : (M : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  have hk := key_nat' B hBS N m hBsub'
  have hR : (B.card : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ ((N : ℝ) + m) * (B.card + m) := by
    exact_mod_cast hk
  rw [← hq4] at hR
  have := real_step (B.card : ℝ) q (m : ℝ) hq1 (Nat.cast_nonneg _)
    (by rw [← hmR]; exact hMge) (by rw [← hmR]; exact hMlt) hR
  rw [hsq]
  linarith

end Erdos30

#print axioms Erdos30.erdos_30.variants.lindstrom
