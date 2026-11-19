import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Function Set Filter
open scoped Pointwise

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Erdos329

noncomputable def sqrtPartialDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt

noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => sqrtPartialDensity A N) atTop

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

lemma key_real (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (N M : ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hM : 0 < M) :
    (S.card : ℝ) ≤ (N : ℝ) / M + 1 + √(N : ℝ) + √(M : ℝ) := by
  have h := key_nat S hS N M hsub hM
  have hR : (S.card : ℝ) ^ 2 * M ≤ ((N : ℝ) + M) * (S.card + M) := by exact_mod_cast h
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : (S.card : ℝ) ^ 2 ≤ ((N : ℝ) / M + 1) * S.card + ((N : ℝ) + M) := by
    have e : ((N : ℝ) / M + 1) * S.card + ((N : ℝ) + M) = ((N : ℝ) + M) * (S.card + M) / M := by
      field_simp
    rw [e, le_div_iff₀ hMpos]
    exact hR
  have h3 := sqrt_bound _ _ _ (Nat.cast_nonneg _) (by positivity) (by positivity) h2
  have h4 : √((N : ℝ) + M) ≤ √(N : ℝ) + √(M : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (Real.sqrt_nonneg (M : ℝ))]
  linarith

lemma count_bound (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ S : Finset ℕ,
    IsSidon (S : Set ℕ) → S ⊆ Finset.Icc 1 N → (S.card : ℝ) ≤ (1 + ε) * √(N : ℝ) := by
  set e := ε / 2 with he
  have hepos : 0 < e := by positivity
  set c : ℕ := ⌈3 / e⌉₊ with hc
  have hc1 : 3 / e ≤ c := Nat.le_ceil _
  have hec : 3 ≤ e * c := by rw [div_le_iff₀ hepos] at hc1; linarith
  have hcpos : 0 < c := by
    have : (0 : ℝ) < c := by
      have : 0 < 3 / e := by positivity
      linarith
    exact_mod_cast this
  set L : ℕ := ⌈9 * c / e ^ 2 + 3 / e⌉₊ with hL
  refine ⟨L ^ 2 + 1, fun N hN S hS hsub => ?_⟩
  set s := Nat.sqrt N + 1 with hs
  have hNs : N < s ^ 2 := by rw [hs, sq]; exact Nat.lt_succ_sqrt N
  have hLs : L ≤ Nat.sqrt N := Nat.le_sqrt'.2 (by omega)
  have hsqN : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtN1 : 1 ≤ √(N : ℝ) := by
    have := Real.sqrt_le_sqrt hN1
    rwa [Real.sqrt_one] at this
  have hrs_le : (s : ℝ) ≤ √(N : ℝ) + 1 := by
    have h1 : ((Nat.sqrt N : ℕ) : ℝ) ≤ √(N : ℝ) := by
      have := Real.sqrt_le_sqrt (show (((Nat.sqrt N ^ 2 : ℕ)) : ℝ) ≤ N by exact_mod_cast hsqN)
      rwa [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)] at this
    rw [hs]; push_cast; linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hLr : 9 * c / e ^ 2 + 3 / e ≤ (s : ℝ) := by
    have h1 : 9 * c / e ^ 2 + 3 / e ≤ (L : ℝ) := Nat.le_ceil _
    have h2 : (L : ℝ) ≤ s := by exact_mod_cast (show L ≤ s by omega)
    linarith
  have h9 : 9 * (c : ℝ) ≤ e ^ 2 * s := by
    have : 9 * (c : ℝ) / e ^ 2 ≤ s := by
      have := div_pos (by norm_num : (0 : ℝ) < 3) hepos
      linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h3 : 3 ≤ e * s := by
    have : 3 / e ≤ (s : ℝ) := by
      have : 0 ≤ 9 * (c : ℝ) / e ^ 2 := by positivity
      linarith
    rw [div_le_iff₀ hepos] at this; linarith
  set M := c * s with hM
  have hMpos : 0 < M := Nat.mul_pos hcpos (by omega)
  have hk := key_real S hS N M hsub hMpos
  have hMR : (M : ℝ) = c * s := by rw [hM]; push_cast; ring
  have hA : (N : ℝ) / M ≤ e * s / 3 := by
    rw [div_le_iff₀ (by exact_mod_cast hMpos), hMR]
    have hN' : (N : ℝ) < (s : ℝ) ^ 2 := by exact_mod_cast hNs
    nlinarith [mul_le_mul_of_nonneg_right hec (sq_nonneg (s : ℝ))]
  have hB : √(M : ℝ) ≤ e * s / 3 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [hMR]
    nlinarith [mul_le_mul_of_nonneg_right h9 hspos.le]
  have hC : (S.card : ℝ) ≤ √(N : ℝ) + e * s := by linarith
  calc (S.card : ℝ) ≤ √(N : ℝ) + e * s := hC
    _ ≤ √(N : ℝ) + e * (√(N : ℝ) + 1) := by
        have := mul_le_mul_of_nonneg_left hrs_le hepos.le
        linarith
    _ ≤ (1 + ε) * √(N : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsqrtN1 hepos.le
        rw [he]
        nlinarith

theorem erdos_329.variants.turan_1941 : ∀ (A : Set ℕ), IsSidon A → sidonUpperDensity A ≤ 1 := by
  intro A hA
  classical
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun N => sqrtPartialDensity A N) :=
    isCoboundedUnder_le_of_le atTop
      (fun N => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N0, hN0⟩ := count_bound ε hε
  refine limsup_le_of_le hcob ?_
  rw [eventually_atTop]
  refine ⟨N0 + 1, fun N hN => ?_⟩
  set S := (Finset.Icc 1 N).filter (· ∈ A) with hSdef
  have hset : A ∩ Set.Icc 1 N = (S : Set ℕ) := by
    ext x
    simp only [hSdef, Finset.coe_filter, Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq,
      Finset.mem_Icc]
    tauto
  have hSid : IsSidon (S : Set ℕ) := by
    intro a ha b hb c hc d hd h
    rw [← hset] at ha hb hc hd
    exact hA a ha.1 b hb.1 c hc.1 d hd.1 h
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hb := hN0 N (by omega) S hSid hsub
  have hpos : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  show (A ∩ Set.Icc 1 N).ncard / √(N : ℝ) ≤ 1 + ε
  rw [hset, Set.ncard_coe_finset, div_le_iff₀ hpos]
  linarith

end Erdos329

#print axioms Erdos329.erdos_329.variants.turan_1941
