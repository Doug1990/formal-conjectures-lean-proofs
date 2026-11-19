import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Finset

namespace Erdos675

/-- Restated from ErdosProblems/675.lean. -/
def IsTranslation (A : Set ℕ) (n t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

/-- Restated from ErdosProblems/675.lean. -/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, IsTranslation A n t

namespace SQ

/-- Solutions of `q ∣ c + M s` with `s < X` and `q` coprime to `M`. -/
lemma count (q M c X : ℕ) (hq : 0 < q) (hc : Nat.Coprime q M) :
    ((range X).filter (fun s => q ∣ c + M * s)).card ≤ X / q + 1 := by
  have hmap : ∀ s ∈ (range X).filter (fun s => q ∣ c + M * s), s / q ∈ range (X / q + 1) := by
    intro s hs
    simp only [mem_filter, mem_range] at hs ⊢
    have : s / q ≤ X / q := Nat.div_le_div_right hs.1.le
    omega
  have key : ∀ s₁ s₂, s₁ ≤ s₂ → q ∣ c + M * s₁ → q ∣ c + M * s₂ → s₁ / q = s₂ / q → s₁ = s₂ := by
    intro s₁ s₂ hle h1 h2 he
    have hd : q ∣ M * (s₂ - s₁) := by
      have := Nat.dvd_sub h2 h1
      have e : c + M * s₂ - (c + M * s₁) = M * (s₂ - s₁) := by
        rw [Nat.mul_sub]; omega
      rwa [e] at this
    have hd' : q ∣ s₂ - s₁ := hc.dvd_of_dvd_mul_left hd
    have m1 := Nat.div_add_mod s₁ q
    have m2 := Nat.div_add_mod s₂ q
    have r2 := Nat.mod_lt s₂ hq
    have hlt : s₂ - s₁ < q := by
      rw [he] at m1
      omega
    have := Nat.eq_zero_of_dvd_of_lt hd' hlt
    omega
  calc ((range X).filter (fun s => q ∣ c + M * s)).card
      ≤ (range (X / q + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun s => s / q) hmap
        intro s₁ hs₁ s₂ hs₂ he
        simp only [coe_filter, Set.mem_ofPred_eq] at hs₁ hs₂
        rcases le_total s₁ s₂ with h | h
        · exact key s₁ s₂ h hs₁.2 hs₂.2 he
        · exact (key s₂ s₁ h hs₂.2 hs₁.2 he.symm).symm
    _ = X / q + 1 := card_range _

lemma tail (n : ℕ) : ∀ K : ℕ,
    ∑ m ∈ Ioc n (n + K), (1 : ℝ) / ((m : ℝ) * m) ≤ 2 / (2 * n + 1) - 2 / (2 * (n + K : ℕ) + 1) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show n + (K + 1) = (n + K) + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
    have step : (1 : ℝ) / (((n + K + 1 : ℕ) : ℝ) * ((n + K + 1 : ℕ) : ℝ)) ≤
        2 / (2 * ((n + K : ℕ) : ℝ) + 1) - 2 / (2 * ((n + K + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      have h0 : (0 : ℝ) ≤ (n : ℝ) + K := by positivity
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma tail' (n R : ℕ) :
    ∑ m ∈ Ioc n R, (1 : ℝ) / ((m : ℝ) * m) ≤ 2 / (2 * n + 1) := by
  rcases le_or_gt R n with h | h
  · rw [Finset.Ioc_eq_empty_of_le h, sum_empty]; positivity
  · obtain ⟨K, rfl⟩ : ∃ K, R = n + K := ⟨R - n, by omega⟩
    have := tail n K
    have : (0 : ℝ) ≤ 2 / (2 * (n + K : ℕ) + 1) := by positivity
    linarith

lemma big (Y R Z : ℕ) (n M : ℕ) (hZ : Z = Y * Y * (n + M)) (hR : R * R ≤ n + M * (Z + 1)) :
    Y * R < Z + 1 := by
  apply (Nat.mul_self_lt_mul_self_iff).1
  calc Y * R * (Y * R) = Y * Y * (R * R) := by ring
    _ ≤ Y * Y * (n + M * (Z + 1)) := Nat.mul_le_mul_left _ hR
    _ ≤ Y * Y * ((n + M) * (Z + 1)) := by
        apply Nat.mul_le_mul_left; nlinarith
    _ = Z * (Z + 1) := by rw [hZ]; ring
    _ < (Z + 1) * (Z + 1) := by nlinarith

end SQ

theorem erdos_675.variants.squarefree : HasTranslationProperty {m : ℕ | Squarefree m} := by
  intro n
  set M := n.factorial * n.factorial with hM
  have hMpos : 0 < M := by positivity
  set Y := n * (2 * n + 1) with hY
  set Z := Y * Y * (n + M) with hZ
  set X := Z + 1 with hX
  set R := Nat.sqrt (n + M * X) with hR
  have hRR : R * R ≤ n + M * X := Nat.sqrt_le _
  have hYR : Y * R < X := SQ.big Y R Z n M hZ hRR
  set P := (Ioc n R).filter Nat.Prime with hP
  set B := (range X).filter (fun s => ∃ a ∈ Icc 1 n, ∃ p ∈ P, p * p ∣ a + M * (s + 1)) with hB
  have hsub : B ⊆ (Icc 1 n).biUnion (fun a => P.biUnion
      (fun p => (range X).filter (fun s => p * p ∣ (a + M) + M * s))) := by
    intro s hs
    simp only [hB, mem_filter, mem_range] at hs
    obtain ⟨hs, a, ha, p, hp, hd⟩ := hs
    simp only [mem_biUnion, mem_filter, mem_range]
    exact ⟨a, ha, p, hp, hs, by rw [show a + M + M * s = a + M * (s + 1) by ring]; exact hd⟩
  have hcard : (B.card : ℝ) ≤ n * (X * (2 / (2 * n + 1)) + R) := by
    have h1 : B.card ≤ ∑ a ∈ Icc 1 n, ∑ p ∈ P, (X / (p * p) + 1) := by
      refine (card_le_card hsub).trans ?_
      refine card_biUnion_le.trans (sum_le_sum fun a _ => ?_)
      refine card_biUnion_le.trans (sum_le_sum fun p hp => ?_)
      simp only [hP, mem_filter, mem_Ioc] at hp
      apply SQ.count _ _ _ _ (by have := hp.2.pos; positivity)
      have hc : Nat.Coprime p n.factorial :=
        (Nat.Prime.coprime_iff_not_dvd hp.2).2 (fun h => by
          have := (Nat.Prime.dvd_factorial hp.2).1 h; omega)
      have hc' : Nat.Coprime p M := Nat.Coprime.mul_right hc hc
      exact Nat.Coprime.mul_left hc' hc'
    have h2 : ∀ a ∈ Icc 1 n, ((∑ p ∈ P, (X / (p * p) + 1) : ℕ) : ℝ) ≤ X * (2 / (2 * n + 1)) + R := by
      intro a _
      push_cast
      rw [sum_add_distrib]
      have e1 : ∑ p ∈ P, ((X / (p * p) : ℕ) : ℝ) ≤ ∑ m ∈ Ioc n R, (X : ℝ) * (1 / ((m : ℝ) * m)) := by
        refine (sum_le_sum fun p _ => ?_).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m _ _ => by positivity)
        rw [mul_one_div]
        have := Nat.cast_div_le (α := ℝ) (m := X) (n := p * p)
        push_cast at this
        exact this
      rw [← mul_sum] at e1
      have e2 := SQ.tail' n R
      have e3 : ∑ p ∈ P, (1 : ℝ) ≤ R := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        have : P.card ≤ R := (card_filter_le _ _).trans (by simp)
        exact_mod_cast this
      have hX0 : (0 : ℝ) ≤ X := by positivity
      nlinarith
    calc (B.card : ℝ) ≤ ((∑ a ∈ Icc 1 n, ∑ p ∈ P, (X / (p * p) + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ∑ a ∈ Icc 1 n, ((∑ p ∈ P, (X / (p * p) + 1) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∑ a ∈ Icc 1 n, (X * (2 / (2 * n + 1)) + R : ℝ) := sum_le_sum h2
      _ = n * (X * (2 / (2 * n + 1)) + R) := by simp
  have hlt : B.card < (range X).card := by
    rw [card_range]
    have hYR' : (Y : ℝ) * R < X := by exact_mod_cast hYR
    have hYd : (Y : ℝ) = n * (2 * n + 1) := by simp [hY]
    have key : (n : ℝ) * (X * (2 / (2 * n + 1)) + R) < X := by
      have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
      have e : (n : ℝ) * (X * (2 / (2 * n + 1)) + R) =
          (2 * n * X + n * (2 * n + 1) * R) / (2 * n + 1) := by
        field_simp
      rw [e, div_lt_iff₀ hpos]
      nlinarith
    exact_mod_cast hcard.trans_lt key
  obtain ⟨s, hs, hsB⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hs' : s < X := mem_range.1 hs
  refine ⟨M * (s + 1), by nlinarith, fun a ha1 han => ?_⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hsq
    rw [Nat.squarefree_iff_prime_squarefree] at hsq ⊢
    intro p hp hd
    rcases le_or_gt p n with hpn | hpn
    · have h1 : p * p ∣ M := Nat.mul_dvd_mul ((Nat.Prime.dvd_factorial hp).2 hpn)
        ((Nat.Prime.dvd_factorial hp).2 hpn)
      have h2 : p * p ∣ M * (s + 1) := Dvd.dvd.mul_right h1 _
      exact hsq p hp ((Nat.dvd_add_left h2).1 hd)
    · apply hsB
      simp only [hB, mem_filter, mem_range]
      refine ⟨hs', a, mem_Icc.2 ⟨ha1, han⟩, p, ?_, hd⟩
      simp only [hP, mem_filter, mem_Ioc]
      refine ⟨⟨hpn, ?_⟩, hp⟩
      rw [hR, Nat.le_sqrt]
      have := Nat.le_of_dvd (by positivity) hd
      have : M * (s + 1) ≤ M * X := Nat.mul_le_mul_left _ hs'
      omega
  · intro hsq x hx
    apply hsq x
    rcases Nat.eq_zero_or_pos x with h0 | hxpos
    · subst h0; simp at hx; omega
    have hxa : x ≤ a := (Nat.le_mul_self x).trans (Nat.le_of_dvd (by omega) hx)
    have h1 : x * x ∣ M := Nat.mul_dvd_mul (Nat.dvd_factorial hxpos (by omega))
      (Nat.dvd_factorial hxpos (by omega))
    exact dvd_add hx (Dvd.dvd.mul_right h1 _)

end Erdos675

#print axioms Erdos675.erdos_675.variants.squarefree
