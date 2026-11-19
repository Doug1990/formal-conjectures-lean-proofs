import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs

open Asymptotics Filter

namespace Erdos304

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ, s.card = k ∧ (∀ n ∈ s, n > 1) ∧ (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

noncomputable def smallestCollection (a b : ℕ) : ℕ := sInf (unitFractionExpressible a b)

noncomputable def smallestCollectionTo (b : ℕ) : ℕ :=
  sSup {smallestCollection a b | a ∈ Finset.Ico 1 b}

namespace LW

/-- Fibonacci–Sylvester (copied from results/erdos295_k.lean). -/
lemma egypt (a : ℕ) : ∀ b M : ℕ, 0 < M → 0 < a → M * a < b →
    ∃ S : Finset ℕ, (∀ s ∈ S, M < s) ∧ ∑ s ∈ S, (1 / s : ℚ) = a / b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b M hM ha hab
  have hdiv := Nat.div_add_mod b a
  have hlt := Nat.mod_lt b ha
  set q := b / a with hq
  set t := b % a with ht
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) hab
  have hab' : a < b := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left a hM) hab
  by_cases h0 : t = 0
  · have hqa : b = a * q := by omega
    refine ⟨{q}, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      by_contra hc
      push Not at hc
      have h1 : q * a ≤ M * a := Nat.mul_le_mul_right a hc
      have h2 : b ≤ M * a := by rw [hqa, Nat.mul_comm]; exact h1
      exact absurd hab (not_lt.2 h2)
    · have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h] at hqa; omega
        · exact h
      rw [Finset.sum_singleton, hqa]
      push_cast
      have : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
      field_simp
  · have hbq : b < (q + 1) * a := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q a]; omega
    have hMq : M < q + 1 := by
      by_contra hc
      push Not at hc
      have h2 : (q + 1) * a ≤ M * a := Nat.mul_le_mul_right a hc
      exact lt_irrefl b (lt_trans (lt_of_lt_of_le hbq h2) hab)
    obtain ⟨S, hS, hsum⟩ := ih (a - t) (by omega) ((q + 1) * b) (q + 1) (by omega) (by omega)
      (mul_lt_mul_of_pos_left (by omega) (by omega))
    have hn : q + 1 ∉ S := fun h => lt_irrefl _ (hS _ h)
    refine ⟨insert (q + 1) S, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · exact hMq
      · exact lt_trans hMq (hS s hs)
    · rw [Finset.sum_insert hn, hsum]
      have key : ((a - t : ℕ) : ℚ) = (q + 1) * a - b := by
        have : (b : ℚ) = a * q + t := by exact_mod_cast hdiv.symm
        rw [Nat.cast_sub (by omega), this]
        ring
      rw [key]
      push_cast
      have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      have : ((q : ℚ) + 1) ≠ 0 := by
        have : (0 : ℚ) ≤ q := Nat.cast_nonneg q
        exact ne_of_gt (by linarith)
      field_simp
      ring

/-- GAP LEMMA: a sum of j ≤ K unit fractions below u/v misses it by at least 1/(2Kv)^(2^j). -/
lemma gap (K : ℕ) (hK : 1 ≤ K) : ∀ j : ℕ, ∀ s : Finset ℕ, s.card = j → j ≤ K →
    (∀ n ∈ s, 0 < n) → ∀ v : ℕ, 0 < v → ∀ u : ℤ,
    (∑ n ∈ s, (n : ℚ)⁻¹) < (u : ℚ) / v →
    1 / ((2 * K * v : ℚ) ^ (2 ^ j)) ≤ (u : ℚ) / v - ∑ n ∈ s, (n : ℚ)⁻¹ := by
  intro j
  induction j with
  | zero =>
    intro s hs _ _ v hv u hlt
    rw [Finset.card_eq_zero] at hs
    subst hs
    simp only [Finset.sum_empty, sub_zero, pow_zero, pow_one] at hlt ⊢
    have hv' : (0 : ℚ) < v := by exact_mod_cast hv
    have hu : (0 : ℚ) < u := by
      have := mul_pos hlt hv'
      rwa [div_mul_cancel₀ _ hv'.ne'] at this
    have hu1 : (1 : ℚ) ≤ u := by
      have : (0 : ℤ) < u := by exact_mod_cast hu
      exact_mod_cast this
    have hK' : (1 : ℚ) ≤ K := by exact_mod_cast hK
    have h1 : 1 / (2 * K * v : ℚ) ≤ 1 / v :=
      one_div_le_one_div_of_le hv' (by nlinarith)
    have h2 : 1 / (v : ℚ) ≤ u / v := (div_le_div_iff_of_pos_right hv').2 hu1
    linarith
  | succ j ih =>
    intro s hs hjK hpos v hv u hlt
    have hv' : (0 : ℚ) < v := by exact_mod_cast hv
    have hK' : (1 : ℚ) ≤ K := by exact_mod_cast hK
    have hsum0 : (0 : ℚ) ≤ ∑ n ∈ s, (n : ℚ)⁻¹ :=
      Finset.sum_nonneg (fun n _ => by positivity)
    have hu : (0 : ℚ) < u := by
      have := mul_pos (lt_of_le_of_lt hsum0 hlt) hv'
      rwa [div_mul_cancel₀ _ hv'.ne'] at this
    have hu1 : (1 : ℚ) ≤ u := by
      have : (0 : ℤ) < u := by exact_mod_cast hu
      exact_mod_cast this
    by_cases h : ∃ n ∈ s, n < 2 * K * v
    · obtain ⟨n, hn, hnlt⟩ := h
      have hn0 : 0 < n := hpos n hn
      have hn0' : (0 : ℚ) < n := by exact_mod_cast hn0
      have hsplit := Finset.add_sum_erase s (fun n : ℕ => (n : ℚ)⁻¹) hn
      have hcard : (s.erase n).card = j := by
        rw [Finset.card_erase_of_mem hn, hs]; rfl
      have htarget : ((u * n - v : ℤ) : ℚ) / ((v * n : ℕ) : ℚ) = (u : ℚ) / v - (n : ℚ)⁻¹ := by
        push_cast
        field_simp
      have hlt' : (∑ m ∈ s.erase n, (m : ℚ)⁻¹) < ((u * n - v : ℤ) : ℚ) / ((v * n : ℕ) : ℚ) := by
        rw [htarget]; linarith
      have hIH := ih (s.erase n) hcard (by omega) (fun m hm => hpos m (Finset.mem_of_mem_erase hm))
        (v * n) (Nat.mul_pos hv hn0) (u * n - v) hlt'
      rw [htarget] at hIH
      have hval : (u : ℚ) / v - (n : ℚ)⁻¹ - ∑ m ∈ s.erase n, (m : ℚ)⁻¹
          = (u : ℚ) / v - ∑ m ∈ s, (m : ℚ)⁻¹ := by
        rw [← hsplit]; ring
      rw [hval] at hIH
      refine le_trans ?_ hIH
      have hnle : (n : ℚ) ≤ 2 * K * v := by
        have : n ≤ 2 * K * v := hnlt.le
        exact_mod_cast this
      have hb0 : (0 : ℚ) < 2 * K * v := by positivity
      have hle : (2 * K * ((v * n : ℕ) : ℚ)) ≤ (2 * K * v) ^ 2 := by
        push_cast
        have : (2 * K * (v * n) : ℚ) = (2 * K * v) * n := by ring
        rw [this, sq]
        exact mul_le_mul_of_nonneg_left hnle hb0.le
      apply one_div_le_one_div_of_le
      · positivity
      · rw [pow_succ, pow_mul']
        exact pow_le_pow_left₀ (by positivity) hle _
    · push Not at h
      have hb0 : (0 : ℚ) < 2 * K * v := by positivity
      have hbound : (∑ n ∈ s, (n : ℚ)⁻¹) ≤ ∑ n ∈ s, ((2 * K * v : ℚ))⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have : 2 * K * v ≤ n := h n hn
        have h' : (2 * K * v : ℚ) ≤ n := by exact_mod_cast this
        exact inv_anti₀ hb0 h'
      rw [Finset.sum_const, hs, nsmul_eq_mul] at hbound
      have hjK' : ((j + 1 : ℕ) : ℚ) ≤ K := by exact_mod_cast hjK
      have h1 : ((j + 1 : ℕ) : ℚ) * (2 * K * v : ℚ)⁻¹ ≤ 1 / (2 * v) := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hb0 (by positivity)]
        nlinarith
      have h2 : 1 / (2 * v : ℚ) ≤ (u : ℚ) / v - 1 / (2 * v) := by
        have e : (1 : ℚ) / v = 1 / (2 * v) + 1 / (2 * v) := by field_simp; ring
        have h2' : 1 / (v : ℚ) ≤ u / v := (div_le_div_iff_of_pos_right hv').2 hu1
        linarith
      have h3 : 1 / ((2 * K * v : ℚ) ^ (2 ^ (j + 1))) ≤ 1 / (2 * v) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hge1 : (1 : ℚ) ≤ 2 * K * v := by
          have : (1 : ℚ) ≤ v := by exact_mod_cast hv
          nlinarith
        calc (2 * v : ℚ) ≤ 2 * K * v := by nlinarith
          _ ≤ (2 * K * v) ^ (2 ^ (j + 1)) := le_self_pow₀ hge1 (by positivity)
      linarith

end LW

theorem erdos_304.variants.lower_1950 :
    (fun b : ℕ => Real.log (Real.log b)) =O[atTop]
      (fun b => (smallestCollectionTo b : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 3 ?_
  rw [Filter.eventually_atTop]
  refine ⟨3, fun b hb => ?_⟩
  -- the fraction (b-1)/b is expressible
  obtain ⟨S, hS, hSsum⟩ := LW.egypt (b - 1) b 1 one_pos (by omega) (by omega)
  have hne : (unitFractionExpressible (b - 1) b).Nonempty := by
    refine ⟨S.card, S, rfl, fun n hn => hS n hn, ?_⟩
    rw [← hSsum]
    simp only [one_div]
  have hmem := Nat.sInf_mem hne
  set k := smallestCollection (b - 1) b with hkdef
  obtain ⟨s, hcard, hgt, hsum⟩ : k ∈ unitFractionExpressible (b - 1) b := hmem
  have hb' : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have hval : ((b - 1 : ℕ) : ℚ) / b = 1 - 1 / b := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, Finset.card_eq_zero] at hcard
    subst hcard
    rw [Finset.sum_empty, hval] at hsum
    have : (1 : ℚ) / b < 1 := by
      rw [div_lt_one hb']; exact_mod_cast (show 1 < b by omega)
    linarith
  have hlt : (∑ n ∈ s, (n : ℚ)⁻¹) < ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    rw [← hsum, hval]; push_cast
    have : (0 : ℚ) < 1 / b := by positivity
    linarith
  have hg := LW.gap k hk1 k s hcard le_rfl (fun n hn => by have := hgt n hn; omega) 1 one_pos 1 hlt
  rw [← hsum, hval] at hg
  push_cast at hg
  have hX : (0 : ℚ) < (2 * k) ^ (2 ^ k) := by positivity
  have hbX : (b : ℚ) ≤ (2 * k) ^ (2 ^ k) := by
    have : (1 : ℚ) / ((2 * k) ^ (2 ^ k)) ≤ 1 / b := by
      have e : (1 : ℚ) - (1 - 1 / b) = 1 / b := by ring
      simpa [e] using hg
    exact (one_div_le_one_div hX hb').1 this
  have hbXr : (b : ℝ) ≤ (2 * k : ℝ) ^ (2 ^ k) := by
    have : ((b : ℚ) : ℝ) ≤ (((2 * k) ^ (2 ^ k) : ℚ) : ℝ) := by exact_mod_cast hbX
    push_cast at this
    exact this
  -- logarithms
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlogb : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have h2k : (0 : ℝ) < Real.log (2 * k) := Real.log_pos (by linarith)
  have hl1 : Real.log b ≤ 2 ^ k * Real.log (2 * k) := by
    have := Real.log_le_log (by linarith) hbXr
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hl2 : Real.log (Real.log b) ≤ k * Real.log 2 + Real.log (Real.log (2 * k)) := by
    have := Real.log_le_log (by linarith) hl1
    rw [Real.log_mul (by positivity) h2k.ne', Real.log_pow] at this
    exact this
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hll : Real.log (Real.log (2 * k)) ≤ 2 * k := by
    have h1 := Real.log_le_sub_one_of_pos h2k
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * k by linarith)
    linarith
  have hmain : Real.log (Real.log b) ≤ 3 * k := by nlinarith
  have hkN : k ≤ smallestCollectionTo b := by
    unfold smallestCollectionTo
    refine le_csSup ⟨(Finset.Ico 1 b).sup (fun a => smallestCollection a b), ?_⟩
      ⟨b - 1, by simp; omega, rfl⟩
    rintro x ⟨a, ha, rfl⟩
    exact Finset.le_sup (f := fun a => smallestCollection a b) ha
  have hkNr : (k : ℝ) ≤ smallestCollectionTo b := by exact_mod_cast hkN
  have hnn : 0 ≤ Real.log (Real.log b) := Real.log_nonneg hlogb
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
  linarith

end Erdos304

#print axioms Erdos304.erdos_304.variants.lower_1950
