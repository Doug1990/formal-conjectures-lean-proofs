import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Fin

open Filter

open scoped Topology Real

namespace Erdos285

namespace LB

/-- Strictly increasing sequences on `Fin (k+1)` stay `k - i` below the last value. -/
lemma gap (k : ℕ) (n : Fin (k+1) → ℕ) (hn : StrictMono n) :
    ∀ t : ℕ, ∀ i : Fin (k+1), i.val + t = k → n i + t ≤ n (Fin.last k) := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have : i = Fin.last k := Fin.ext (by simp [Fin.val_last]; omega)
    subst this; simp
  | succ t ih =>
    intro i hi
    have hlt : i.val + 1 < k + 1 := by omega
    have h1 := ih ⟨i.val + 1, hlt⟩ (by simp; omega)
    have h2 : n i < n ⟨i.val + 1, hlt⟩ := hn (Fin.lt_def.mpr (by simp))
    omega

lemma log_sum (m : ℕ) (hm : 1 ≤ m) :
    ∀ K : ℕ, Real.log ((m:ℝ) + K) - Real.log m ≤ ∑ i ∈ Finset.range K, 1 / ((m:ℝ) + i) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0:ℝ) < (m:ℝ) + K := by
      have : (1:ℝ) ≤ m := by exact_mod_cast hm
      have : (0:ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    have hpos' : (0:ℝ) < (m:ℝ) + K + 1 := by linarith
    have hstep : Real.log ((m:ℝ) + K + 1) - Real.log ((m:ℝ) + K) ≤ 1 / ((m:ℝ) + K) := by
      rw [← Real.log_div hpos'.ne' hpos.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hpos' hpos)
      have e : ((m:ℝ) + K + 1) / ((m:ℝ) + K) - 1 = 1 / ((m:ℝ) + K) := by
        field_simp; ring
      linarith
    push_cast
    have e2 : (m:ℝ) + ((K:ℝ) + 1) = (m:ℝ) + K + 1 := by ring
    rw [e2]
    linarith

lemma key (k : ℕ) (n : Fin (k+1) → ℕ) (hn : StrictMono n) (h0 : 0 ∉ Set.range n)
    (hs : 1 = ∑ i, (1 : ℝ) / n i) :
    Real.exp 1 * k + 1 ≤ (Real.exp 1 - 1) * n (Fin.last k) := by
  set N := n (Fin.last k) with hN
  have hg : ∀ i : Fin (k+1), n i + (k - i.val) ≤ N := fun i =>
    gap k n hn (k - i.val) i (by have := i.isLt; omega)
  have hpos0 : 1 ≤ n 0 := by
    rcases Nat.eq_zero_or_pos (n 0) with h | h
    · exact absurd ⟨0, h⟩ h0
    · exact h
  have hkN : k + 1 ≤ N := by have := hg 0; simp at this; omega
  set m := N - k with hm
  have hm1 : 1 ≤ m := by omega
  have hmk : (m:ℝ) + k = N := by
    have : m + k = N := by omega
    exact_mod_cast this
  -- termwise bound
  have hterm : ∀ i : Fin (k+1), 1 / ((m:ℝ) + i.val) ≤ (1:ℝ) / n i := by
    intro i
    have hni : 1 ≤ n i := by
      rcases Nat.eq_zero_or_pos (n i) with h | h
      · exact absurd ⟨i, h⟩ h0
      · exact h
    have hle : n i ≤ m + i.val := by have := hg i; have := i.isLt; omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast hni
    · exact_mod_cast hle
  have hsum : ∑ i ∈ Finset.range (k+1), 1 / ((m:ℝ) + i) ≤ 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => 1 / ((m:ℝ) + i))]
    calc _ ≤ ∑ i, (1:ℝ) / n i := Finset.sum_le_sum (fun i _ => hterm i)
      _ = 1 := hs.symm
  have hlog := log_sum m hm1 (k+1)
  have hlog2 : Real.log ((N:ℝ) + 1) ≤ 1 + Real.log m := by
    have e : (m:ℝ) + ((k+1 : ℕ) : ℝ) = (N:ℝ) + 1 := by push_cast; linarith
    rw [e] at hlog
    linarith
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  have hNpos : (0:ℝ) < (N:ℝ) + 1 := by have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith
  have hexp : (N:ℝ) + 1 ≤ Real.exp 1 * m := by
    have := Real.exp_le_exp.mpr hlog2
    rw [Real.exp_log hNpos, Real.exp_add, Real.exp_log hmpos] at this
    exact this
  have : (m:ℝ) = N - k := by linarith
  rw [this] at hexp
  nlinarith

end LB

theorem erdos_285.variants.lb (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)) :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) ≤ f k := by
  refine ⟨fun k => -(1 / ((k:ℝ) + 1)), ?_, ?_⟩
  · have : (1 : ℕ → ℝ) = fun _ => (1:ℝ) := rfl
    rw [this, Asymptotics.isLittleO_one_iff]
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.neg
    rw [neg_zero] at h2
    exact h2
  · intro k hk
    obtain ⟨n, hn, h0, hs, hfk⟩ := (h k hk).1
    have hkey := LB.key k n hn h0 hs
    rw [hfk] at hkey
    have he : 1 < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    have he1 : 0 < Real.exp 1 - 1 := by linarith
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
    have e : (1 + -(1 / ((k:ℝ) + 1))) * rexp 1 / (rexp 1 - 1) * ((k:ℝ) + 1)
        = rexp 1 * k / (rexp 1 - 1) := by
      field_simp
      ring
    rw [e, div_le_iff₀ he1]
    nlinarith

end Erdos285

#print axioms Erdos285.erdos_285.variants.lb
