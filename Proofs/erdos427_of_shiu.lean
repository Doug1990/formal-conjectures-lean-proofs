import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos427

def erdos427 : Prop := ∀ (n d : ℕ),
    d ≠ 0 → ∃ k, k ≠ 0 ∧
    d ∣ ∑ i ∈ Finset.Ico n (n + k), i.nth Nat.Prime

def ShiuTheorem : Prop := ∀ (k a q : ℕ), 1 ≤ k → 1 ≤ q → a.gcd q = 1 →
    { m : ℕ | ∀ p ∈ (Finset.Ico m (m + k)).image (Nat.nth Nat.Prime), p ≡ a [MOD q]}.Infinite

theorem erdos_427.variants.of_shiu (H : ShiuTheorem) : erdos427 := by
  intro n d hd
  obtain ⟨m, hm, hnm⟩ := (H d 1 d (by omega) (by omega) (Nat.gcd_one_left d)).exists_gt n
  have hcong : ∀ i, i < d → (m + i).nth Nat.Prime ≡ 1 [MOD d] := fun i hi =>
    hm _ (Finset.mem_image_of_mem _ (Finset.mem_Ico.2 ⟨by omega, by omega⟩))
  set S := ∑ i ∈ Finset.Ico n m, i.nth Nat.Prime with hS
  have hpart : ∀ j, j ≤ d →
      ∑ i ∈ Finset.Ico n (m + j), i.nth Nat.Prime ≡ S + j [MOD d] := by
    intro j
    induction j with
    | zero => intro _; simp [hS]; rfl
    | succ j ih =>
      intro hj
      rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), ← Nat.add_assoc]
      exact (ih (by omega)).add (hcong j (by omega))
  have hr := Nat.mod_lt S (Nat.pos_of_ne_zero hd)
  have hdvd : d ∣ S + (d - S % d) := by
    refine ⟨S / d + 1, ?_⟩
    have := Nat.div_add_mod S d
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨m + (d - S % d) - n, by omega, ?_⟩
  rw [show n + (m + (d - S % d) - n) = m + (d - S % d) by omega]
  exact (Nat.modEq_zero_iff_dvd).1
    ((hpart _ (by omega)).trans ((Nat.modEq_zero_iff_dvd).2 hdvd))

end Erdos427

#print axioms Erdos427.erdos_427.variants.of_shiu
