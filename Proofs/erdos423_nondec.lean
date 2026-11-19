import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace Erdos423

def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

lemma step {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (k : ℕ) (hk : 1 ≤ k) : a k < a (k + 1) := by
  obtain ⟨h1, h2, hs⟩ := ha
  rcases Nat.eq_or_lt_of_le hk with rfl | hk'
  · show a 1 < a 2
    omega
  · have := (hs (k + 1) (by omega)).2.1
    simpa using this

theorem erdos_423.variants.nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m := by
  intro a ha n m hn hnm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := step ha (n + d) (by omega)
    rw [← Nat.add_assoc]
    omega

end Erdos423

#print axioms Erdos423.erdos_423.variants.nondecreasing
