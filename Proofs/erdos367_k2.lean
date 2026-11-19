import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Asymptotics Filter

namespace Erdos367

def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

lemma B_dvd (r m : ℕ) (hm : m ≠ 0) : B r m ∣ m := by
  unfold B
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

lemma prod_le (k n : ℕ) (hk : k ≤ 2) (hn : 1 ≤ n) :
    (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ 4 * n ^ 2 := by
  have h1 : (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ (n + 1) ^ (Finset.Ico n (n + k)).card := by
    apply Finset.prod_le_pow_card
    intro m hm
    rw [Finset.mem_Ico] at hm
    have := Nat.le_of_dvd (by omega) (B_dvd 2 m (by omega))
    omega
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at h1
  have h2 : (n + 1) ^ k ≤ (n + 1) ^ 2 := Nat.pow_le_pow_right (by omega) hk
  have h3 : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  omega

theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro k hk
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_two]
  exact_mod_cast prod_le k n hk hn

end Erdos367

#print axioms Erdos367.erdos_367.variants.k_le_two
