import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter
namespace LegendreConjecture

/-- The prime gap bound gives `p_{j+1} < p_j + √p_j`. -/
lemma gap_le {c : ℝ} (hc : 0 < c) (j n : ℕ) (hj : j.nth Nat.Prime ≤ n ^ 2)
    (h : ((j + 1).nth Nat.Prime : ℝ) - j.nth Nat.Prime < (j.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c)) :
    (j + 1).nth Nat.Prime < j.nth Nat.Prime + n := by
  have hp1 : (1 : ℝ) ≤ j.nth Nat.Prime := by
    exact_mod_cast (Nat.prime_nth_prime j).one_lt.le
  have e1 : (j.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c) ≤ (j.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have e2 : (j.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ)) ≤ n := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (j.nth Nat.Prime : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hj)
      _ = n := Real.sqrt_sq (Nat.cast_nonneg _)
  have : ((j + 1).nth Nat.Prime : ℝ) < j.nth Nat.Prime + n := by linarith
  exact_mod_cast this

theorem bounded_gap_legendre
    (H : ∃ c > 0, ∀ᶠ n in atTop, (n + 1).nth Nat.Prime - n.nth Nat.Prime <
      (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c)) :
    ∀ᶠ n in atTop, ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p := by
  obtain ⟨c, hc, hev⟩ := H
  obtain ⟨N0, hN⟩ := Filter.eventually_atTop.1 hev
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  refine Filter.eventually_atTop.2 ⟨max 2 (N0.nth Nat.Prime), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hnN : N0.nth Nat.Prime ≤ n := le_of_max_le_right hn
  have hex : ∃ k : ℕ, n ^ 2 < k.nth Nat.Prime := ⟨n ^ 2 + 1, by
    have := hmono.id_le (n ^ 2 + 1)
    simp only [id] at this
    omega⟩
  classical
  let k := Nat.find hex
  have hk : n ^ 2 < k.nth Nat.Prime := Nat.find_spec hex
  have hmin : ∀ i < k, i.nth Nat.Prime ≤ n ^ 2 := fun i hi =>
    Nat.le_of_not_lt (Nat.find_min hex hi)
  have hn2' : 4 ≤ n ^ 2 := by nlinarith
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, Nat.nth_prime_zero_eq_two] at hk
    omega
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjle : j.nth Nat.Prime ≤ n ^ 2 := hmin j (by omega)
  have hjN : N0 ≤ j := by
    by_contra hlt
    have : (j + 1).nth Nat.Prime ≤ N0.nth Nat.Prime :=
      hmono.monotone (by omega)
    rw [← hj] at this
    have : n ≤ n ^ 2 := by nlinarith
    omega
  have hg := gap_le hc j n hjle (hN j hjN)
  rw [← hj] at hg
  refine ⟨k.nth Nat.Prime, ⟨hk, ?_⟩, Nat.prime_nth_prime k⟩
  have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  omega

end LegendreConjecture

#print axioms LegendreConjecture.bounded_gap_legendre
