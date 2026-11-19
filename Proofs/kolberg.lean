import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

namespace Nat

def partitionNumber : ℕ → ℕ := fun n ↦ Fintype.card (Nat.Partition n)

end Nat

namespace PartitionParity

open Nat PowerSeries PowerSeries.WithPiTopology

/-- Euler: (Σ p(n) Xⁿ) · ∏ (1 - X^(i+1)) = 1, here with the pentagonal series. -/
theorem gen_id :
    (PowerSeries.mk fun n ↦ (partitionNumber n : ZMod 2)) * pentagonalSeries (ZMod 2) = 1 := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have h1 := Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2) (fun _ ↦ True)
  have h2 := hasProd_one_sub_X_pow (ZMod 2)
  have h3 := h1.mul h2
  have hp : (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (fun _ ↦ True)).card : ZMod 2))
      = PowerSeries.mk fun n ↦ (partitionNumber n : ZMod 2) := by
    ext n
    simp [Nat.Partition.restricted, partitionNumber]
  rw [hp] at h3
  have h4 : (fun i : ℕ ↦ (if True then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1) *
      (1 - X ^ (i + 1))) = fun _ ↦ 1 := by
    funext i
    simp only [if_true, pow_mul]
    exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  rw [h4] at h3
  exact h3.unique hasProd_one

theorem coeff_pent_pent (k : ℤ) : (pentagonalSeries (ZMod 2)).coeff (pentagonal k) = 1 := by
  rw [coeff_pentagonalSeries_pentagonal]
  rcases Int.units_eq_one_or (Int.negOnePow k) with h | h <;> rw [h] <;> decide

/-- Gap before the pentagonal number of a positive index `K`. -/
theorem gap (K : ℕ) (k : ℤ) (h : pentagonal k < pentagonal (K : ℤ)) :
    pentagonal k + (2 * K - 1) ≤ pentagonal (K : ℤ) := by
  have e1 := two_mul_natCast_pentagonal k
  have e2 := two_mul_natCast_pentagonal (K : ℤ)
  have h' : (pentagonal k : ℤ) < pentagonal (K : ℤ) := by exact_mod_cast h
  have hK : (1 : ℤ) ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [pentagonal_def] at h
    · exact_mod_cast hK
  suffices (pentagonal k : ℤ) + (2 * K - 1) ≤ pentagonal (K : ℤ) by omega
  rcases le_or_gt (K : ℤ) k with hk | hk
  · nlinarith
  rcases le_or_gt k (-(K : ℤ)) with hk' | hk'
  · nlinarith
  · have a1 : k ≤ (K : ℤ) - 1 := by omega
    have a2 : -((K : ℤ) - 1) ≤ k := by omega
    nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 a2)]

/-- A power series over ZMod 2 that is a polynomial with constant term 1, multiplied by the
pentagonal series, has coefficient 1 at arbitrarily large indices. -/
theorem key (B : (ZMod 2)⟦X⟧) (N : ℕ) (h0 : B.coeff 0 = 1) (hB : ∀ i, N < i → B.coeff i = 0)
    (L : ℕ) : ∃ m, L ≤ m ∧ (B * pentagonalSeries (ZMod 2)).coeff m = 1 := by
  refine ⟨pentagonal ((N + L + 1 : ℕ) : ℤ), ?_, ?_⟩
  · have e2 := two_mul_natCast_pentagonal ((N + L + 1 : ℕ) : ℤ)
    have : (L : ℤ) ≤ pentagonal ((N + L + 1 : ℕ) : ℤ) := by push_cast at e2 ⊢; nlinarith
    exact_mod_cast this
  set m := pentagonal ((N + L + 1 : ℕ) : ℤ) with hm
  rw [coeff_mul, Finset.sum_eq_single (0, m)]
  · simp [h0, hm]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    simp only at hij
    rcases Nat.lt_or_ge N i with hi | hi
    · simp [hB i hi]
    · have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · exact absurd (by simp at hij; simp [hij]) hne
        · exact h
      have hj : j ∉ Set.range pentagonal := by
        rintro ⟨k, rfl⟩
        have := gap (N + L + 1) k (by omega)
        omega
      simp [coeff_pentagonalSeries_eq_zero (ZMod 2) hj]
  · intro h; exact absurd (Finset.mem_antidiagonal.2 (by simp)) h

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem kolberg :
    {n : ℕ | Even (partitionNumber n)}.Infinite ∧ {n : ℕ | Odd (partitionNumber n)}.Infinite := by
  have p0 : (partitionNumber 0 : ZMod 2) = 1 := by
    have : partitionNumber 0 = 1 := by decide
    rw [this]; rfl
  constructor
  · -- if p(n) is odd for all n ≥ N, use B = (1 + X) · A
    intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    let A : (ZMod 2)⟦X⟧ := PowerSeries.mk fun n ↦ (partitionNumber n : ZMod 2)
    have hA : ∀ n, N < n → A.coeff n = 1 := by
      intro n hn
      have : n ∉ {n : ℕ | Even (partitionNumber n)} := fun h ↦ absurd (hN h) (by omega)
      simp only [Set.mem_ofPred_eq] at this
      rcases zmod2_cases (partitionNumber n : ZMod 2) with h | h
      · exact absurd ((ZMod.natCast_eq_zero_iff_even).1 h) this
      · simpa [A] using h
    obtain ⟨m, hm, hc⟩ := key ((1 + X) * A) (N + 1) (by simp [A, p0])
      (by
        intro i hi
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [add_mul, one_mul, map_add, coeff_succ_X_mul, hA _ (by omega), hA _ (by omega)]
        decide) 2
    rw [mul_assoc, gen_id, mul_one] at hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    rw [map_add, coeff_one, coeff_X] at hc
    simp at hc
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    let A : (ZMod 2)⟦X⟧ := PowerSeries.mk fun n ↦ (partitionNumber n : ZMod 2)
    have hA : ∀ n, N < n → A.coeff n = 0 := by
      intro n hn
      have : n ∉ {n : ℕ | Odd (partitionNumber n)} := fun h ↦ absurd (hN h) (by omega)
      simp only [Set.mem_ofPred_eq, Nat.not_odd_iff_even] at this
      simpa [A] using (ZMod.natCast_eq_zero_iff_even).2 this
    obtain ⟨m, hm, hc⟩ := key A N (by simp [A, p0]) hA 1
    rw [gen_id] at hc
    rw [coeff_one, if_neg (by omega)] at hc
    exact absurd hc (by decide)

end PartitionParity

#print axioms PartitionParity.kolberg
