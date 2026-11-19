import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-- The set of subset sums of a set `A ⊆ M` (restated from FormalConjecturesForMathlib). -/
def subsetSums {M : Type*} [AddCommMonoid M] (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

open Filter

namespace Erdos18

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Every `m ≤ n!` is a sum of at most `n - 1` distinct divisors of `n!` (for `n ≥ 2`). -/
theorem rep (n : ℕ) (hn : 2 ≤ n) : ∀ m ≤ n.factorial, ∃ B : Finset ℕ,
    B ⊆ n.factorial.divisors ∧ B.card ≤ n - 1 ∧ ∑ i ∈ B, i = m := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro m hm
    have h2 : Nat.factorial 2 = 2 := rfl
    rw [h2] at hm ⊢
    interval_cases m
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by decide, by simp, by simp⟩
    · exact ⟨{2}, by decide, by simp, by simp⟩
  | succ n hn ih =>
    intro m hm
    rw [Nat.factorial_succ] at hm
    have hq : m / (n + 1) ≤ n.factorial := Nat.div_le_of_le_mul hm
    obtain ⟨B, hBsub, hBcard, hBsum⟩ := ih (m / (n + 1)) hq
    have hr : m % (n + 1) < n + 1 := Nat.mod_lt m (Nat.succ_pos n)
    have hdm : m = (n + 1) * (m / (n + 1)) + m % (n + 1) := (Nat.div_add_mod m (n + 1)).symm
    set q := m / (n + 1)
    set r := m % (n + 1)
    have hfpos : 0 < n.factorial := Nat.factorial_pos n
    have hinj : Set.InjOn (fun d : ℕ => d * (n + 1)) B := by
      intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) h
    have hsumB' : ∑ i ∈ B.image (fun d : ℕ => d * (n + 1)), i = (n + 1) * q := by
      rw [Finset.sum_image hinj, ← Finset.sum_mul, hBsum, Nat.mul_comm]
    have hsub' : B.image (fun d : ℕ => d * (n + 1)) ⊆ (n + 1).factorial.divisors := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hd' := Nat.dvd_of_mem_divisors (hBsub hd)
      refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
      rw [Nat.factorial_succ, Nat.mul_comm (n + 1)]
      exact Nat.mul_dvd_mul_right hd' _
    have hcard' : (B.image (fun d : ℕ => d * (n + 1))).card ≤ n - 1 :=
      (Finset.card_image_le).trans hBcard
    by_cases hr0 : r = 0
    · refine ⟨B.image (fun d : ℕ => d * (n + 1)), hsub', by omega, ?_⟩
      rw [hsumB']; omega
    · have hnot : r ∉ B.image (fun d : ℕ => d * (n + 1)) := by
        intro hx
        obtain ⟨d, hd, hdr⟩ := Finset.mem_image.mp hx
        have hdpos : 0 < d := Nat.pos_of_mem_divisors (hBsub hd)
        have : n + 1 ≤ d * (n + 1) := Nat.le_mul_of_pos_left _ hdpos
        omega
      refine ⟨insert r (B.image (fun d : ℕ => d * (n + 1))), ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
          exact Nat.dvd_factorial (by omega) (by omega)
        · exact hsub' h
      · rw [Finset.card_insert_of_notMem hnot]; omega
      · rw [Finset.sum_insert hnot, hsumB']; omega

theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  unfold practicalH
  rw [Finset.sup_lt_iff (by simp; omega)]
  intro m hm
  have hm' : m ≤ n.factorial := (Finset.mem_Icc.mp hm).2
  obtain ⟨B, hBsub, hBcard, hBsum⟩ := rep n hn m hm'
  have : sInf {k | ∃ D : Finset ℕ, D ⊆ n.factorial.divisors ∧ D.card = k ∧
      m ∈ subsetSums (D : Set ℕ)} ≤ B.card :=
    Nat.sInf_le ⟨B, hBsub, rfl, B, subset_refl _, hBsum.symm⟩
  omega

end Erdos18

#print axioms Erdos18.erdos_18_upper_bound
