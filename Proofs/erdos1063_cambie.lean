import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring

open Finset
open scoped Nat

namespace Erdos1063

noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

lemma sub_eq {N d : ℕ} (hd : d ∣ N) : N - d = d * (N / d - 1) := by
  obtain ⟨q, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h]
  · rw [Nat.mul_div_cancel_left q h, Nat.mul_sub_one]

lemma coprime_aux (a c : ℕ) (ha : 0 < a) (hc : 0 < c) : Nat.Coprime a (a * c - 1) := by
  have h1 : Nat.gcd a (a * c - 1) ∣ a * c := Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) c
  have h2 : Nat.gcd a (a * c - 1) ∣ a * c - 1 := Nat.gcd_dvd_right _ _
  have h3 := Nat.dvd_sub h1 h2
  have h4 : a * c - (a * c - 1) = 1 := by
    have : 1 ≤ a * c := Nat.mul_pos ha hc
    omega
  rw [h4] at h3
  exact Nat.dvd_one.1 h3

/-- With `N = (m+1) L` and `1, …, m ∣ L`: `C(N, m+1) = L · ∏_{j<m} (N/(j+1) - 1)`. -/
lemma choose_eq (m L : ℕ) (hL : ∀ j, 1 ≤ j → j ≤ m → j ∣ L) :
    ((m + 1) * L).choose (m + 1) = L * ∏ j ∈ range m, ((m + 1) * L / (j + 1) - 1) := by
  have h1 := Nat.descFactorial_eq_factorial_mul_choose ((m + 1) * L) (m + 1)
  rw [Nat.descFactorial_eq_prod_range, Finset.prod_range_succ'] at h1
  have h3 : ∀ j ∈ range m, (m + 1) * L - (j + 1) = (j + 1) * ((m + 1) * L / (j + 1) - 1) := by
    intro j hj
    apply sub_eq
    exact Dvd.dvd.mul_left (hL (j + 1) (by omega) (by simp at hj; omega)) _
  rw [Finset.prod_congr rfl h3, Finset.prod_mul_distrib, Finset.prod_range_add_one_eq_factorial,
    Nat.sub_zero, Nat.factorial_succ] at h1
  have hpos : 0 < (m + 1) * m ! := Nat.mul_pos (Nat.succ_pos m) (Nat.factorial_pos m)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h1]
  ring

lemma mem_set (m L : ℕ) (hm : 1 ≤ m) (hL2 : 2 ≤ L) (hL : ∀ j, 1 ≤ j → j ≤ m → j ∣ L) :
    2 * (m + 1) ≤ (m + 1) * L ∧ ∃ i0 < m + 1, ¬ ((m + 1) * L - i0) ∣ ((m + 1) * L).choose (m + 1) ∧
      ∀ i < m + 1, i ≠ i0 → ((m + 1) * L - i) ∣ ((m + 1) * L).choose (m + 1) := by
  refine ⟨?_, 0, Nat.succ_pos m, ?_, ?_⟩
  · rw [Nat.mul_comm]; exact Nat.mul_le_mul le_rfl hL2
  · rw [choose_eq m L hL, Nat.sub_zero]
    intro h
    have hL0 : 0 < L := by omega
    have hcop : Nat.Coprime (m + 1) (∏ j ∈ range m, ((m + 1) * L / (j + 1) - 1)) := by
      apply Nat.Coprime.prod_right
      intro j hj
      have hdj : (j + 1) ∣ L := hL (j + 1) (by omega) (by simp at hj; omega)
      obtain ⟨c, hcL⟩ := hdj
      have hq : (m + 1) * L / (j + 1) = (m + 1) * c := by
        rw [hcL, show (m + 1) * ((j + 1) * c) = (j + 1) * ((m + 1) * c) by ring,
          Nat.mul_div_cancel_left _ (Nat.succ_pos j)]
      rw [hq]
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, Nat.mul_zero] at hcL; omega
        · exact h0
      exact coprime_aux (m + 1) c (Nat.succ_pos m) hc0
    generalize ∏ j ∈ range m, ((m + 1) * L / (j + 1) - 1) = P at h hcop
    have h' : (m + 1) ∣ P := by
      rw [Nat.mul_comm L P] at h
      exact Nat.dvd_of_mul_dvd_mul_right hL0 h
    have := Nat.Coprime.eq_one_of_dvd hcop h'
    omega
  · intro i hi hi0
    rw [choose_eq m L hL]
    have hiL : i ∣ L := hL i (by omega) (by omega)
    rw [sub_eq (Dvd.dvd.mul_left hiL (m + 1))]
    apply Nat.mul_dvd_mul hiL
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact Finset.dvd_prod_of_mem (f := fun j => (m + 1) * L / (j + 1) - 1)
      (Finset.mem_range.2 (by omega))

lemma lcm_facts (k : ℕ) (hk : 3 ≤ k) :
    2 ≤ (Finset.Icc 1 (k - 1)).lcm id ∧
      ∀ j, 1 ≤ j → j ≤ k - 1 → j ∣ (Finset.Icc 1 (k - 1)).lcm id := by
  have hd : ∀ j, 1 ≤ j → j ≤ k - 1 → j ∣ (Finset.Icc 1 (k - 1)).lcm id := fun j h1 h2 =>
    Finset.dvd_lcm (s := Finset.Icc 1 (k - 1)) (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  refine ⟨?_, hd⟩
  have h0 : (Finset.Icc 1 (k - 1)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; simp
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (hd 2 (by omega) (by omega))

theorem erdos_1063.variants.cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by
  obtain ⟨h2, hd⟩ := lcm_facts k hk
  have := mem_set (k - 1) _ (by omega) h2 hd
  rw [show k - 1 + 1 = k by omega] at this
  exact Nat.sInf_le this

theorem erdos_1063.variants.monier_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k ! := by
  refine le_trans (erdos_1063.variants.cambie_upper_bound hk) ?_
  have h : (Finset.Icc 1 (k - 1)).lcm id ∣ (k - 1)! := Finset.lcm_dvd fun j hj => by
    rw [Finset.mem_Icc] at hj
    show j ∣ _
    exact Nat.dvd_factorial (by omega) hj.2
  have := Nat.le_of_dvd (Nat.factorial_pos _) h
  calc k * (Finset.Icc 1 (k - 1)).lcm id ≤ k * (k - 1)! := Nat.mul_le_mul le_rfl this
    _ = k ! := Nat.mul_factorial_pred (by omega)

end Erdos1063

#print axioms Erdos1063.erdos_1063.variants.cambie_upper_bound
#print axioms Erdos1063.erdos_1063.variants.monier_upper_bound
