import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Finset.Nat

namespace OeisA397588

/-- Manyama's coefficient recurrence, extended by $a(0)=0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (n + 3) * ∑ k ∈ (Finset.Icc 1 (n + 1)).attach, a k.1 * a (n + 2 - k.1)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp k.2).2
  · exact Nat.sub_lt (Nat.succ_pos _) (Finset.mem_Icc.mp k.2).1

/-- The recurrence without attached membership proofs. -/
theorem a_succ_succ (n : ℕ) :
    a (n + 2) = (n + 3) * ∑ k ∈ Finset.Icc 1 (n + 1), a k * a (n + 2 - k) := by
  simp only [a]
  exact congrArg (fun t => (n + 3) * t)
    (Finset.sum_attach (Finset.Icc 1 (n + 1)) (fun k => a k * a (n + 2 - k)))

/-- Manyama's recurrence for every index greater than one. -/
theorem a_of_gt_one {n : ℕ} (hn : 1 < n) :
    a n = (n + 1) * ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => simp [a_succ_succ]

theorem a_0 : a 0 = 0 := by
  simp only [a]

theorem a_1 : a 1 = 1 := by
  simp only [a]

namespace P

lemma zz : ∀ x : ZMod 2, x + x = 0 := by decide

lemma sq2 : ∀ x : ZMod 2, x * x = x := by decide

lemma sym_sum (N : ℕ) (f : ℕ → ZMod 2) (hf : ∀ k ≤ N, f (N - k) = f k) :
    ∑ k ∈ Finset.range (N + 1), f k = if Even N then f (N / 2) else 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun k => 2 * k = N)]
  have h0 : ∑ k ∈ (Finset.range (N + 1)).filter (fun k => ¬ 2 * k = N), f k = 0 := by
    refine Finset.sum_involution (fun k _ => N - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rw [hf k (by omega)]
      exact zz _
    · intro k hk _
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
  rw [h0, add_zero]
  split_ifs with he
  · obtain ⟨r, hr⟩ := he
    have : (Finset.range (N + 1)).filter (fun k => 2 * k = N) = {N / 2} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this, Finset.sum_singleton]
  · have : (Finset.range (N + 1)).filter (fun k => 2 * k = N) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k _ h => he ⟨k, by omega⟩)
    rw [this, Finset.sum_empty]

/-- the recurrence with the full convolution over `range (n+1)` -/
lemma a_full {n : ℕ} (hn : 1 < n) :
    a n = (n + 1) * ∑ k ∈ Finset.range (n + 1), a k * a (n - k) := by
  rw [a_of_gt_one hn]
  congr 1
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc] at hk'
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, a_0, zero_mul]
    · have : n - k = 0 := by omega
      rw [this, a_0, mul_zero]

lemma a_mod {n : ℕ} (hn : 1 < n) :
    (a n : ZMod 2) = (n + 1 : ZMod 2) * (if Even n then (a (n / 2) : ZMod 2) else 0) := by
  rw [a_full hn]
  push_cast
  congr 1
  rw [sym_sum n (fun k => (a k : ZMod 2) * a (n - k)) ?_]
  · try dsimp only
    split_ifs with he
    · obtain ⟨r, hr⟩ := he
      have : n - n / 2 = n / 2 := by omega
      rw [this]
      exact sq2 _
    · rfl
  · intro k hk
    try dsimp only
    rw [show n - (n - k) = k by omega, mul_comm]

lemma a_even_mod (m : ℕ) (hm : 1 ≤ m) : (a (2 * m) : ZMod 2) = a m := by
  rw [a_mod (by omega), if_pos ⟨m, by omega⟩, show 2 * m / 2 = m by omega]
  push_cast
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_mul, zero_add, one_mul]

lemma a_odd_mod (m : ℕ) (hm : 1 ≤ m) : (a (2 * m + 1) : ZMod 2) = 0 := by
  rw [a_mod (by omega), if_neg (by rintro ⟨r, hr⟩; omega), mul_zero]

end P

theorem conjecture_parity (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [← ZMod.natCast_eq_one_iff_odd]
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨m, hm⟩
  · have hr2 : n = 2 * r := by omega
    have hr1 : 1 ≤ r := by omega
    subst hr2
    rw [P.a_even_mod r hr1, ZMod.natCast_eq_one_iff_odd, ih r (by omega) hr1]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by rw [pow_succ]; omega⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | j
      · rw [pow_zero] at hk
        omega
      · exact ⟨j, by rw [pow_succ] at hk; omega⟩
  · subst hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [show 2 * 0 + 1 = 1 from rfl, a_1, Nat.cast_one]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    · rw [P.a_odd_mod m hpos]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro ⟨k, hk⟩
        rcases k with _ | j
        · rw [pow_zero] at hk
          omega
        · rw [pow_succ] at hk
          omega

theorem three_dvd_a (n : ℕ) (hn : 1 < n) : 3 ∣ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [a_of_gt_one hn]
  by_cases h2 : n = 2
  · subst h2
    exact Dvd.dvd.mul_right (by decide) _
  · apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hk2 : 2 ≤ k
    · exact Dvd.dvd.mul_right (ih k (by omega) (by omega)) _
    · exact Dvd.dvd.mul_left (ih (n - k) (by omega) (by omega)) _

end OeisA397588

#print axioms OeisA397588.conjecture_parity
#print axioms OeisA397588.three_dvd_a
