import Mathlib.Tactic.Ring

namespace OeisA112970

def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let k := n / 2
    if n % 2 = 1 then -- Odd case: a(2k + 1) = a(k)
      a k
    else -- Even case: a(2k) = a(k) + a(k - 2)
      let aPrev : ℕ :=
        -- a(m) is 0 if m < 0. Equivalent to checking k < 2 for the argument k-2.
        if k < 2 then 0
        else a (k - 2)
      a k + aPrev
termination_by n

theorem a_0 : a 0 = 1 := by unfold a; rfl

theorem a_2 : a 2 = 1 := by unfold a; unfold a; unfold a; rfl

theorem a_eq (n : ℕ) : a n = if n = 0 then 1 else if n = 1 then 1 else
    if n % 2 = 1 then a (n / 2) else a (n / 2) + (if n / 2 < 2 then 0 else a (n / 2 - 2)) := by
  rw [a]

theorem a_odd (k : ℕ) : a (2 * k + 1) = a k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [a_eq 1, if_neg (show (1 : ℕ) ≠ 0 by omega), if_pos rfl, a_0]
  · rw [a_eq (2 * k + 1), if_neg (show 2 * k + 1 ≠ 0 by omega),
      if_neg (show 2 * k + 1 ≠ 1 by omega), if_pos (show (2 * k + 1) % 2 = 1 by omega),
      show (2 * k + 1) / 2 = k by omega]

theorem a_even (k : ℕ) (hk : 1 ≤ k) :
    a (2 * k) = a k + (if k < 2 then 0 else a (k - 2)) := by
  rw [a_eq (2 * k), if_neg (show 2 * k ≠ 0 by omega), if_neg (show 2 * k ≠ 1 by omega),
    if_neg (show ¬ (2 * k % 2 = 1) by omega), show 2 * k / 2 = k by omega]

theorem h1 (m : ℕ) (hm : 1 ≤ m) : a (2 * m - 1) = a (m - 1) := by
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, a_odd]

theorem conjecture3 (n : ℕ) : a (2^n - 1) = 1 := by
  induction n with
  | zero => exact a_0
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_comm, h1 _ (Nat.two_pow_pos n), ih]

theorem three_pow (n : ℕ) : a (3 * 2^n - 1) = 1 := by
  induction n with
  | zero => exact a_2
  | succ n ih =>
    have hp := Nat.two_pow_pos n
    rw [Nat.pow_succ, show 3 * (2 ^ n * 2) = 2 * (3 * 2 ^ n) by ring,
      h1 _ (by omega), ih]

theorem conjecture2 (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  rw [conjecture3, three_pow]

theorem conjecture1 (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm, a_odd]

theorem c_val (m : ℕ) :
    a (2 ^ (m + 1) - 2) = (m + 2) / 2 ∧ a (2 ^ (m + 2) - 2) = (m + 3) / 2 := by
  induction m with
  | zero => exact ⟨a_0, a_2⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hP := Nat.two_pow_pos m
    have h3 := conjecture3 (m + 2)
    obtain ⟨P, hPdef⟩ : ∃ P, 2 ^ m = P := ⟨_, rfl⟩
    have e1 : 2 ^ (m + 1) = 2 * P := by rw [Nat.pow_succ, hPdef, Nat.mul_comm]
    have e2 : 2 ^ (m + 2) = 4 * P := by rw [Nat.pow_succ, e1]; ring
    have e3 : 2 ^ (m + 1 + 2) = 8 * P := by rw [Nat.pow_succ, e2]; ring
    rw [e1] at ih
    rw [e2] at h3
    rw [e3, show 8 * P - 2 = 2 * (4 * P - 1) by omega, a_even _ (by omega),
      if_neg (show ¬ (4 * P - 1 < 2) by omega), h3,
      show 4 * P - 1 - 2 = 2 * (2 * P - 2) + 1 by omega, a_odd, ih.1]
    omega

theorem arith (n : ℕ) : (n + 1) ^ 2 / 4 = n ^ 2 / 4 + (n + 1) / 2 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t ∨ n = 2 * t + 1 := ⟨n / 2, by omega⟩
  · have e1 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
    have e2 : (2 * t) ^ 2 = 4 * (t * t) := by ring
    rw [e1, e2]
    generalize t * t = s
    omega
  · have e1 : (2 * t + 1 + 1) ^ 2 = 4 * (t * t + 2 * t + 1) := by ring
    have e2 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
    rw [e1, e2]
    generalize t * t = s
    omega

theorem conjecture1_value (n : ℕ) : a (2^n) = n ^ 2 / 4 + 1 := by
  induction n with
  | zero => exact a_odd 0 ▸ a_0
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_comm, a_even _ (Nat.two_pow_pos n), ih]
    rcases n with _ | j
    · rw [if_pos (by decide : 2 ^ 0 < 2)]
      decide
    · have hge : 2 ≤ 2 ^ (j + 1) := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos j; omega
      rw [if_neg (show ¬ (2 ^ (j + 1) < 2) by omega), (c_val j).1, arith (j + 1)]
      omega

end OeisA112970

#print axioms OeisA112970.conjecture1
#print axioms OeisA112970.conjecture1_value
#print axioms OeisA112970.conjecture2
#print axioms OeisA112970.conjecture3
