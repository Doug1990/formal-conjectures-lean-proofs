import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

namespace BeaverMathOlympiad

namespace P3

/-- T t = Σ_{i=1}^{t} 2^{v₂ i}. -/
def T : ℕ → ℕ
  | 0 => 0
  | n + 1 => T n + 2 ^ (padicValNat 2 (n + 1))

theorem T_succ (n : ℕ) : T (n + 1) = T n + 2 ^ (padicValNat 2 (n + 1)) := rfl

theorem v2_odd (x : ℕ) (h : x % 2 = 1) : padicValNat 2 x = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun ⟨c, hc⟩ => by omega)

theorem v2_double (n : ℕ) (hn : n ≠ 0) : padicValNat 2 (2 * n) = padicValNat 2 n + 1 := by
  rw [padicValNat.mul two_ne_zero hn, padicValNat.self one_lt_two]; omega

theorem v2_eq (k m : ℕ) (hm : Odd m) : padicValNat 2 (2 ^ k * m) = k := by
  obtain ⟨r, rfl⟩ := hm
  have hnd : ¬ 2 ∣ 2 * r + 1 := fun ⟨c, hc⟩ => by omega
  rw [padicValNat.mul (Nat.two_pow_pos k).ne' (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnd, Nat.add_zero]

theorem pow_v2_odd (x : ℕ) (h : x % 2 = 1) : 2 ^ (padicValNat 2 x + 2) = 4 := by
  rw [v2_odd x h]; rfl

theorem pow_v2_two (x : ℕ) (h : x % 4 = 2) : 2 ^ (padicValNat 2 x + 2) = 8 := by
  have : x = 2 ^ 1 * (x / 2) := by omega
  rw [this, v2_eq 1 (x / 2) ⟨x / 4, by omega⟩]; rfl

theorem T_odd (s : ℕ) : T (2 * s + 1) = T (2 * s) + 1 := by
  rw [T_succ, v2_odd _ (by omega)]; rfl

theorem T_double (t : ℕ) : T (2 * t) = 2 * T t + t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, T_succ, T_odd, ih, T_succ,
      show 2 * t + 1 + 1 = 2 * (t + 1) by ring, v2_double _ (by omega), pow_succ]
    ring

theorem not_pow2 (x j : ℕ) (h1 : x % 4 = 2) (h2 : 6 ≤ x) : x ≠ 2 ^ j := by
  intro h
  rcases j with _ | _ | j
  · simp at h; omega
  · simp at h; omega
  · rw [pow_succ, pow_succ] at h; omega

theorem Hnot (t : ℕ) : ∀ p j, p % 4 = 2 → 6 ≤ p → 8 * T t + p * t + p ≠ 2 ^ j := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro p j hp hp6
    obtain ⟨q, rfl⟩ : ∃ q, p = 4 * q + 2 := ⟨p / 4, by omega⟩
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
    · rw [T_double]
      have e : (4 * q + 2) * (2 * s) = 4 * ((2 * q + 1) * s) := by ring
      rw [e]
      apply not_pow2 <;> omega
    · intro h
      have e : 8 * T (2 * s + 1) + (4 * q + 2) * (2 * s + 1) + (4 * q + 2)
          = 2 * (8 * T s + (4 * q + 2 + 4) * s + (4 * q + 2 + 4)) := by
        rw [T_odd, T_double]; ring
      rw [e] at h
      rcases j with _ | j
      · simp at h
      · rw [pow_succ] at h
        exact ih s (by omega) (4 * q + 2 + 4) j (by omega) (by omega) (by omega)

theorem Vval (k m : ℕ) (hm : Odd m) :
    ∃ r, Odd r ∧ 6 * (2 ^ k * m) + 8 * T (2 ^ k * m - 1) = 2 ^ (k + 1) * r := by
  induction k with
  | zero =>
    obtain ⟨s, rfl⟩ := hm
    refine ⟨10 * s + 3 + 8 * T s, ⟨5 * s + 1 + 4 * T s, by ring⟩, ?_⟩
    simp only [pow_zero, one_mul, zero_add, pow_one]
    rw [show 2 * s + 1 - 1 = 2 * s by omega, T_double]
    ring
  | succ k ih =>
    obtain ⟨r, hr, hv⟩ := ih
    refine ⟨r + 2 * m, hr.add_even (even_two_mul m), ?_⟩
    have h2 : 2 ^ (k + 1 + 1) * (r + 2 * m) = 2 * (2 ^ (k + 1) * r) + 8 * (2 ^ k * m) := by
      ring
    rw [h2, ← hv, show 2 ^ (k + 1) * m = 2 * (2 ^ k * m) by ring]
    have hpos : 0 < 2 ^ k * m := Nat.mul_pos (Nat.two_pow_pos k) hm.pos
    generalize 2 ^ k * m = s at *
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [show 2 * (s' + 1) - 1 = 2 * s' + 1 by omega, T_odd, T_double,
      show s' + 1 - 1 = s' by omega]
    ring

theorem seq (a : ℕ → ℕ) (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1) (t : ℕ) :
    a (4 * t + 2) = 12 * (t + 1) + 16 * T t := by
  induction t with
  | zero =>
    have h1 : a 1 = 9 := by rw [a_rec 0, a_ini, padicValNat.self one_lt_two]; rfl
    have h2 : a 2 = 12 := by rw [a_rec 1, h1, pow_v2_odd 9 (by decide)]
    rw [show 4 * 0 + 2 = 2 by rfl, h2]; rfl
  | succ t ih =>
    obtain ⟨k, m, hm, htm⟩ := Nat.exists_eq_two_pow_mul_odd (n := t + 1) (by omega)
    have hk : padicValNat 2 (t + 1) = k := by rw [htm, v2_eq k m hm]
    obtain ⟨r, hr, hv⟩ := Vval k m hm
    rw [← htm, show t + 1 - 1 = t by omega] at hv
    have hBe : 12 * (t + 1) + 16 * T t = 2 ^ (k + 2) * r := by
      rw [show 2 ^ (k + 2) * r = 2 * (2 ^ (k + 1) * r) by ring, ← hv]; ring
    have hB : padicValNat 2 (12 * (t + 1) + 16 * T t) = k + 2 := by
      rw [hBe, v2_eq _ r hr]
    have h16 : 2 ^ (k + 2 + 2) = 2 ^ k * 16 := by rw [pow_add, pow_add]; ring
    have hg : 0 < 2 ^ k := Nat.two_pow_pos k
    have e3 : a (4 * t + 3) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 - 1 := by
      rw [show 4 * t + 3 = 4 * t + 2 + 1 by omega, a_rec, ih, hB, h16]
    have e4 : a (4 * t + 4) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 + 2 := by
      rw [show 4 * t + 4 = 4 * t + 3 + 1 by omega, a_rec, e3, pow_v2_odd _ (by omega)]
      omega
    have e5 : a (4 * t + 5) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 + 9 := by
      rw [show 4 * t + 5 = 4 * t + 4 + 1 by omega, a_rec, e4, pow_v2_two _ (by omega)]
      omega
    rw [show 4 * (t + 1) + 2 = 4 * t + 5 + 1 by omega, a_rec, e5, pow_v2_odd _ (by omega),
      T_succ, hk]
    omega

theorem odd_terms (a : ℕ → ℕ) (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1) (t : ℕ) :
    a (4 * t + 3) = 12 * (t + 1) + 16 * T t + 2 ^ (padicValNat 2 (t + 1)) * 16 - 1 ∧
    a (4 * t + 4) = 12 * (t + 1) + 16 * T t + 2 ^ (padicValNat 2 (t + 1)) * 16 + 2 ∧
    a (4 * t + 5) = 12 * (t + 1) + 16 * T t + 2 ^ (padicValNat 2 (t + 1)) * 16 + 9 := by
  have ih := seq a a_ini a_rec t
  obtain ⟨k, m, hm, htm⟩ := Nat.exists_eq_two_pow_mul_odd (n := t + 1) (by omega)
  have hk : padicValNat 2 (t + 1) = k := by rw [htm, v2_eq k m hm]
  obtain ⟨r, hr, hv⟩ := Vval k m hm
  rw [← htm, show t + 1 - 1 = t by omega] at hv
  have hBe : 12 * (t + 1) + 16 * T t = 2 ^ (k + 2) * r := by
    rw [show 2 ^ (k + 2) * r = 2 * (2 ^ (k + 1) * r) by ring, ← hv]; ring
  have hB : padicValNat 2 (12 * (t + 1) + 16 * T t) = k + 2 := by
    rw [hBe, v2_eq _ r hr]
  have h16 : 2 ^ (k + 2 + 2) = 2 ^ k * 16 := by rw [pow_add, pow_add]; ring
  have hg : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [hk]
  have e3 : a (4 * t + 3) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 - 1 := by
    rw [show 4 * t + 3 = 4 * t + 2 + 1 by omega, a_rec, ih, hB, h16]
  have e4 : a (4 * t + 4) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 + 2 := by
    rw [show 4 * t + 4 = 4 * t + 3 + 1 by omega, a_rec, e3, pow_v2_odd _ (by omega)]
    omega
  have e5 : a (4 * t + 5) = 12 * (t + 1) + 16 * T t + 2 ^ k * 16 + 9 := by
    rw [show 4 * t + 5 = 4 * t + 4 + 1 by omega, a_rec, e4, pow_v2_two _ (by omega)]
    omega
  exact ⟨e3, e4, e5⟩

theorem pow4 (k : ℕ) : 4 ^ k = 1 ∨ 4 ^ k % 4 = 0 := by
  rcases k with _ | k
  · left; rfl
  · right; rw [pow_succ]; omega

end P3

open P3 in
theorem beaver_math_olympiad_problem_3
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1) :
    ¬ (∃ n k, a n = 4 ^ k) := by
  rintro ⟨n, k, h⟩
  have h1 : a 1 = 9 := by rw [a_rec 0, a_ini, padicValNat.self one_lt_two]; rfl
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rw [a_ini] at h; rcases pow4 k with h' | h' <;> omega
    · rw [h1] at h; rcases pow4 k with h' | h' <;> omega
  · obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 4 ∧ n = 4 * t + 2 + r :=
      ⟨(n - 2) / 4, (n - 2) % 4, Nat.mod_lt _ (by omega), by omega⟩
    obtain ⟨e3, e4, e5⟩ := odd_terms a a_ini a_rec t
    have hg : 0 < 2 ^ (padicValNat 2 (t + 1)) := Nat.two_pow_pos _
    obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    · rw [Nat.add_zero, seq a a_ini a_rec t] at h
      rcases k with _ | k
      · simp at h; omega
      · have hH := Hnot t 6 (2 * k + 1) (by decide) (by decide)
        apply hH
        have : 4 ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
          rw [pow_succ, pow_succ, pow_mul]; ring
        omega
    · rw [show 4 * t + 2 + 1 = 4 * t + 3 by omega, e3] at h
      rcases pow4 k with h' | h' <;> omega
    · rw [show 4 * t + 2 + 2 = 4 * t + 4 by omega, e4] at h
      rcases pow4 k with h' | h' <;> omega
    · rw [show 4 * t + 2 + 3 = 4 * t + 5 by omega, e5] at h
      rcases pow4 k with h' | h' <;> omega

end BeaverMathOlympiad

#print axioms BeaverMathOlympiad.beaver_math_olympiad_problem_3
