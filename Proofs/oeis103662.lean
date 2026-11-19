import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases

namespace OeisA103662

open Nat List Set

def IsValidZerolessPower (n b : ℕ) : Prop :=
  b > 1 ∧ 0 ∉ digits 10 (b ^ n)

noncomputable def a (n : ℕ) : ℕ :=
  let smallestBase := sInf { b | IsValidZerolessPower n b }
  smallestBase ^ n

namespace P

theorem zero_mem : ∀ (k N : ℕ), 0 < N / 10 ^ k → (N / 10 ^ k) % 10 = 0 → 0 ∈ digits 10 N := by
  intro k
  induction k with
  | zero =>
    intro N h1 h2
    simp only [pow_zero, Nat.div_one] at h1 h2
    rw [Nat.digits_def' (by omega) h1, h2]
    exact List.mem_cons_self
  | succ k ih =>
    intro N h1 h2
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp at h1
      · exact h
    have e : N / 10 ^ (k + 1) = N / 10 / 10 ^ k := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [e] at h1 h2
    rw [Nat.digits_def' (by omega) hN]
    exact List.mem_cons_of_mem _ (ih _ h1 h2)

theorem odd16 (b : ℕ) (hb : b % 2 = 1) : b ^ 2500 % 16 = 1 := by
  have h4 : b ^ 4 % 16 = 1 := by
    rw [Nat.pow_mod]
    have : b % 16 < 16 := Nat.mod_lt _ (by omega)
    have h2 : b % 16 % 2 = 1 := by omega
    generalize b % 16 = r at this h2
    interval_cases r <;> simp_all
  rw [show 2500 = 4 * 625 from rfl, pow_mul, Nat.pow_mod, h4]
  simp

theorem cop3125 (b : ℕ) (hb : ¬ 5 ∣ b) : b ^ 2500 % 3125 = 1 := by
  have hc : Nat.Coprime b (5 ^ 5) := by
    apply Nat.Coprime.symm
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hb
  have := Nat.ModEq.pow_totient hc
  rw [Nat.totient_prime_pow Nat.prime_five (by omega)] at this
  exact this

theorem big (b : ℕ) (hb : 1 < b) : 10 ^ 5 ≤ b ^ 2500 := by
  calc 10 ^ 5 ≤ 2 ^ 17 := by norm_num
    _ ≤ 2 ^ 2500 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ b ^ 2500 := Nat.pow_le_pow_left (by omega) _

theorem dvd_pow (b d e : ℕ) (h : d ∣ b) (he : e ≤ 2500) : d ^ e ∣ b ^ 2500 :=
  (pow_dvd_pow_of_dvd h e).trans (pow_dvd_pow b he)

theorem key (b : ℕ) (hb : 1 < b) : 0 ∈ digits 10 (b ^ 2500) := by
  have hbig := big b hb
  by_cases h2 : 2 ∣ b <;> by_cases h5 : 5 ∣ b
  · -- 10 ∣ b
    have h10 : 2 ^ 1 ∣ b ^ 2500 := dvd_pow b 2 1 h2 (by omega)
    have h50 : 5 ^ 1 ∣ b ^ 2500 := dvd_pow b 5 1 h5 (by omega)
    generalize b ^ 2500 = N at *
    apply zero_mem 0 N <;> simp only [pow_zero, Nat.div_one, pow_one] at * <;> omega
  · have h32 : 2 ^ 5 ∣ b ^ 2500 := dvd_pow b 2 5 h2 (by omega)
    have h3 := cop3125 b h5
    generalize b ^ 2500 = N at *
    apply zero_mem 4 N <;> norm_num at * <;> omega
  · have h625 : 5 ^ 4 ∣ b ^ 2500 := dvd_pow b 5 4 h5 (by omega)
    have h16 := odd16 b (by omega)
    generalize b ^ 2500 = N at *
    apply zero_mem 3 N <;> norm_num at * <;> omega
  · have h16 := odd16 b (by omega)
    have h3 := cop3125 b h5
    generalize b ^ 2500 = N at *
    apply zero_mem 1 N <;> norm_num at * <;> omega

end P

theorem conjecture : ∃ n : ℕ, a n = 0 := by
  refine ⟨2500, ?_⟩
  have hE : { b | IsValidZerolessPower 2500 b } = (∅ : Set ℕ) := by
    ext b
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false, iff_false]
    rintro ⟨hb, hd⟩
    exact hd (P.key b hb)
  simp only [a, hE, Nat.sInf_empty]
  norm_num

end OeisA103662

#print axioms OeisA103662.conjecture
