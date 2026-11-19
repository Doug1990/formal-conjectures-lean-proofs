import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

namespace Arxiv.«2607.08366»

variable {N : ℕ}

def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = #A → ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

namespace MM

/-- `g p x = x / 2^p + (number of one bits of x mod 2^p)`: the least number of powers
of two `≤ 2^p` summing to `x`. -/
def g : ℕ → ℕ → ℕ
  | 0, x => x
  | p + 1, x => g p (x / 2) + x % 2

theorem g_zero (x : ℕ) : g 0 x = x := rfl
theorem g_succ (p x : ℕ) : g (p + 1) x = g p (x / 2) + x % 2 := rfl

theorem g_le (p x : ℕ) : g p x ≤ x := by
  induction p generalizing x with
  | zero => exact le_rfl
  | succ p ih =>
    rw [g_succ]
    have := ih (x / 2)
    omega

theorem g_add (p a b : ℕ) : g p (a + b) ≤ g p a + g p b := by
  induction p generalizing a b with
  | zero => exact le_rfl
  | succ p ih =>
    simp only [g_succ]
    have h2 := ih (a / 2) (b / 2)
    have h1 := ih (a / 2 + b / 2) 1
    have h3 := g_le p 1
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
    · rw [show (a + b) / 2 = a / 2 + b / 2 by omega, show (a + b) % 2 = 0 by omega]; omega
    · rw [show (a + b) / 2 = a / 2 + b / 2 by omega, show (a + b) % 2 = 1 by omega]; omega
    · rw [show (a + b) / 2 = a / 2 + b / 2 by omega, show (a + b) % 2 = 1 by omega]; omega
    · rw [show (a + b) / 2 = a / 2 + b / 2 + 1 by omega, show (a + b) % 2 = 0 by omega]
      omega

theorem g_lip (p x y : ℕ) : g p (x + y) ≤ g p x + y :=
  (g_add p x y).trans (by have := g_le p y; omega)

theorem g_split (p a : ℕ) : ∀ b, b < 2 ^ p → g p (2 ^ p * a + b) = a + g p b := by
  induction p with
  | zero =>
    intro b hb
    rw [pow_zero] at hb
    show 2 ^ 0 * a + b = a + b
    rw [pow_zero]; omega
  | succ p ih =>
    intro b hb
    rw [g_succ, g_succ]
    rw [pow_succ, mul_comm (2 ^ p) 2] at hb
    rw [pow_succ, mul_comm (2 ^ p) 2, mul_assoc]
    rw [show (2 * (2 ^ p * a) + b) / 2 = 2 ^ p * a + b / 2 by omega,
      show (2 * (2 ^ p * a) + b) % 2 = b % 2 by omega, ih (b / 2) (by omega)]
    omega

theorem g_full (p : ℕ) : g p (2 ^ p - 1) = p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [g_succ]
    have h1 := Nat.one_le_two_pow (n := p)
    rw [pow_succ, show (2 ^ p * 2 - 1) / 2 = 2 ^ p - 1 by omega,
      show (2 ^ p * 2 - 1) % 2 = 1 by omega, ih]

theorem g_shift (q L x : ℕ) : g (q + L) (2 ^ L * x) = g q x := by
  induction L with
  | zero => simp
  | succ L ih =>
    show g ((q + L) + 1) _ = _
    rw [g_succ, pow_succ, mul_comm (2 ^ L) 2, mul_assoc,
      show 2 * (2 ^ L * x) / 2 = 2 ^ L * x by omega,
      show 2 * (2 ^ L * x) % 2 = 0 by omega, ih]
    rfl

theorem decomp (p : ℕ) (m : ℕ → ℕ) :
    ∑ k ∈ range (p + 2), m k * 2 ^ k
      = 2 * ∑ k ∈ range (p + 1), m (k + 1) * 2 ^ k + m 0 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem key (p : ℕ) : ∀ m : ℕ → ℕ,
    g p (∑ k ∈ range (p + 1), m k * 2 ^ k) ≤ ∑ k ∈ range (p + 1), m k := by
  induction p with
  | zero => intro m; simp [g_zero]
  | succ p ih =>
    intro m
    rw [decomp p m, Finset.sum_range_succ' _ (p + 1), g_succ]
    have h := ih (fun k => m (k + 1))
    generalize ∑ k ∈ range (p + 1), m (k + 1) * 2 ^ k = T at *
    generalize ∑ k ∈ range (p + 1), m (k + 1) = S at *
    rw [show (2 * T + m 0) / 2 = T + m 0 / 2 by omega, show (2 * T + m 0) % 2 = m 0 % 2 by omega]
    have := g_lip p T (m 0 / 2)
    omega

theorem uniq (p : ℕ) : ∀ m : ℕ → ℕ, ∑ k ∈ range (p + 1), m k = p + 1 →
    ∑ k ∈ range (p + 1), m k * 2 ^ k = 2 ^ (p + 1) - 1 → ∀ k < p + 1, m k = 1 := by
  induction p with
  | zero =>
    intro m h1 _ k hk
    simp at h1
    obtain rfl : k = 0 := by omega
    exact h1
  | succ p ih =>
    intro m h1 h2 k hk
    rw [decomp p m] at h2
    rw [Finset.sum_range_succ' _ (p + 1)] at h1
    have hK := key p (fun k => m (k + 1))
    have hfull : g p (2 ^ (p + 1) - 1) = p + 1 := by
      have h0 := Nat.one_le_two_pow (n := p)
      rw [pow_succ, show 2 ^ p * 2 - 1 = 2 ^ p * 1 + (2 ^ p - 1) by omega,
        g_split p 1 _ (by omega), g_full]
      omega
    have hp1 := Nat.one_le_two_pow (n := p)
    have hpow : 2 ^ (p + 1 + 1) = 2 ^ p * 2 * 2 := by rw [pow_succ, pow_succ]
    have hpow' : 2 ^ (p + 1) = 2 ^ p * 2 := pow_succ 2 p
    generalize hT : ∑ k ∈ range (p + 1), m (k + 1) * 2 ^ k = T at *
    generalize hS : ∑ k ∈ range (p + 1), m (k + 1) = S at *
    have hodd : m 0 % 2 = 1 := by omega
    have hT' : T + (m 0 - 1) / 2 = 2 ^ (p + 1) - 1 := by omega
    have ha := g_add p T ((m 0 - 1) / 2)
    have hb := g_le p ((m 0 - 1) / 2)
    rw [hT', hfull] at ha
    have hm0 : m 0 = 1 := by omega
    rcases k with _ | k
    · exact hm0
    · have hT2 : T = 2 ^ (p + 1) - 1 := by omega
      have hS2 : S = p + 1 := by omega
      subst hT hS
      exact ih (fun k => m (k + 1)) hS2 hT2 k (by omega)

end MM

theorem exists_isValidMod_minModulus (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hLle : 2 ^ Nat.log 2 (p + 1) ≤ p + 1 := Nat.pow_log_le_self 2 (by omega)
  have hLp : Nat.log 2 (p + 1) ≤ p := by
    have := Nat.log_lt_self 2 (show p + 1 ≠ 0 by omega); omega
  have hN : minModulus (p + 1) = 2 ^ (p + 1) - 2 ^ Nat.log 2 (p + 1) := rfl
  generalize Nat.log 2 (p + 1) = L at *
  generalize minModulus (p + 1) = N at *
  have hpowL : 2 ^ L ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hLp
  have hpow : 2 ^ (p + 1) = 2 ^ p * 2 := pow_succ 2 p
  have hL1 := Nat.one_le_two_pow (n := L)
  have hp1 := Nat.one_le_two_pow (n := p)
  have hNb : N + 2 ^ L = 2 ^ p * 2 := by omega
  have hlt : ∀ k < p + 1, 2 ^ k - 1 < N := by
    intro k hk
    have : 2 ^ k ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  let f : ℕ → ZMod N := fun k => ((2 ^ k - 1 : ℕ) : ZMod N)
  have hinj : Set.InjOn f (range (p + 1)) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
    rw [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at this
    have h1 := Nat.one_le_two_pow (n := a)
    have h2 := Nat.one_le_two_pow (n := b)
    exact Nat.pow_right_injective le_rfl (show 2 ^ a = 2 ^ b by omega)
  refine ⟨(range (p + 1)).image f, by rw [card_image_of_injOn hinj, card_range], ?_⟩
  intro m hm hs
  rw [card_image_of_injOn hinj, card_range, sum_image hinj] at hm
  rw [sum_image hinj, sum_image hinj] at hs
  have hs' : ((∑ k ∈ range (p + 1), m (f k) * (2 ^ k - 1) : ℕ) : ZMod N)
      = ((∑ k ∈ range (p + 1), (2 ^ k - 1) : ℕ) : ZMod N) := by
    rw [Nat.cast_sum, Nat.cast_sum]
    simp only [Nat.cast_mul]
    exact hs
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hs'
  have geo : ∀ q, ∑ k ∈ range q, (2 ^ k - 1) + q + 1 = 2 ^ q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [sum_range_succ, pow_succ]
      have := Nat.one_le_two_pow (n := q)
      omega
  have hTE : ∑ k ∈ range (p + 1), m (f k) * (2 ^ k - 1) + ∑ k ∈ range (p + 1), m (f k)
      = ∑ k ∈ range (p + 1), m (f k) * 2 ^ k := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    obtain ⟨c, hc⟩ : ∃ c, 2 ^ k = c + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    rw [hc, Nat.add_sub_cancel]
    ring
  have hU := MM.uniq p (fun k => m (f k)) hm
  have hK := MM.key p (fun k => m (f k))
  rw [hm] at hTE
  have hgeo := geo (p + 1)
  generalize ∑ k ∈ range (p + 1), m (f k) * 2 ^ k = T at *
  generalize ∑ k ∈ range (p + 1), m (f k) * (2 ^ k - 1) = E at *
  generalize ∑ k ∈ range (p + 1), (2 ^ k - 1) = F at *
  have hmodT : T % N = (2 ^ (p + 1) - 1) % N := by
    have := Nat.ModEq.add_right (p + 1) hmod
    rw [← hTE, show 2 ^ (p + 1) - 1 = F + (p + 1) by omega]
    exact this
  have hr : (2 ^ (p + 1) - 1) % N = 2 ^ L - 1 := by
    rw [show 2 ^ (p + 1) - 1 = N + (2 ^ L - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
  rw [hr] at hmodT
  have hdm := Nat.div_add_mod T N
  rw [hmodT] at hdm
  obtain ⟨i, hi⟩ : ∃ i, T / N = i + 1 := by
    rcases h : T / N with _ | i
    · rw [h] at hdm; omega
    · exact ⟨i, rfl⟩
  rw [hi] at hdm
  have hprod : N * (i + 1) + 2 ^ L * i + 2 ^ L = 2 ^ p * (2 * i + 1) + 2 ^ p := by
    have : N * (i + 1) + 2 ^ L * i + 2 ^ L = (N + 2 ^ L) * (i + 1) := by ring
    rw [this, hNb]; ring
  have heq : T + 2 ^ L * i = 2 ^ p * (2 * i + 1) + (2 ^ p - 1) := by
    generalize N * (i + 1) = X at *
    generalize 2 ^ L * i = Y at *
    generalize 2 ^ p * (2 * i + 1) = Z at *
    omega
  have hleft : MM.g p (T + 2 ^ L * i) = 2 * i + 1 + p := by
    rw [heq, MM.g_split p _ _ (by omega), MM.g_full]
  have hshift : MM.g p (2 ^ L * i) ≤ i := by
    have := MM.g_shift (p - L) L i
    rw [Nat.sub_add_cancel hLp] at this
    rw [this]; exact MM.g_le _ _
  have hadd := MM.g_add p T (2 ^ L * i)
  have hi0 : i = 0 := by omega
  subst hi0
  have hT : T = 2 ^ (p + 1) - 1 := by
    simp only [Nat.mul_one, Nat.zero_add] at hdm
    omega
  have hU' := hU hT
  intro a ha
  rw [mem_image] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact hU' k (mem_range.1 hk)

end Arxiv.«2607.08366»

#print axioms Arxiv.«2607.08366».exists_isValidMod_minModulus
