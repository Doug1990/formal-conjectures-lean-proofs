import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OeisA368633

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of $A(x)=1+2xA(x)^2-xA(-x)^2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 3 else 1) * conv2 b (n - 1)

theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      (if Even n then 3 else 1) * conv2 (fun m => if m < n then a m else 0) (n - 1) := by
  rw [a, Nat.strongRec_eq]
  simp only [a, dite_eq_ite]

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

lemma conv2_congr (b c : ℕ → ℕ) (N : ℕ) (h : ∀ m ≤ N, b m = c m) :
    conv2 b N = conv2 c N := by
  unfold conv2
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [h k (by omega), h (N - k) (by omega)]

lemma a_zero : a 0 = 1 := by
  rw [a_eq, if_pos rfl]

lemma three : ((3 : ℕ) : ZMod 2) = 1 := by decide

lemma a_mod (n : ℕ) (h1 : 1 ≤ n) : (a n : ZMod 2) = (conv2 a (n - 1) : ZMod 2) := by
  have hc : conv2 (fun m => if m < n then a m else 0) (n - 1) = conv2 a (n - 1) := by
    apply conv2_congr
    intro m hm
    rw [if_pos (by omega)]
  rw [a_eq, if_neg (by omega), hc, Nat.cast_mul]
  split_ifs
  · rw [three, one_mul]
  · rw [Nat.cast_one, one_mul]

lemma conv2_mod (f : ℕ → ℕ) (N : ℕ) :
    ((conv2 f N : ℕ) : ZMod 2) = if Even N then (f (N / 2) : ZMod 2) else 0 := by
  simp only [conv2, Nat.cast_sum, Nat.cast_mul]
  rw [sym_sum N (fun k => (f k : ZMod 2) * f (N - k)) ?_]
  · try dsimp only
    split_ifs with he
    · obtain ⟨r, hr⟩ := he
      have : N - N / 2 = N / 2 := by omega
      rw [this]
      exact sq2 _
    · rfl
  · intro k hk
    try dsimp only
    rw [show N - (N - k) = k by omega, mul_comm]

lemma even_zero (j : ℕ) : (a (2 * j + 2) : ZMod 2) = 0 := by
  rw [a_mod (2 * j + 2) (by omega), show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    conv2_mod, if_neg]
  rintro ⟨s, hs⟩
  omega

lemma a_odd_mod (m : ℕ) : (a (2 * m + 1) : ZMod 2) = (a m : ZMod 2) := by
  rw [a_mod (2 * m + 1) (by omega),
    show 2 * m + 1 - 1 = 2 * m by omega, conv2_mod, if_pos ⟨m, by omega⟩,
    show 2 * m / 2 = m by omega]

lemma pow_succ2 (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]

end P

theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [← ZMod.natCast_eq_one_iff_odd]
  have hne : ¬ ((0 : ZMod 2) = 1) := by decide
  obtain ⟨j, hj | hj | hj⟩ : ∃ j, n = 0 ∨ n = 2 * j + 2 ∨ n = 2 * j + 1 :=
    ⟨if n % 2 = 0 then n / 2 - 1 else n / 2, by split_ifs <;> omega⟩
  · subst hj
    rw [P.a_zero, Nat.cast_one]
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
  · subst hj
    rw [P.even_zero j]
    refine ⟨fun h => absurd h hne, ?_⟩
    rintro ⟨k, hk⟩
    rcases k with _ | k
    · rw [pow_zero] at hk
      omega
    · rw [P.pow_succ2] at hk
      omega
  · subst hj
    rw [P.a_odd_mod, ZMod.natCast_eq_one_iff_odd, ih j (by omega)]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [P.pow_succ2]
      omega
    · rintro ⟨k, hk⟩
      rcases k with _ | k
      · rw [pow_zero] at hk
        omega
      · rw [P.pow_succ2] at hk
        exact ⟨k, by omega⟩

end OeisA368633

#print axioms OeisA368633.conjecture_1
