import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OeisA368626

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the cube of a power series with coefficient sequence $b$. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), conv2 b k * b (n - k)

/-- Coefficients of $A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^3+A(-x)^3)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1)
      else conv3 b (n - 1)

theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      if Even n then conv2 (fun m => if m < n then a m else 0) (n - 1)
      else conv3 (fun m => if m < n then a m else 0) (n - 1) := by
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

lemma conv3_congr (b c : ℕ → ℕ) (N : ℕ) (h : ∀ m ≤ N, b m = c m) :
    conv3 b N = conv3 c N := by
  unfold conv3
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [conv2_congr b c k (fun m hm => h m (by omega)), h (N - k) (by omega)]

lemma a_zero : a 0 = 1 := by
  rw [a_eq, if_pos rfl]

lemma a_even (n : ℕ) (h1 : 1 ≤ n) (he : Even n) : a n = conv2 a (n - 1) := by
  rw [a_eq, if_neg (by omega), if_pos he]
  apply conv2_congr
  intro m hm
  rw [if_pos (by omega)]

lemma a_odd (n : ℕ) (ho : ¬ Even n) (h1 : 1 ≤ n) : a n = conv3 a (n - 1) := by
  rw [a_eq, if_neg (by omega), if_neg ho]
  apply conv3_congr
  intro m hm
  rw [if_pos (by omega)]

lemma conv2_mod (N : ℕ) :
    ((conv2 a N : ℕ) : ZMod 2) = if Even N then (a (N / 2) : ZMod 2) else 0 := by
  simp only [conv2, Nat.cast_sum, Nat.cast_mul]
  rw [sym_sum N (fun k => (a k : ZMod 2) * a (N - k)) ?_]
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

lemma even_zero (e : ℕ) (h1 : 1 ≤ e) (he : Even e) : (a e : ZMod 2) = 0 := by
  rw [a_even e h1 he, conv2_mod, if_neg]
  obtain ⟨r, hr⟩ := he
  rintro ⟨s, hs⟩
  omega

lemma a_odd_mod (m : ℕ) : (a (2 * m + 1) : ZMod 2) = a m := by
  rw [a_odd (2 * m + 1) (by rintro ⟨r, hr⟩; omega) (by omega)]
  simp only [conv3, Nat.cast_sum, Nat.cast_mul, conv2_mod]
  rw [show 2 * m + 1 - 1 = 2 * m by omega]
  rw [Finset.sum_eq_single (2 * m)]
  · rw [if_pos ⟨m, by omega⟩, Nat.sub_self, a_zero, Nat.cast_one, mul_one,
      show 2 * m / 2 = m by omega]
  · intro k hk hne
    rw [Finset.mem_range] at hk
    split_ifs with hke
    · obtain ⟨r, hr⟩ := hke
      rw [even_zero (2 * m - k) (by omega) ⟨m - r, by omega⟩, mul_zero]
    · rw [zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end P

theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [← ZMod.natCast_eq_one_iff_odd]
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨m, hm⟩
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [P.a_zero, Nat.cast_one]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    · rw [P.even_zero n hpos ⟨r, hr⟩]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro ⟨k, hk⟩
        rcases k with _ | j
        · rw [pow_zero] at hk
          omega
        · have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
          have := Nat.two_pow_pos j
          omega
  · subst hm
    rw [P.a_odd_mod, ZMod.natCast_eq_one_iff_odd, ih m (by omega)]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
      have := Nat.two_pow_pos k
      omega
    · rintro ⟨k, hk⟩
      rcases k with _ | j
      · rw [pow_zero] at hk
        omega
      · refine ⟨j, ?_⟩
        have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
        have := Nat.two_pow_pos j
        omega

end OeisA368626

#print axioms OeisA368626.conjecture
