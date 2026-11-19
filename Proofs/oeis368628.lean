import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OeisA368628

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the fourth power of a power series with coefficient sequence $b$. -/
def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficients of $A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv4 b (n - 1)

theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      if Even n then conv2 (fun m => if m < n then a m else 0) (n - 1)
      else conv4 (fun m => if m < n then a m else 0) (n - 1) := by
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

lemma conv4_congr (b c : ℕ → ℕ) (N : ℕ) (h : ∀ m ≤ N, b m = c m) :
    conv4 b N = conv4 c N := by
  unfold conv4
  apply conv2_congr
  intro m hm
  apply conv2_congr
  intro i hi
  exact h i (by omega)

lemma a_zero : a 0 = 1 := by
  rw [a_eq, if_pos rfl]

lemma a_even (n : ℕ) (h1 : 1 ≤ n) (he : Even n) : a n = conv2 a (n - 1) := by
  rw [a_eq, if_neg (by omega), if_pos he]
  apply conv2_congr
  intro m hm
  rw [if_pos (by omega)]

lemma a_odd (n : ℕ) (ho : ¬ Even n) (h1 : 1 ≤ n) : a n = conv4 a (n - 1) := by
  rw [a_eq, if_neg (by omega), if_neg ho]
  apply conv4_congr
  intro m hm
  rw [if_pos (by omega)]

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

lemma even_zero (e : ℕ) (h1 : 1 ≤ e) (he : Even e) : (a e : ZMod 2) = 0 := by
  rw [a_even e h1 he, conv2_mod, if_neg]
  obtain ⟨r, hr⟩ := he
  rintro ⟨s, hs⟩
  omega

lemma a_odd_mod (m : ℕ) :
    (a (2 * m + 1) : ZMod 2) = if Even m then (a (m / 2) : ZMod 2) else 0 := by
  rw [a_odd (2 * m + 1) (by rintro ⟨r, hr⟩; omega) (by omega),
    show 2 * m + 1 - 1 = 2 * m by omega]
  unfold conv4
  rw [conv2_mod, if_pos ⟨m, by omega⟩, show 2 * m / 2 = m by omega, conv2_mod]

lemma s_succ (k : ℕ) : (4 ^ (k + 1) - 1) / 3 = 4 * ((4 ^ k - 1) / 3) + 1 := by
  have h3 : 4 ^ k % 3 = 1 := by
    simp [Nat.pow_mod]
  have h4 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ, mul_comm]
  have : 0 < 4 ^ k := Nat.pow_pos (by omega)
  rw [h4]
  omega

end P

theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [← ZMod.natCast_eq_one_iff_odd]
  have hne : ¬ ((0 : ZMod 2) = 1) := by decide
  obtain ⟨j, hj | hj | hj | hj⟩ : ∃ j, n = 4 * j ∨ n = 4 * j + 1 ∨ n = 4 * j + 2 ∨ n = 4 * j + 3 :=
    ⟨n / 4, by omega⟩
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [P.a_zero, Nat.cast_one]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    · rw [P.even_zero n hpos ⟨2 * j, by omega⟩]
      refine ⟨fun h => absurd h hne, ?_⟩
      rintro ⟨k, hk⟩
      rcases k with _ | k
      · rw [pow_zero] at hk
        omega
      · rw [P.s_succ] at hk
        omega
  · subst hj
    rw [show 4 * j + 1 = 2 * (2 * j) + 1 by omega, P.a_odd_mod, if_pos ⟨j, by omega⟩,
      show 2 * j / 2 = j by omega, ZMod.natCast_eq_one_iff_odd, ih j (by omega)]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [P.s_succ]
      omega
    · rintro ⟨k, hk⟩
      rcases k with _ | k
      · rw [pow_zero] at hk
        omega
      · rw [P.s_succ] at hk
        exact ⟨k, by omega⟩
  · rw [P.even_zero n (by omega) ⟨2 * j + 1, by omega⟩]
    refine ⟨fun h => absurd h hne, ?_⟩
    rintro ⟨k, hk⟩
    rcases k with _ | k
    · rw [pow_zero] at hk
      omega
    · rw [P.s_succ] at hk
      omega
  · subst hj
    rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by omega, P.a_odd_mod,
      if_neg (by rintro ⟨r, hr⟩; omega)]
    refine ⟨fun h => absurd h hne, ?_⟩
    rintro ⟨k, hk⟩
    rcases k with _ | k
    · rw [pow_zero] at hk
      omega
    · rw [P.s_succ] at hk
      omega

end OeisA368628

#print axioms OeisA368628.conjecture
