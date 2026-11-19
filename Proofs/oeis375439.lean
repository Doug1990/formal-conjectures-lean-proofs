import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Group.Nat.Even

namespace OeisA375439

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the cube of a power series with coefficient sequence $b$. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), conv2 b k * b (n - k)

/-- Coefficients obtained by substituting $x^3$ for $x$. -/
def subst3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 3 ∣ n then b (n / 3) else 0

/-- Coefficients of $2B(x)^3+B(x^3)$. -/
def rhs (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * conv3 b n + subst3 b n

/-- Coefficients of $A(x)=x+x^2+(2A(x)^3+A(x^3))/3$, with $a(0)=0$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 0
    else if n = 1 then 1
    else if n = 2 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      rhs b n / 3

/-- The coefficient recurrence unfolded at an index. -/
theorem a_eq (n : ℕ) :
    a n = if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 1
      else rhs (fun m => if m < n then a m else 0) n / 3 := by
  rw [a, Nat.strongRec_eq]
  simp only [a, dite_eq_ite]

namespace P

open Polynomial

noncomputable def F (b : ℕ → ℕ) (N : ℕ) : (ZMod 3)[X] :=
  ∑ i ∈ Finset.range (N + 1), monomial i ((b i : ℕ) : ZMod 3)

lemma coeff_F (b : ℕ → ℕ) (N i : ℕ) (hi : i ≤ N) : (F b N).coeff i = (b i : ZMod 3) := by
  unfold F
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    simp only [Finset.mem_range] at h
    omega

lemma conv2_eq (b : ℕ → ℕ) (N k : ℕ) (hk : k ≤ N) :
    ((conv2 b k : ℕ) : ZMod 3) = (F b N * F b N).coeff k := by
  rw [coeff_mul]
  refine Eq.trans ?_ (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (F b N).coeff i * (F b N).coeff j) k).symm
  unfold conv2
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  show _ = (F b N).coeff i * (F b N).coeff (k - i)
  rw [coeff_F b N i (by omega), coeff_F b N (k - i) (by omega)]

lemma conv3_eq (b : ℕ → ℕ) (N : ℕ) :
    ((conv3 b N : ℕ) : ZMod 3) = (F b N ^ 3).coeff N := by
  rw [pow_three', coeff_mul]
  refine Eq.trans ?_ (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (F b N * F b N).coeff i * (F b N).coeff j) N).symm
  unfold conv3
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  show _ = (F b N * F b N).coeff i * (F b N).coeff (N - i)
  rw [conv2_eq b N i (by omega), coeff_F b N (N - i) (by omega)]

lemma conv3_mod (b : ℕ → ℕ) (N : ℕ) :
    ((conv3 b N : ℕ) : ZMod 3) = ((subst3 b N : ℕ) : ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [conv3_eq, ← ZMod.expand_card, coeff_expand (by decide)]
  unfold subst3
  split_ifs with h
  · rw [coeff_F b N (N / 3) (Nat.div_le_self _ _)]
  · simp

lemma z3 : ∀ x : ZMod 3, 2 * x + x = 0 := by decide

lemma dvd_rhs (b : ℕ → ℕ) (N : ℕ) : 3 ∣ rhs b N := by
  have h : ((rhs b N : ℕ) : ZMod 3) = 0 := by
    unfold rhs
    push_cast
    rw [conv3_mod]
    exact z3 _
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_zero] at this
  exact Nat.dvd_of_mod_eq_zero this

lemma a_mod (n : ℕ) (hn : 3 ≤ n) :
    a n % 2 = (if 3 ∣ n then a (n / 3) else 0) % 2 := by
  have e := a_eq n
  rw [if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega),
    if_neg (show ¬ n = 2 by omega)] at e
  obtain ⟨q, hq⟩ := dvd_rhs (fun m => if m < n then a m else 0) n
  have hsub : subst3 (fun m => if m < n then a m else 0) n
      = if 3 ∣ n then a (n / 3) else 0 := by
    unfold subst3
    split_ifs with h
    · show (if n / 3 < n then a (n / 3) else 0) = a (n / 3)
      rw [if_pos (by omega)]
    · rfl
  rw [e, hq, Nat.mul_div_cancel_left q (by decide), ← hsub]
  unfold rhs at hq
  omega

lemma P_iff (n : ℕ) (hn : 3 ≤ n) :
    (∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
      3 ∣ n ∧ ∃ k : ℕ, n / 3 = 3 ^ k ∨ n / 3 = 2 * 3 ^ k := by
  constructor
  · rintro ⟨k, h | h⟩
    · cases k with
      | zero => rw [pow_zero] at h; omega
      | succ k =>
        rw [pow_succ] at h
        refine ⟨?_, k, Or.inl ?_⟩
        · generalize 3 ^ k = x at h
          omega
        · generalize 3 ^ k = x at h ⊢
          omega
    · cases k with
      | zero => rw [pow_zero] at h; omega
      | succ k =>
        rw [pow_succ] at h
        refine ⟨?_, k, Or.inr ?_⟩
        · generalize 3 ^ k = x at h
          omega
        · generalize 3 ^ k = x at h ⊢
          omega
  · rintro ⟨hd, k, h | h⟩
    · refine ⟨k + 1, Or.inl ?_⟩
      rw [pow_succ]
      generalize 3 ^ k = x at h ⊢
      omega
    · refine ⟨k + 1, Or.inr ?_⟩
      rw [pow_succ]
      generalize 3 ^ k = x at h ⊢
      omega

end P

theorem a_1 : a 1 = 1 := by
  rw [a_eq]
  simp

theorem a_2 : a 2 = 1 := by
  rw [a_eq]
  simp

theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
  · subst h
    rw [a_1]
    exact ⟨fun _ => ⟨0, Or.inl rfl⟩, fun _ => odd_one⟩
  · subst h
    rw [a_2]
    exact ⟨fun _ => ⟨0, Or.inr rfl⟩, fun _ => odd_one⟩
  · rw [P.P_iff n h, Nat.odd_iff, P.a_mod n h]
    by_cases hd : 3 ∣ n
    · rw [if_pos hd, ← Nat.odd_iff, ih (n / 3) (by omega) (by omega)]
      exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩
    · rw [if_neg hd]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 hd⟩

end OeisA375439

#print axioms OeisA375439.conjecture
