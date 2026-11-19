import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

namespace OeisA108306

open Matrix

def invertSeqC (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (k + 2) => a * b^k

/-- The INVERT transform of the sequence c. -/
noncomputable def invertSeqD (a b : ℕ) (n : ℕ) : ℕ :=
  Nat.strongRecOn n
    (fun m ih =>
      if m = 0 then 1
      else ∑ i ∈ Finset.range m,
        if h : i < m then invertSeqC a b (m - i) * ih i h else 0)

/-- The general 2x2 matrix [(1,a); (1,b)]. -/
def genMatrix (a b : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => a
  | 1, 0 => 1
  | 1, 1 => b

lemma D_zero (a b : ℕ) : invertSeqD a b 0 = 1 := by
  rw [invertSeqD, Nat.strongRecOn, WellFounded.fix_eq]
  simp

lemma D_succ (a b m : ℕ) : invertSeqD a b (m + 1) =
    ∑ i ∈ Finset.range (m + 1), invertSeqC a b (m + 1 - i) * invertSeqD a b i := by
  rw [invertSeqD, Nat.strongRecOn, WellFounded.fix_eq]
  simp only [Nat.add_one_ne_zero, if_false]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dif_pos (Finset.mem_range.mp hi)]
  rfl

/-- The auxiliary sequence (upper right entry). -/
noncomputable def Y (a b : ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, a * b ^ (m - 1 - i) * invertSeqD a b i

lemma D_succ' (a b m : ℕ) : invertSeqD a b (m + 1) = invertSeqD a b m + Y a b m := by
  rw [D_succ, Finset.sum_range_succ, Nat.add_sub_cancel_left, Y, add_comm]
  congr 1
  · show 1 * invertSeqD a b m = _
    rw [one_mul]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    rw [show m + 1 - i = (m - 1 - i) + 2 by omega]
    rfl

lemma Y_succ (a b m : ℕ) : Y a b (m + 1) = a * invertSeqD a b m + b * Y a b m := by
  rw [Y, Finset.sum_range_succ, Y, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    rw [show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]
    ring

lemma key (a b n : ℕ) :
    (genMatrix a b ^ n) 0 0 = invertSeqD a b n ∧ (genMatrix a b ^ n) 0 1 = Y a b n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, D_zero]; rfl
    · rw [pow_zero, Y]; simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      ih.1, ih.2, D_succ', Y_succ]
    simp only [genMatrix]
    constructor <;> ring

theorem conjecture (a_val b_val n : ℕ) :
    invertSeqD a_val b_val n = (genMatrix a_val b_val ^ n) 0 0 :=
  (key a_val b_val n).1.symm

end OeisA108306

#print axioms OeisA108306.conjecture
