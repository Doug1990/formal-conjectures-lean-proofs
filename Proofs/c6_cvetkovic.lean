import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open SimpleGraph Polynomial Matrix

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Copied verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cvetkovic.lean -/
noncomputable def cvetkovic (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI A : Matrix α α ℝ := G.adjMatrix ℝ
  letI spectrum : Multiset ℝ := (Matrix.charpoly A).roots
  letI positive_count : ℕ := spectrum.countP (fun x => 0 < x)
  letI negative_count : ℕ := spectrum.countP (fun x => 0 > x)
  letI zero_count : ℕ := spectrum.countP (fun x => 0 = x)
  zero_count + min positive_count negative_count

end SimpleGraph

set_option maxHeartbeats 400000

namespace WrittenOnTheWallII.Test

abbrev C6 : SimpleGraph (Fin 6) := cycleGraph 6

lemma C6_charmatrix : charmatrix (C6.adjMatrix ℝ) =
    !![X, -1, 0, 0, 0, -1;
       -1, X, -1, 0, 0, 0;
       0, -1, X, -1, 0, 0;
       0, 0, -1, X, -1, 0;
       0, 0, 0, -1, X, -1;
       -1, 0, 0, 0, -1, (X : ℝ[X])] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true})

lemma det6 (x : ℝ[X]) :
    (!![x, -1, 0, 0, 0, -1;
       -1, x, -1, 0, 0, 0;
       0, -1, x, -1, 0, 0;
       0, 0, -1, x, -1, 0;
       0, 0, 0, -1, x, -1;
       -1, 0, 0, 0, -1, x] : Matrix (Fin 6) (Fin 6) ℝ[X]).det
      = (x - 2) * (x + 2) * (x - 1) ^ 2 * (x + 1) ^ 2 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Matrix.det_unique, Fin.default_eq_zero, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ,
    mul_zero, zero_mul, add_zero, zero_add]
  ring

lemma C6_charpoly : (C6.adjMatrix ℝ).charpoly =
    (X - C 2) * (X - C (-2)) * (X - C 1) ^ 2 * (X - C (-1)) ^ 2 := by
  rw [Matrix.charpoly, C6_charmatrix, det6]
  have h2 : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
  have h2' : (C (-2) : ℝ[X]) = -2 := by rw [map_neg, h2]
  have h1 : (C 1 : ℝ[X]) = 1 := map_one C
  have h1' : (C (-1) : ℝ[X]) = -1 := by rw [map_neg, map_one]
  rw [h2, h2', h1, h1']
  ring

theorem C6_cvetkovic : cvetkovic C6 = 3 := by
  unfold cvetkovic
  rw [C6_charpoly, roots_mul, roots_mul, roots_mul, roots_pow, roots_pow,
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  · simp only [Multiset.countP_add, Multiset.countP_nsmul, ← Multiset.cons_zero,
      Multiset.countP_cons, Multiset.countP_zero]
    norm_num
  all_goals
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', X_sub_C_ne_zero, false_and, or_self,
      not_false_eq_true]

#print axioms C6_cvetkovic

end WrittenOnTheWallII.Test
