import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
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

set_option maxHeartbeats 100000

namespace WrittenOnTheWallII.Test

abbrev K4 : SimpleGraph (Fin 4) := completeGraph (Fin 4)

lemma K4_charmatrix : charmatrix (K4.adjMatrix ℝ) =
    !![X, -1, -1, -1; -1, X, -1, -1; -1, -1, X, -1; -1, -1, -1, (X : ℝ[X])] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma det4 (x : ℝ[X]) :
    (!![x, -1, -1, -1; -1, x, -1, -1; -1, -1, x, -1; -1, -1, -1, x] :
      Matrix (Fin 4) (Fin 4) ℝ[X]).det = (x - 3) * (x + 1) ^ 3 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Matrix.det_unique, Fin.default_eq_zero, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ]
  ring

lemma K4_charpoly :
    (K4.adjMatrix ℝ).charpoly = (X - C 3) * (X - C (-1)) ^ 3 := by
  rw [Matrix.charpoly, K4_charmatrix, det4]
  have h3 : (C 3 : ℝ[X]) = 3 := map_ofNat C 3
  have h1 : (C (-1) : ℝ[X]) = -1 := by rw [map_neg, map_one]
  rw [h3, h1]
  ring

theorem K4_cvetkovic : cvetkovic K4 = 1 := by
  unfold cvetkovic
  rw [K4_charpoly, roots_mul (mul_ne_zero (X_sub_C_ne_zero 3)
    (pow_ne_zero 3 (X_sub_C_ne_zero (-1)))), roots_pow, roots_X_sub_C, roots_X_sub_C]
  simp [Multiset.countP_nsmul]
  simp only [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero]
  norm_num

#print axioms K4_cvetkovic

end WrittenOnTheWallII.Test
