import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
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

/-- Star5: Star graph with center 0 and 5 leaves. -/
abbrev Star5 : SimpleGraph (Fin 1 ⊕ Fin 5) := completeBipartiteGraph (Fin 1) (Fin 5)

instance : DecidableRel Star5.Adj := by unfold Star5 completeBipartiteGraph; infer_instance

lemma Star5_reindex :
    reindex (finSumFinEquiv : Fin 1 ⊕ Fin 5 ≃ Fin 6) finSumFinEquiv (Star5.adjMatrix ℝ) =
    !![0, 1, 1, 1, 1, 1;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, (0 : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma Star5_charmatrix :
    charmatrix (!![0, 1, 1, 1, 1, 1;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, (0 : ℝ)]) =
    !![X, -1, -1, -1, -1, -1;
       -1, X, 0, 0, 0, 0;
       -1, 0, X, 0, 0, 0;
       -1, 0, 0, X, 0, 0;
       -1, 0, 0, 0, X, 0;
       -1, 0, 0, 0, 0, (X : ℝ[X])] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma det6 (x : ℝ[X]) :
    (!![x, -1, -1, -1, -1, -1;
       -1, x, 0, 0, 0, 0;
       -1, 0, x, 0, 0, 0;
       -1, 0, 0, x, 0, 0;
       -1, 0, 0, 0, x, 0;
       -1, 0, 0, 0, 0, x] : Matrix (Fin 6) (Fin 6) ℝ[X]).det = x ^ 4 * (x ^ 2 - 5) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Matrix.det_unique, Fin.default_eq_zero, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ,
    mul_zero, zero_mul, add_zero, zero_add]
  ring

lemma Star5_charpoly : (Star5.adjMatrix ℝ).charpoly =
    X ^ 4 * ((X - C (Real.sqrt 5)) * (X - C (-Real.sqrt 5))) := by
  rw [← charpoly_reindex (finSumFinEquiv : Fin 1 ⊕ Fin 5 ≃ Fin 6), Star5_reindex,
    Matrix.charpoly, Star5_charmatrix, det6]
  have hs : (C (Real.sqrt 5) : ℝ[X]) ^ 2 = 5 := by
    rw [← map_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    exact map_ofNat C 5
  have hf : (X - C (Real.sqrt 5)) * (X - -C (Real.sqrt 5)) =
      (X ^ 2 - C (Real.sqrt 5) ^ 2 : ℝ[X]) := by ring
  rw [map_neg, hf, hs]

theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by
  unfold cvetkovic
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  rw [Star5_charpoly, roots_mul, roots_mul, roots_pow, roots_X,
    roots_X_sub_C, roots_X_sub_C]
  · simp only [Multiset.countP_add, Multiset.countP_nsmul, ← Multiset.cons_zero,
      Multiset.countP_cons, Multiset.countP_zero]
    simp [h5, h5.ne, h5.not_gt, h5.ne']
  all_goals
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', X_sub_C_ne_zero, X_ne_zero, false_and,
      or_self, not_false_eq_true]

#print axioms Star5_cvetkovic

end WrittenOnTheWallII.Test
