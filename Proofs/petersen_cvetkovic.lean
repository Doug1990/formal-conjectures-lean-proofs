import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open SimpleGraph Polynomial Matrix

namespace SimpleGraph

/-- Copied verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean -/
abbrev PetersenVertex : Type := {s : Finset (Fin 5) // s.card = 2}

def petersenGraph : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have hc := s.2
    rw [disjoint_self.mp h] at hc
    simp at hc⟩

instance : DecidableRel petersenGraph.Adj := fun s t =>
  inferInstanceAs (Decidable (Disjoint s.1 t.1))

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

abbrev PetersenGraph : SimpleGraph PetersenVertex := petersenGraph

/-- Outer 5-cycle `j ↦ {2j, 2j+1}`, inner pentagram `j ↦ {2j+2, 2j+4}`. -/
def pf : Fin 5 ⊕ Fin 5 → PetersenVertex :=
  Sum.elim
    ![⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩, ⟨{4, 0}, by decide⟩, ⟨{1, 2}, by decide⟩,
      ⟨{3, 4}, by decide⟩]
    ![⟨{2, 4}, by decide⟩, ⟨{4, 1}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{3, 0}, by decide⟩,
      ⟨{0, 2}, by decide⟩]

lemma pf_bij : Function.Bijective pf := by decide

noncomputable def pe : Fin 5 ⊕ Fin 5 ≃ PetersenVertex := Equiv.ofBijective pf pf_bij

/-- Block adjacency: cycle outside, pentagram inside, perfect matching between. -/
def T : Fin 5 ⊕ Fin 5 → Fin 5 ⊕ Fin 5 → Bool
  | .inl a, .inl b => decide (b = a + 1 ∨ a = b + 1)
  | .inr a, .inr b => decide (b = a + 2 ∨ a = b + 2)
  | .inl a, .inr b => decide (a = b)
  | .inr a, .inl b => decide (a = b)

lemma pf_adj (i j : Fin 5 ⊕ Fin 5) : PetersenGraph.Adj (pf i) (pf j) ↔ T i j = true := by
  revert i j; decide

noncomputable def M : Matrix (Fin 5) (Fin 5) ℝ[X] :=
  !![X, -1, 0, 0, -1;
     -1, X, -1, 0, 0;
     0, -1, X, -1, 0;
     0, 0, -1, X, -1;
     -1, 0, 0, -1, X]

noncomputable def N : Matrix (Fin 5) (Fin 5) ℝ[X] :=
  !![X, 0, -1, -1, 0;
     0, X, 0, -1, -1;
     -1, 0, X, 0, -1;
     -1, -1, 0, X, 0;
     0, -1, -1, 0, X]

lemma hchar : charmatrix (reindex pe.symm pe.symm (PetersenGraph.adjMatrix ℝ)) =
    fromBlocks M (-1) (-1) N := by
  ext i j
  simp only [charmatrix_apply, reindex_apply, submatrix_apply, Equiv.symm_symm, pe,
    Equiv.ofBijective_apply, adjMatrix_apply, pf_adj]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [M, N]

lemma block_det {R : Type*} [CommRing R] [NoZeroDivisors R] (A B : Matrix (Fin 5) (Fin 5) R) :
    (fromBlocks A (-1) (-1) B).det = (1 - A * B).det ∨
      (fromBlocks A (-1) (-1) B).det = -(1 - A * B).det := by
  let S : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) R := fromBlocks 0 (-1) (-1) 0
  have hS1 : S * fromBlocks A (-1) (-1) B = fromBlocks 1 (-B) (-A) 1 := by
    simp [S, fromBlocks_multiply]
  have hSS : S * S = 1 := by
    simp [S, fromBlocks_multiply]
  have detS : S.det = 1 ∨ S.det = -1 := by
    apply mul_self_eq_one_iff.mp
    rw [← det_mul, hSS, det_one]
  have key : S.det * (fromBlocks A (-1) (-1) B).det = (1 - A * B).det := by
    rw [← det_mul, hS1, det_fromBlocks_one₁₁, neg_mul_neg]
  rcases detS with h | h
  · left; rw [h, one_mul] at key; exact key
  · right; rw [h, neg_one_mul] at key; rw [← key, neg_neg]

def W (d a : ℝ[X]) : Matrix (Fin 5) (Fin 5) ℝ[X] :=
  !![d, a, a, a, a;
     a, d, a, a, a;
     a, a, d, a, a;
     a, a, a, d, a;
     a, a, a, a, d]

lemma hMN : 1 - M * N = W (1 - X ^ 2) (X - 1) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [M, N, W, Matrix.mul_apply, Fin.sum_univ_five, Matrix.one_apply] <;> ring

lemma det_W (d a : ℝ[X]) : (W d a).det = (d - a) ^ 4 * (d + 4 * a) := by
  simp only [W, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Matrix.det_unique, Fin.default_eq_zero, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ]
  ring

lemma petersen_roots : (Matrix.charpoly (PetersenGraph.adjMatrix ℝ)).roots =
    ((X - C 3) * (X - C 1) ^ 5 * (X - C (-2)) ^ 4 : ℝ[X]).roots := by
  rw [← charpoly_reindex pe.symm, Matrix.charpoly, hchar]
  have h3 : (C 3 : ℝ[X]) = 3 := map_ofNat C 3
  have h1 : (C 1 : ℝ[X]) = 1 := map_one C
  have h2 : (C (-2) : ℝ[X]) = -2 := by rw [map_neg, map_ofNat C 2]
  have hP : (1 - X ^ 2 - (X - 1)) ^ 4 * (1 - X ^ 2 + 4 * (X - 1)) =
      -((X - C 3) * (X - C 1) ^ 5 * (X - C (-2)) ^ 4 : ℝ[X]) := by
    rw [h3, h1, h2]; ring
  rcases block_det M N with h | h
  · rw [h, hMN, det_W, hP, roots_neg]
  · rw [h, hMN, det_W, hP, neg_neg]

theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by
  unfold cvetkovic
  rw [petersen_roots, roots_mul, roots_mul, roots_pow, roots_pow,
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  · simp only [Multiset.countP_add, Multiset.countP_nsmul, ← Multiset.cons_zero,
      Multiset.countP_cons, Multiset.countP_zero]
    norm_num
  all_goals
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', X_sub_C_ne_zero, false_and, or_self,
      not_false_eq_true]

#print axioms petersen_cvetkovic

end WrittenOnTheWallII.Test
