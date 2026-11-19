import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.ComputeDegree
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

/-- House Graph: Square 0-1-2-3-0 with roof 4 connected to 2,3. -/
abbrev HouseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 0),
    s(2, 4), s(3, 4)
  }

lemma house_charmatrix : charmatrix (HouseGraph.adjMatrix ℝ) =
    !![X, -1, 0, -1, 0;
       -1, X, -1, 0, 0;
       0, -1, X, -1, -1;
       -1, 0, -1, X, -1;
       0, 0, -1, -1, (X : ℝ[X])] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true})

lemma det5 (x : ℝ[X]) :
    (!![x, -1, 0, -1, 0;
       -1, x, -1, 0, 0;
       0, -1, x, -1, -1;
       -1, 0, -1, x, -1;
       0, 0, -1, -1, x] : Matrix (Fin 5) (Fin 5) ℝ[X]).det
      = x * (x + 2) * (x ^ 3 - 2 * x ^ 2 - 2 * x + 2) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Matrix.det_unique, Fin.default_eq_zero, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Fin.val_zero, Fin.val_succ,
    mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- The cubic factor. -/
noncomputable abbrev q : ℝ[X] := X ^ 3 - C 2 * X ^ 2 - C 2 * X + C 2

lemma house_charpoly : (HouseGraph.adjMatrix ℝ).charpoly = X * (X - C (-2)) * q := by
  rw [Matrix.charpoly, house_charmatrix, det5]
  have h2 : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
  have h2' : (C (-2) : ℝ[X]) = -2 := by rw [map_neg, h2]
  rw [q, h2, h2']
  ring

lemma q_eval (x : ℝ) : q.eval x = x ^ 3 - 2 * x ^ 2 - 2 * x + 2 := by
  simp [q]

lemma q_ne_zero : q ≠ 0 := by
  intro h
  have := q_eval 0
  rw [h] at this
  norm_num at this

lemma q_natDegree : q.natDegree ≤ 3 := by
  unfold q
  compute_degree

lemma exists_root {a b : ℝ} (hab : a ≤ b) (h : q.eval a < 0 ∧ 0 < q.eval b ∨
    0 < q.eval a ∧ q.eval b < 0) : ∃ r ∈ Set.Ioo a b, q.eval r = 0 := by
  have hc : ContinuousOn (fun x => q.eval x) (Set.Icc a b) := q.continuous.continuousOn
  rcases h with h | h
  · exact intermediate_value_Ioo hab hc ⟨h.1, h.2⟩
  · exact intermediate_value_Ioo' hab hc ⟨h.2, h.1⟩

lemma q_roots : ∃ r₁ r₂ r₃ : ℝ, r₁ < 0 ∧ 0 < r₂ ∧ 0 < r₃ ∧
    q.roots = r₁ ::ₘ r₂ ::ₘ {r₃} := by
  obtain ⟨r₁, ⟨h1a, h1b⟩, h1⟩ := exists_root (a := -2) (b := -1) (by norm_num)
    (Or.inl (by rw [q_eval, q_eval]; norm_num))
  obtain ⟨r₂, ⟨h2a, h2b⟩, h2⟩ := exists_root (a := 0) (b := 1) (by norm_num)
    (Or.inr (by rw [q_eval, q_eval]; norm_num))
  obtain ⟨r₃, ⟨h3a, h3b⟩, h3⟩ := exists_root (a := 1) (b := 3) (by norm_num)
    (Or.inl (by rw [q_eval, q_eval]; norm_num))
  refine ⟨r₁, r₂, r₃, by linarith, h2a, by linarith, ?_⟩
  have hnd : (r₁ ::ₘ r₂ ::ₘ {r₃} : Multiset ℝ).Nodup := by
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, and_true]
    refine ⟨?_, ?_⟩
    · rintro (h | h) <;> linarith
    · intro h; linarith
  have hle : (r₁ ::ₘ r₂ ::ₘ {r₃} : Multiset ℝ) ≤ q.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
    rw [mem_roots q_ne_zero, IsRoot.def]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : Multiset.card q.roots ≤ Multiset.card (r₁ ::ₘ r₂ ::ₘ {r₃} : Multiset ℝ) := by
    have := (card_roots' q).trans q_natDegree
    simpa using this
  exact (Multiset.eq_of_le_of_card_le hle hcard).symm

theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by
  obtain ⟨r₁, r₂, r₃, h1, h2, h3, hq⟩ := q_roots
  unfold cvetkovic
  rw [house_charpoly, roots_mul (mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _))
    q_ne_zero), roots_mul (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)), roots_X,
    roots_X_sub_C, hq]
  have n1 : ¬ (0 : ℝ) < r₁ := not_lt.mpr h1.le
  have n2 : ¬ r₂ < 0 := not_lt.mpr h2.le
  have n3 : ¬ r₃ < 0 := not_lt.mpr h3.le
  have z1 : (0 : ℝ) ≠ r₁ := h1.ne'
  have z2 : (0 : ℝ) ≠ r₂ := h2.ne
  have z3 : (0 : ℝ) ≠ r₃ := h3.ne
  simp only [Multiset.countP_add, ← Multiset.cons_zero, Multiset.countP_cons,
    Multiset.countP_zero, gt_iff_lt, h1, h2, h3, n1, n2, n3, z1, z2, z3]
  norm_num

#print axioms house_cvetkovic

end WrittenOnTheWallII.Test
