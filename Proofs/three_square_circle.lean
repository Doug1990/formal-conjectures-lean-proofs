import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open scoped NNReal

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

namespace SquarePacking

def Square (side : ℝ) : Set ℝ² :=
  {p : ℝ² | 0 < p 0 ∧ p 0 < side ∧ 0 < p 1 ∧ p 1 < side}

def UnitSquare : Set ℝ² := Square 1

def Circle (r : ℝ≥0) : Set ℝ² :=
  {p : ℝ² | p 0 ^ 2 + p 1 ^ 2 < (r : ℝ) ^ 2}

structure Packing (n : ℕ) (s : Set ℝ²) (S : Set ℝ²) where
  embeddings : Fin n → (ℝ² ≃ᵢ ℝ²)
  disjoint : Pairwise fun i j => Disjoint (embeddings i '' s) (embeddings j '' s)
  inside : ∀ i : Fin n, embeddings i '' s ⊆ S

/-- Translation vectors: two squares side by side below, one centred on top;
the circle centre is the origin. -/
noncomputable def shift : Fin 3 → ℝ² :=
  ![!₂[-1, -13/16], !₂[0, -13/16], !₂[-1/2, 3/16]]

lemma mem_img {v x : ℝ²} (hx : x ∈ (IsometryEquiv.addRight v) '' UnitSquare) :
    0 < x 0 - v 0 ∧ x 0 - v 0 < 1 ∧ 0 < x 1 - v 1 ∧ x 1 - v 1 < 1 := by
  obtain ⟨p, ⟨h1, h2, h3, h4⟩, rfl⟩ := hx
  have e : (IsometryEquiv.addRight v) p = p + v := rfl
  rw [e, PiLp.add_apply, PiLp.add_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma radius_sq : (((5 * NNReal.sqrt 17) / 16 : ℝ≥0) : ℝ) ^ 2 = 425 / 256 := by
  have h : ((NNReal.sqrt 17 : ℝ≥0) : ℝ) ^ 2 = 17 := by
    rw [← NNReal.coe_pow, NNReal.sq_sqrt]; norm_num
  rw [NNReal.coe_div, NNReal.coe_mul, div_pow, mul_pow, h]
  norm_num

theorem three_square_packing_in_circle_bound :
    Nonempty (Packing 3 UnitSquare (Circle ((5 * NNReal.sqrt 17) / 16))) := by
  refine ⟨⟨fun i => IsometryEquiv.addRight (shift i), ?_, ?_⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have a := mem_img hi
    have b := mem_img hj
    fin_cases i <;> fin_cases j <;> simp [shift] at a b hij <;> linarith
  · intro i x hx
    have a := mem_img hx
    show x 0 ^ 2 + x 1 ^ 2 < _
    rw [radius_sq]
    fin_cases i <;> simp [shift] at a <;> nlinarith
end SquarePacking

#print axioms SquarePacking.three_square_packing_in_circle_bound
