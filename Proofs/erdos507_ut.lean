import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.FinCases

open Asymptotics Filter Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace EuclideanGeometry

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]

noncomputable def triangle_area (a b c : P) : ℝ :=
  positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2

lemma triangle_area_eq_det (a b c : ℝ²) :
    triangle_area a b c =
    Matrix.det !![a 0, b 0, c 0;
                  a 1, b 1, c 1;
                  1,   1,   1] / 2 := by
  rw [triangle_area, Orientation.areaForm_to_volumeForm,
    positiveOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl, Module.Basis.det_apply]
  suffices (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1) =
      a 0 * b 1 - a 0 * c 1 - b 0 * a 1 + b 0 * c 1 + c 0 * a 1 - c 0 * b 1 by
    simp [Matrix.det_fin_two, Matrix.det_fin_three, Module.Basis.toMatrix, this]
  ring

end EuclideanGeometry

namespace Erdos507

noncomputable def minTriangleArea (S : Finset ℝ²) : ℝ :=
  sInf {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
    (p : Fin 3 → ℝ²) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)}

noncomputable def α (n : ℕ) : ℝ :=
  sSup (minTriangleArea '' { S : Finset ℝ² |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) })

namespace UT

lemma area_eq (a b c : ℝ²) : EuclideanGeometry.triangle_area a b c =
    ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp
  ring

lemma sq_le (p : ℝ²) (h : ‖p‖ ≤ 1) : p 0 ^ 2 + p 1 ^ 2 ≤ 1 := by
  have := EuclideanSpace.norm_sq_eq p
  rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at this
  nlinarith [norm_nonneg p]

lemma c0 (p : ℝ²) (h : ‖p‖ ≤ 1) : -1 ≤ p 0 ∧ p 0 ≤ 1 := by
  have := sq_le p h
  constructor <;> nlinarith [sq_nonneg (p 1)]

lemma c1 (p : ℝ²) (h : ‖p‖ ≤ 1) : -1 ≤ p 1 ∧ p 1 ≤ 1 := by
  have := sq_le p h
  constructor <;> nlinarith [sq_nonneg (p 0)]

lemma close (x y : ℝ) (m : ℕ) (hm : 0 < m) (hx : -1 ≤ x) (hy : -1 ≤ y)
    (h : ⌊(x + 1) * m / 2⌋₊ = ⌊(y + 1) * m / 2⌋₊) : |x - y| ≤ 2 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : 0 ≤ (x + 1) * m / 2 := by
    have : 0 ≤ x + 1 := by linarith
    positivity
  have hy' : 0 ≤ (y + 1) * m / 2 := by
    have : 0 ≤ y + 1 := by linarith
    positivity
  have hu := Nat.floor_le hx'
  have hu2 := Nat.lt_floor_add_one ((x + 1) * m / 2)
  have hv := Nat.floor_le hy'
  have hv2 := Nat.lt_floor_add_one ((y + 1) * m / 2)
  rw [h] at hu hu2
  have e : x - y = ((x + 1) * m / 2 - (y + 1) * m / 2) * (2 / m) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / m)]
  apply mul_le_of_le_one_left (by positivity)
  rw [abs_le]
  constructor <;> linarith

lemma area_bd (a0 a1 b0 b1 c0 c1 w : ℝ) (hw : 0 ≤ w) (h1 : |a0 - c0| ≤ w) (h2 : |b0 - c0| ≤ w)
    (hb1 : |b1 - c1| ≤ 2) (ha1 : |a1 - c1| ≤ 2) :
    |((a0 - c0) * (b1 - c1) - (b0 - c0) * (a1 - c1)) / 2| ≤ 2 * w := by
  have e1 : |(a0 - c0) * (b1 - c1)| ≤ w * 2 := by
    rw [abs_mul]; exact mul_le_mul h1 hb1 (abs_nonneg _) hw
  have e2 : |(b0 - c0) * (a1 - c1)| ≤ w * 2 := by
    rw [abs_mul]; exact mul_le_mul h2 ha1 (abs_nonneg _) hw
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

lemma d2 (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) : |x - y| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma key (S : Finset ℝ²) (n : ℕ) (hn : 7 ≤ n) (hc : S.card = n) (hS : ∀ p ∈ S, ‖p‖ ≤ 1) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      |EuclideanGeometry.triangle_area a b c| ≤ 56 / n := by
  set m := (n - 3) / 2 with hmdef
  have hm : 2 ≤ m := by omega
  have hmn : n ≤ 14 * m := by omega
  have hmaps : ∀ p ∈ S, (fun p : ℝ² => ⌊(p 0 + 1) * m / 2⌋₊) p ∈ Finset.range (m + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hb := c0 p (hS p hp)
    have hm' : (0 : ℝ) ≤ m := by positivity
    rw [Nat.floor_lt (by have : 0 ≤ p 0 + 1 := by linarith
                         positivity)]
    push_cast
    nlinarith
  have hcard : (Finset.range (m + 1)).card * 2 < S.card := by
    rw [Finset.card_range, hc]; omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hy
  simp only [Finset.mem_filter] at ha hb hc'
  refine ⟨a, ha.1, b, hb.1, c, hc'.1, hab, hac, hbc, ?_⟩
  have ha0 := c0 a (hS a ha.1)
  have hb0 := c0 b (hS b hb.1)
  have hc0 := c0 c (hS c hc'.1)
  have ha1 := c1 a (hS a ha.1)
  have hb1 := c1 b (hS b hb.1)
  have hc1 := c1 c (hS c hc'.1)
  have w1 := close (a 0) (c 0) m (by omega) ha0.1 hc0.1 (ha.2.trans hc'.2.symm)
  have w2 := close (b 0) (c 0) m (by omega) hb0.1 hc0.1 (hb.2.trans hc'.2.symm)
  rw [area_eq]
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine (area_bd _ _ _ _ _ _ _ (by positivity) w1 w2 (d2 _ _ hb1 hc1) (d2 _ _ ha1 hc1)).trans ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmn' : (n : ℝ) ≤ 14 * m := by exact_mod_cast hmn
  rw [show 2 * (2 / (m : ℝ)) = 4 / m by ring, div_le_div_iff₀ hm' hn']
  linarith

lemma mta_le (S : Finset ℝ²) (n : ℕ) (hn : 7 ≤ n) (hc : S.card = n) (hS : ∀ p ∈ S, ‖p‖ ≤ 1) :
    minTriangleArea S ≤ 56 / n := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h⟩ := key S n hn hc hS
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨![a, b, c], ?_, ?_, rfl⟩) h
  · rintro x ⟨p, -, -, rfl⟩
    exact abs_nonneg _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i
    fin_cases i <;> simpa

end UT

theorem erdos_507.variants.upper_trivial :
    Asymptotics.IsBigO Filter.atTop (α : ℕ → ℝ) ((fun n ↦ 1 / (n : ℝ)) : ℕ → ℝ) := by
  refine Asymptotics.IsBigO.of_bound 56 ?_
  filter_upwards [Filter.eventually_ge_atTop 7] with n hn
  have h0 : 0 ≤ α n := Real.sSup_nonneg (by
    rintro _ ⟨S, -, rfl⟩
    exact Real.sInf_nonneg (by
      rintro _ ⟨p, -, -, rfl⟩
      exact abs_nonneg _))
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : α n ≤ 56 / n := Real.sSup_le (by
    rintro _ ⟨S, ⟨hc, hS, -⟩, rfl⟩
    exact UT.mta_le S n hn hc (fun p hp => mem_closedBall_zero_iff.mp (hS hp))) (by positivity)
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
  calc α n ≤ 56 / n := h1
    _ = 56 * (1 / n) := by ring

end Erdos507

#print axioms Erdos507.erdos_507.variants.upper_trivial
