import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Restated from FormalConjecturesForMathlib/Geometry/2d.lean. -/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- Restated from FormalConjecturesForMathlib/Geometry/2d.lean. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- Restated from FormalConjecturesForMathlib/Geometry/2d.lean. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]

/-- Restated from FormalConjecturesForMathlib/Geometry/2d.lean. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (∡ (p i) (p j) (p k)).sign = 1

end EuclideanGeometry

open Affine EuclideanGeometry

namespace Erdos189

/-- Erdős problem 189 asked whether the below holds for all rectangles. -/
def Erdos189For (P : ℝ² → ℝ² → ℝ² → ℝ² → Prop) (A : ℝ² → ℝ² → ℝ² → ℝ² → ℝ) :=
    ∀ᵉ (n > 0) (colouring : ℝ² → Fin n), ∃ colour, ∀ area > (0 : ℝ), ∃ a b c d,
      {a, b, c, d} ⊆ colouring⁻¹' {colour} ∧
      IsCcwConvexPolygon ![a, b, c, d] ∧
      A a b c d = area ∧
      P a b c d

namespace QC

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

lemma ortho_iff (a b c d : ℝ²) :
    line[ℝ, a, b].direction ⟂ line[ℝ, c, d].direction ↔
      (a 0 - b 0) * (c 0 - d 0) + (a 1 - b 1) * (c 1 - d 1) = 0 := by
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair,
    Submodule.isOrtho_span]
  simp only [Set.mem_singleton_iff, forall_eq]
  simp only [vsub_eq_sub, PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply,
    RCLike.inner_apply, conj_trivial]
  constructor <;> intro h <;> linarith

/-- three right angles in the plane (non-degenerate) force a parallelogram -/
lemma key (u0 u1 w0 w1 e0 e1 : ℝ) (hw : w0 ^ 2 + w1 ^ 2 ≠ 0)
    (he : e0 ^ 2 + e1 ^ 2 ≠ 0) (h1 : u0 * w0 + u1 * w1 = 0) (h2 : w0 * e0 + w1 * e1 = 0)
    (h3 : e0 * (u0 - w0 - e0) + e1 * (u1 - w1 - e1) = 0) : e0 = u0 ∧ e1 = u1 := by
  have hX : (u0 * e1 - u1 * e0) * (w0 ^ 2 + w1 ^ 2) = 0 := by
    linear_combination (e1 * w0 - e0 * w1) * h1 + (u0 * w1 - u1 * w0) * h2
  have hX0 : u0 * e1 - u1 * e0 = 0 := by
    rcases mul_eq_zero.1 hX with h | h
    · exact h
    · exact absurd h hw
  have hdot : e0 * u0 + e1 * u1 = e0 ^ 2 + e1 ^ 2 := by linear_combination h3 + h2
  have hlag : (e0 * u0 + e1 * u1) ^ 2 + (u0 * e1 - u1 * e0) ^ 2
      = (e0 ^ 2 + e1 ^ 2) * (u0 ^ 2 + u1 ^ 2) := by ring
  rw [hX0, hdot] at hlag
  have hn : (e0 ^ 2 + e1 ^ 2) * ((u0 ^ 2 + u1 ^ 2) - (e0 ^ 2 + e1 ^ 2)) = 0 := by
    linear_combination -hlag
  have hn' : u0 ^ 2 + u1 ^ 2 = e0 ^ 2 + e1 ^ 2 := by
    rcases mul_eq_zero.1 hn with h | h
    · exact absurd h he
    · linarith
  have hs : (u0 - e0) ^ 2 + (u1 - e1) ^ 2 = 0 := by linear_combination hn' - 2 * hdot
  have ha : (u0 - e0) ^ 2 = 0 := by nlinarith [sq_nonneg (u0 - e0), sq_nonneg (u1 - e1)]
  have hb : (u1 - e1) ^ 2 = 0 := by nlinarith [sq_nonneg (u0 - e0), sq_nonneg (u1 - e1)]
  constructor
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ha; linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hb; linarith

/-- real part of x², x viewed as a complex number -/
noncomputable def q0 (x : ℝ²) : ℝ := x 0 ^ 2 - x 1 ^ 2

/-- imaginary part of x², x viewed as a complex number -/
noncomputable def q1 (x : ℝ²) : ℝ := 2 * (x 0 * x 1)

/-- the colouring: (⌊Re x²⌋ mod 8, ⌊Im x²⌋ mod 8) -/
noncomputable def col (x : ℝ²) : Fin 64 :=
  ⟨(⌊q0 x⌋ % 8 * 8 + ⌊q1 x⌋ % 8).toNat, by omega⟩

lemma col_eq {x y : ℝ²} (h : col x = col y) :
    ⌊q0 x⌋ % 8 = ⌊q0 y⌋ % 8 ∧ ⌊q1 x⌋ % 8 = ⌊q1 y⌋ % 8 := by
  have := congrArg Fin.val h
  simp only [col] at this
  omega

lemma close (ta tb tc td : ℝ) (h1 : ⌊ta⌋ % 8 = ⌊tb⌋ % 8) (h2 : ⌊tc⌋ % 8 = ⌊tb⌋ % 8)
    (h3 : ⌊td⌋ % 8 = ⌊tb⌋ % 8) :
    (ta + tc - tb - td) ^ 2 < 4 ∨ 36 < (ta + tc - tb - td) ^ 2 := by
  set j : ℤ := (⌊ta⌋ + ⌊tc⌋ - ⌊tb⌋ - ⌊td⌋) / 8 with hj
  have hj8 : ⌊ta⌋ + ⌊tc⌋ - ⌊tb⌋ - ⌊td⌋ = 8 * j := by omega
  have hj8' : (⌊ta⌋ : ℝ) + ⌊tc⌋ - ⌊tb⌋ - ⌊td⌋ = 8 * (j : ℝ) := by exact_mod_cast hj8
  have a1 := Int.floor_le ta
  have a2 := Int.lt_floor_add_one ta
  have b1 := Int.floor_le tb
  have b2 := Int.lt_floor_add_one tb
  have c1 := Int.floor_le tc
  have c2 := Int.lt_floor_add_one tc
  have d1 := Int.floor_le td
  have d2 := Int.lt_floor_add_one td
  have lo : 8 * (j : ℝ) - 2 < ta + tc - tb - td := by linarith
  have hi : ta + tc - tb - td < 8 * (j : ℝ) + 2 := by linarith
  rcases lt_trichotomy j 0 with h | h | h
  · right
    have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    nlinarith
  · left
    rw [h] at lo hi
    simp only [Int.cast_zero, mul_zero] at lo hi
    nlinarith
  · right
    have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    nlinarith

end QC

open QC in
/-- Solved by Kovač (2023): a finite colouring of the plane in which no colour class contains
the vertices of rectangles of every area. -/
theorem erdos_189 :
    ¬ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction)
      (fun a b c d ↦ dist a b * dist b c) := by
  intro h
  obtain ⟨k, hk⟩ := h 64 (by norm_num) col
  obtain ⟨a, b, c, d, hsub, hccw, harea, h1, h2, h3⟩ := hk 2 (by norm_num)
  simp only at harea
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_preimage,
    Set.mem_singleton_iff] at hsub
  obtain ⟨ha, hb, hc, hd⟩ := hsub
  have hcd : c ≠ d := by
    rintro rfl
    have := hccw (i := 1) (j := 2) (k := 3) (by decide) (by decide)
    simp [EuclideanGeometry.oangle_self_right] at this
  have hab : dist a b ≠ 0 := by
    intro h0; rw [h0] at harea; norm_num at harea
  have hbc : dist b c ≠ 0 := by
    intro h0; rw [h0] at harea; norm_num at harea
  have hcd' : dist c d ≠ 0 := dist_ne_zero.2 hcd
  have sab := dist_sq a b
  have sbc := dist_sq b c
  have scd := dist_sq c d
  rw [ortho_iff] at h1 h2 h3
  have hpar := key (a 0 - b 0) (a 1 - b 1) (c 0 - b 0) (c 1 - b 1) (d 0 - c 0) (d 1 - c 1)
    (by
      have : (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 = dist b c ^ 2 := by rw [sbc]; ring
      rw [this]; exact pow_ne_zero 2 hbc)
    (by
      have : (d 0 - c 0) ^ 2 + (d 1 - c 1) ^ 2 = dist c d ^ 2 := by rw [scd]; ring
      rw [this]; exact pow_ne_zero 2 hcd')
    (by linear_combination -h1) (by linear_combination h2)
    (by linear_combination h3)
  obtain ⟨hd0, hd1⟩ := hpar
  have hd0' : d 0 = a 0 + c 0 - b 0 := by linarith
  have hd1' : d 1 = a 1 + c 1 - b 1 := by linarith
  have harea' : ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2) * ((b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2)
      = 4 := by
    rw [← sab, ← sbc, ← mul_pow, harea]; norm_num
  have hid : (q0 a + q0 c - q0 b - q0 d) ^ 2 + (q1 a + q1 c - q1 b - q1 d) ^ 2 = 16 := by
    simp only [q0, q1]
    rw [hd0', hd1']
    linear_combination 4 * harea'
  obtain ⟨ea0, ea1⟩ := col_eq (ha.trans hb.symm)
  obtain ⟨ec0, ec1⟩ := col_eq (hc.trans hb.symm)
  obtain ⟨ed0, ed1⟩ := col_eq (hd.trans hb.symm)
  have r0 := close (q0 a) (q0 b) (q0 c) (q0 d) ea0 ec0 ed0
  have r1 := close (q1 a) (q1 b) (q1 c) (q1 d) ea1 ec1 ed1
  have p0 := sq_nonneg (q0 a + q0 c - q0 b - q0 d)
  have p1 := sq_nonneg (q1 a + q1 c - q1 b - q1 d)
  rcases r0 with r0 | r0 <;> rcases r1 with r1 | r1 <;> linarith

/-- Graham claims this is "easy to see". -/
theorem erdos_189.variants.square :
    ¬ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction ∧
        dist a b = dist b c)
      (fun a b c d ↦ dist a b * dist b c) := by
  intro h
  apply erdos_189
  intro n hn colouring
  obtain ⟨k, hk⟩ := h n hn colouring
  refine ⟨k, fun area harea => ?_⟩
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, -⟩ := hk area harea
  exact ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩

end Erdos189

#print axioms Erdos189.erdos_189
#print axioms Erdos189.erdos_189.variants.square
