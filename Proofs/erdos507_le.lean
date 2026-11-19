import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

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

namespace LE

/-- second coordinate (as a natural number) of the k-th point on the parabola mod p -/
def r (p k : ℕ) : ℕ := k ^ 2 % p

noncomputable def f (p k : ℕ) : ℝ² := !₂[(k : ℝ) / (2 * p), (r p k : ℝ) / (2 * p)]

lemma f0 (p k : ℕ) : f p k 0 = (k : ℝ) / (2 * p) := by simp [f]

lemma f1 (p k : ℕ) : f p k 1 = (r p k : ℝ) / (2 * p) := by simp [f]

def D (p a b c : ℕ) : ℤ :=
  ((a : ℤ) - c) * ((r p b : ℤ) - r p c) - ((b : ℤ) - c) * ((r p a : ℤ) - r p c)

lemma area_f (p a b c : ℕ) (hp : 0 < p) :
    EuclideanGeometry.triangle_area (f p a) (f p b) (f p c) = (D p a b c : ℝ) / (8 * p ^ 2) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [UT.area_eq, f0, f0, f0, f1, f1, f1, D]
  push_cast
  field_simp
  ring

lemma natCast_inj (p a c : ℕ) (ha : a < p) (hc : c < p) (h : (a : ZMod p) = c) : a = c := by
  have := (ZMod.natCast_eq_natCast_iff' a c p).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this

lemma D_ne (p a b c : ℕ) (hp : p.Prime) (ha : a < p) (hb : b < p) (hc : c < p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : D p a b c ≠ 0 := by
  have := Fact.mk hp
  intro h
  have h2 : ((D p a b c : ℤ) : ZMod p) = 0 := by rw [h]; simp
  simp only [D, r, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_mod,
    Nat.cast_pow] at h2
  have h3 : ((a : ZMod p) - c) * ((b : ZMod p) - c) * ((b : ZMod p) - a) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact hac (natCast_inj p a c ha hc (sub_eq_zero.mp h5))
    · exact hbc (natCast_inj p b c hb hc (sub_eq_zero.mp h5))
  · exact hab (natCast_inj p b a hb ha (sub_eq_zero.mp h4)).symm

lemma area_ge (p a b c : ℕ) (hp : p.Prime) (ha : a < p) (hb : b < p) (hc : c < p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    1 / (8 * (p : ℝ) ^ 2) ≤ |EuclideanGeometry.triangle_area (f p a) (f p b) (f p c)| := by
  have hp0 := hp.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [area_f p a b c hp0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * p ^ 2)]
  have h1 : (1 : ℤ) ≤ |D p a b c| := Int.one_le_abs (D_ne p a b c hp ha hb hc hab hac hbc)
  have h1' : (1 : ℝ) ≤ |(D p a b c : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast h1
  exact div_le_div_of_nonneg_right h1' (by positivity)

lemma f_inj (p : ℕ) (hp : 0 < p) : Function.Injective (f p) := by
  intro a b h
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have := congrArg (fun x : ℝ² => x 0) h
  simp only [f0] at this
  field_simp at this
  exact_mod_cast this

lemma f_norm (p k : ℕ) (hp : 0 < p) (hk : k < p) : ‖f p k‖ ≤ 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hk' : (k : ℝ) ≤ p := by exact_mod_cast hk.le
  have hr : (r p k : ℝ) ≤ p := by exact_mod_cast (Nat.mod_lt _ hp).le
  have e0 : 0 ≤ (k : ℝ) / (2 * p) ∧ (k : ℝ) / (2 * p) ≤ 1 / 2 := by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]; linarith
  have e1 : 0 ≤ (r p k : ℝ) / (2 * p) ∧ (r p k : ℝ) / (2 * p) ≤ 1 / 2 := by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]; linarith
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    f0, f1]
  have s0 := pow_le_pow_left₀ e0.1 e0.2 2
  have s1 := pow_le_pow_left₀ e1.1 e1.2 2
  have hs : ((k : ℝ) / (2 * p)) ^ 2 + ((r p k : ℝ) / (2 * p)) ^ 2 ≤ 1 := by
    have : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    linarith
  calc √(((k : ℝ) / (2 * p)) ^ 2 + ((r p k : ℝ) / (2 * p)) ^ 2) ≤ √1 :=
        Real.sqrt_le_sqrt hs
    _ = 1 := Real.sqrt_one

lemma not_collinear (p : ℕ) (hp : p.Prime) (h2 : 2 < p) (S : Finset ℝ²)
    (h0 : f p 0 ∈ S) (h1 : f p 1 ∈ S) (h2' : f p 2 ∈ S) : ¬ Collinear ℝ (S : Set ℝ²) := by
  intro hcol
  have hne := area_ge p 0 1 2 hp (by omega) (by omega) h2 (by omega) (by omega) (by omega)
  rw [collinear_iff_of_mem (Finset.mem_coe.mpr h2')] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨ra, hra⟩ := hv _ (Finset.mem_coe.mpr h0)
  obtain ⟨rb, hrb⟩ := hv _ (Finset.mem_coe.mpr h1)
  have hz : EuclideanGeometry.triangle_area (f p 0) (f p 1) (f p 2) = 0 := by
    rw [UT.area_eq, hra, hrb]
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hz, abs_zero] at hne
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have : (0 : ℝ) < 1 / (8 * (p : ℝ) ^ 2) := by positivity
  linarith

lemma inj3 (g : ℕ → ℝ²) (hg : Function.Injective g) : Function.Injective ![g 0, g 1, g 2] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [hg.eq_iff] at hij ⊢

lemma mta_ge (p n : ℕ) (hp : p.Prime) (hnp : n < p) (hn : 3 ≤ n) :
    1 / (8 * (p : ℝ) ^ 2) ≤ minTriangleArea ((Finset.range n).image (f p)) := by
  have hp0 := hp.pos
  have finj := f_inj p hp0
  have mem : ∀ k, k < n → f p k ∈ (Finset.range n).image (f p) := fun k hk =>
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  apply le_csInf
  · refine ⟨_, ![f p 0, f p 1, f p 2], inj3 (f p) finj, ?_, rfl⟩
    intro i
    fin_cases i
    · exact mem 0 (by omega)
    · exact mem 1 (by omega)
    · exact mem 2 (by omega)
  · rintro _ ⟨q, hq, hmem, rfl⟩
    have := fun i => Finset.mem_image.mp (hmem i)
    choose k hk hkq using this
    simp only [Finset.mem_range] at hk
    have hne : ∀ i j, i ≠ j → k i ≠ k j := by
      intro i j hij hk'
      apply hij
      apply hq
      rw [← hkq i, ← hkq j, hk']
    rw [← hkq 0, ← hkq 1, ← hkq 2]
    exact area_ge p _ _ _ hp (by have := hk 0; omega) (by have := hk 1; omega)
      (by have := hk 2; omega) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))

end LE

theorem erdos_507.variants.lower_erdos :
    Asymptotics.IsBigO Filter.atTop ((fun n ↦ 1 / (n : ℝ) ^ 2) : ℕ → ℝ) (α : ℕ → ℝ) := by
  refine Asymptotics.IsBigO.of_bound 32 ?_
  filter_upwards [Filter.eventually_ge_atTop 7] with n hn
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hp0 := hp.pos
  set S := (Finset.range n).image (LE.f p) with hSdef
  have hmem : ∀ k, k < n → LE.f p k ∈ S := fun k hk =>
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hball : ∀ x ∈ S, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact LE.f_norm p k hp0 (by rw [Finset.mem_range] at hk; omega)
  have hcard : S.card = n := by
    rw [hSdef, Finset.card_image_of_injective _ (LE.f_inj p hp0), Finset.card_range]
  have hS : S ∈ { S : Finset ℝ² |
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) } := by
    refine ⟨hcard, ?_, LE.not_collinear p hp (by omega) S (hmem 0 (by omega)) (hmem 1 (by omega))
      (hmem 2 (by omega))⟩
    intro x hx
    exact mem_closedBall_zero_iff.mpr (hball x hx)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbdd : BddAbove (minTriangleArea '' { S : Finset ℝ² |
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) }) := by
    refine ⟨56 / n, ?_⟩
    rintro _ ⟨T, ⟨hc, hT, -⟩, rfl⟩
    exact UT.mta_le T n hn hc (fun q hq => mem_closedBall_zero_iff.mp (hT hq))
  have hα : minTriangleArea S ≤ α n := le_csSup hbdd ⟨S, hS, rfl⟩
  have hm := LE.mta_ge p n hp hnp (by omega)
  have hp' : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp0
  have hcmp : 1 / (32 * (n : ℝ) ^ 2) ≤ 1 / (8 * (p : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by
      have := pow_le_pow_left₀ hpp.le hp' 2
      have e : (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 := by ring
      linarith)
  have hαpos : 0 ≤ α n := le_trans (by positivity) (hm.trans hα)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hαpos]
  have : 1 / (n : ℝ) ^ 2 = 32 * (1 / (32 * (n : ℝ) ^ 2)) := by field_simp
  rw [this]
  linarith

end Erdos507

#print axioms Erdos507.erdos_507.variants.lower_erdos
