import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Local restatements of the checkout definitions (FormalConjecturesForMathlib:
`Geometry/Metric.lean`, `Geometry/2d.lean`, `Data/Set/Triplewise.lean`). -/

open scoped Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Defs

variable {X : Type*} [MetricSpace X]

open Classical in
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

end Defs

protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

end EuclideanGeometry

namespace Erdos1082

open EuclideanGeometry

namespace H8

/-- `a = √3 - 1` in `ℤ[√3]`. -/
def a : ℤ√3 := ⟨-1, 1⟩

/-- Square corners `(±1, ±1)` and axis points `(±a, 0)`, `(0, ±a)`. -/
def cz : Fin 8 → ℤ√3 × ℤ√3 :=
  ![(1, 1), (1, -1), (-1, 1), (-1, -1), (a, 0), (-a, 0), (0, a), (0, -a)]

def D2 (i j : Fin 8) : ℤ√3 :=
  ((cz i).1 - (cz j).1) * ((cz i).1 - (cz j).1) + ((cz i).2 - (cz j).2) * ((cz i).2 - (cz j).2)

def detZ (i j k : Fin 8) : ℤ√3 :=
  ((cz j).1 - (cz i).1) * ((cz k).2 - (cz i).2) - ((cz j).2 - (cz i).2) * ((cz k).1 - (cz i).1)

lemma cz_inj : ∀ i j : Fin 8, cz i = cz j → i = j := by decide

lemma det_ne : ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k → detZ i j k ≠ 0 := by decide

lemma card_D2 : ∀ i : Fin 8, ((Finset.univ.erase i).image (fun j => D2 j i)).card ≤ 3 := by
  decide

lemma s3 : Real.sqrt 3 * Real.sqrt 3 = ((3 : ℤ) : ℝ) := by
  rw [Real.mul_self_sqrt (by norm_num)]; norm_num

noncomputable def φ : ℤ√3 →+* ℝ := Zsqrtd.lift ⟨Real.sqrt 3, s3⟩

lemma φ_inj : Function.Injective φ := by
  refine Zsqrtd.lift_injective _ ?_
  intro n hn
  have h1 : n ≤ 2 := by nlinarith
  have h2 : -2 ≤ n := by nlinarith
  interval_cases n <;> omega

noncomputable def pt (i : Fin 8) : ℝ² := WithLp.toLp 2 ![φ (cz i).1, φ (cz i).2]

lemma pt0 (i : Fin 8) : pt i 0 = φ (cz i).1 := by simp [pt]
lemma pt1 (i : Fin 8) : pt i 1 = φ (cz i).2 := by simp [pt]

lemma pt_inj : Function.Injective pt := by
  intro i j h
  have h0 := congrArg (fun p : ℝ² => p 0) h
  have h1 := congrArg (fun p : ℝ² => p 1) h
  simp only [pt0, pt1] at h0 h1
  exact cz_inj i j (Prod.ext (φ_inj h0) (φ_inj h1))

lemma dist_pt (i j : Fin 8) : dist (pt i) (pt j) = Real.sqrt (φ (D2 i j)) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
    pt0, pt0, pt1, pt1]
  congr 1
  simp only [D2, map_add, map_mul, map_sub]
  ring

lemma col_det {p q r : ℝ²} (h : Collinear ℝ ({p, q, r} : Set ℝ²)) :
    (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0) = 0 := by
  rw [collinear_iff_of_mem (p₀ := p) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨t, ht⟩ := hv q (by simp)
  obtain ⟨u, hu⟩ := hv r (by simp)
  have hq0 : q 0 = t * v 0 + p 0 := by rw [ht]; simp
  have hq1 : q 1 = t * v 1 + p 1 := by rw [ht]; simp
  have hr0 : r 0 = u * v 0 + p 0 := by rw [hu]; simp
  have hr1 : r 1 = u * v 1 + p 1 := by rw [hu]; simp
  rw [hq0, hq1, hr0, hr1]
  ring

end H8

open H8 in
theorem erdos_1082.parts.ii :
    ¬ ∀ (A : Finset ℝ²) (hA : A.Nonempty) (hA_n3c : NonTrilinear (A : Set ℝ²)),
    ∃ (a : ℝ²) (ha : a ∈ A), A.card / 2 ≤ distinctDistancesFrom A a := by
  intro hall
  classical
  set A : Finset ℝ² := Finset.univ.image pt with hAdef
  have hne : A.Nonempty := ⟨pt 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hnt : NonTrilinear (A : Set ℝ²) := by
    intro x hx y hy z hz hxy hyz hxz hcol
    simp only [hAdef, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy hz
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := hz
    have hd := col_det hcol
    simp only [pt0, pt1] at hd
    have hd' : φ (detZ i j k) = φ 0 := by
      rw [map_zero, ← hd]
      simp only [detZ, map_sub, map_mul]
    exact det_ne i j k (fun h => hxy (h ▸ rfl)) (fun h => hyz (h ▸ rfl)) (fun h => hxz (h ▸ rfl))
      (φ_inj hd')
  obtain ⟨x, hx, hle⟩ := hall A hne hnt
  rw [hAdef, Finset.mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  have hcard : A.card = 8 := by
    rw [hAdef, Finset.card_image_of_injective _ pt_inj]; rfl
  have hdd : distinctDistancesFrom A (pt i) ≤ 3 := by
    unfold distinctDistancesFrom
    refine le_trans (Finset.card_le_card (t := ((Finset.univ.erase i).image
      (fun j => D2 j i)).image (fun z => Real.sqrt (φ z))) ?_)
      (le_trans Finset.card_image_le (card_D2 i))
    intro d hd
    simp only [hAdef, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and,
      and_true] at hd ⊢
    obtain ⟨x, ⟨hx, j, rfl⟩, rfl⟩ := hd
    exact ⟨D2 j i, ⟨j, fun h => hx (h ▸ rfl), rfl⟩, (dist_pt j i).symm⟩
  rw [hcard] at hle
  have : (8 : ℕ) / 2 = 4 := rfl
  omega

end Erdos1082

#print axioms Erdos1082.erdos_1082.parts.ii
