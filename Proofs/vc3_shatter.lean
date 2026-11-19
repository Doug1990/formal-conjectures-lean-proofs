import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Real.Cardinality

/-- Restated from FormalConjecturesForMathlib/Combinatorics/SetFamily/VCDim.lean. -/
def Shatters {α : Type*} (𝒜 : Set (Set α)) (A : Set α) : Prop :=
  ∀ ⦃B⦄, B ⊆ A → ∃ C ∈ 𝒜, A ∩ C = B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped Pointwise

namespace VCDimConvex

namespace VC3

/-- Point on the paraboloid `z = x² + y²`. -/
noncomputable def pt (x y : ℝ) : ℝ³ := !₂[x, y, x ^ 2 + y ^ 2]

lemma pt_0 (x y : ℝ) : pt x y 0 = x := by simp [pt]
lemma pt_1 (x y : ℝ) : pt x y 1 = y := by simp [pt]
lemma pt_2 (x y : ℝ) : pt x y 2 = x ^ 2 + y ^ 2 := by simp [pt]

lemma pt_add (x y : ℝ) : pt 0 y + pt x 0 = pt x y := by
  ext i
  fin_cases i <;> simp [pt, add_comm]

/-- A point of the paraboloid is not in the convex hull of other paraboloid points. -/
lemma not_mem (G : Set ℝ³) (p1 p2 : ℝ)
    (hG : ∀ v ∈ G, ∃ x y : ℝ, v = pt x y ∧ (x, y) ≠ (p1, p2)) :
    pt p1 p2 ∉ convexHull ℝ G := by
  intro hmem
  let f : ℝ³ → ℝ := fun v => v 2 - 2 * p1 * v 0 - 2 * p2 * v 1
  have hlin : IsLinearMap ℝ f := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · simp only [f, PiLp.add_apply]; ring
    · simp only [f, PiLp.smul_apply, smul_eq_mul]; ring
  have hsub : G ⊆ {w | -(p1 ^ 2 + p2 ^ 2) < f w} := by
    intro v hv
    obtain ⟨x, y, rfl, hne⟩ := hG v hv
    show -(p1 ^ 2 + p2 ^ 2) < f (pt x y)
    simp only [f, pt_0, pt_1, pt_2]
    have hpos : (x - p1) ^ 2 + (y - p2) ^ 2 ≠ 0 := by
      intro h
      apply hne
      have h1 : (x - p1) ^ 2 = 0 := by linarith [sq_nonneg (x - p1), sq_nonneg (y - p2)]
      have h2 : (y - p2) ^ 2 = 0 := by linarith [sq_nonneg (x - p1), sq_nonneg (y - p2)]
      have e1 : x - p1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
      have e2 : y - p2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
      rw [Prod.mk.injEq]
      constructor <;> linarith
    have hnn : 0 ≤ (x - p1) ^ 2 + (y - p2) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hlt := lt_of_le_of_ne hnn (Ne.symm hpos)
    nlinarith [hlt]
  have h := convexHull_min hsub (convex_halfSpace_gt hlin _) hmem
  have h' : -(p1 ^ 2 + p2 ^ 2) < f (pt p1 p2) := h
  simp only [f, pt_0, pt_1, pt_2] at h'
  nlinarith [h']

lemma exists_inj : ∃ q : Set ℕ → ℝ, Function.Injective q := by
  have h : Cardinal.mk (Set ℕ) = Cardinal.mk ℝ := by
    rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.mk_real, Cardinal.two_power_aleph0]
  obtain ⟨e⟩ := Cardinal.eq.1 h
  exact ⟨e, e.injective⟩

end VC3

open VC3 in
/-- There exists a set in $\mathbb R^3$ shattering an infinite set. -/
lemma exists_infinite_convex_r3_shatters :
    ∃ A C : Set ℝ³, A.Infinite ∧ Convex ℝ C ∧ Shatters {t +ᵥ C | t : ℝ³} A := by
  obtain ⟨q, hq⟩ := exists_inj
  let G : Set ℝ³ := {v | ∃ k : ℕ, ∃ T : Set ℕ, k ∈ T ∧ v = pt k (q T)}
  refine ⟨Set.range (fun k : ℕ => pt k 0), convexHull ℝ G, ?_, convex_convexHull ℝ G, ?_⟩
  · refine Set.infinite_range_of_injective fun j k hjk => ?_
    have := congrArg (fun v : ℝ³ => v 0) hjk
    simp only [pt_0] at this
    exact_mod_cast this
  · intro B hB
    let S : Set ℕ := {k | pt k 0 ∈ B}
    refine ⟨(-pt 0 (q S)) +ᵥ convexHull ℝ G, ⟨_, rfl⟩, ?_⟩
    ext v
    constructor
    · rintro ⟨⟨k, rfl⟩, hv⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, pt_add] at hv
      by_contra hk
      refine not_mem G k (q S) ?_ hv
      rintro w ⟨j, T, hj, rfl⟩
      refine ⟨j, q T, rfl, ?_⟩
      intro he
      rw [Prod.mk.injEq] at he
      have hjk : j = k := by exact_mod_cast he.1
      have hTS : T = S := hq he.2
      rw [hjk, hTS] at hj
      exact hk hj
    · intro hv
      obtain ⟨k, rfl⟩ := hB hv
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, pt_add]
      exact subset_convexHull ℝ G ⟨k, S, hv, rfl⟩

end VCDimConvex

#print axioms VCDimConvex.exists_infinite_convex_r3_shatters
