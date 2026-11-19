import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter

open scoped Real Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace GaussCircleProblem

noncomputable abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }.ncard

noncomputable abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

open MeasureTheory

def S (r : ℝ) : Set (ℤ × ℤ) := { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }

noncomputable def pt (p : ℤ × ℤ) : ℝ² := !₂[(p.1 : ℝ), (p.2 : ℝ)]

lemma pt0 (p : ℤ × ℤ) : pt p 0 = p.1 := by simp [pt]
lemma pt1 (p : ℤ × ℤ) : pt p 1 = p.2 := by simp [pt]

lemma mem_S {r : ℝ} {p : ℤ × ℤ} : p ∈ S r ↔ dist (pt p) 0 ≤ r := by
  obtain ⟨m, n⟩ := p
  exact Iff.rfl

lemma d2 (x y : ℝ²) : dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma dist0 (p : ℤ × ℤ) : dist (pt p) 0 = √((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) := by
  rw [d2, pt0, pt1]
  simp

/-- The half-open unit square centred at the lattice point `p`. -/
def Q (p : ℤ × ℤ) : Set ℝ² :=
  {x | (p.1 : ℝ) - 1/2 ≤ x 0 ∧ x 0 < p.1 + 1/2 ∧ (p.2 : ℝ) - 1/2 ≤ x 1 ∧ x 1 < p.2 + 1/2}

lemma mem_Q {p : ℤ × ℤ} {x : ℝ²} : x ∈ Q p ↔
    ((p.1 : ℝ) - 1/2 ≤ x 0 ∧ x 0 < p.1 + 1/2 ∧ (p.2 : ℝ) - 1/2 ≤ x 1 ∧ x 1 < p.2 + 1/2) :=
  Iff.rfl

lemma Q_eq (p : ℤ × ℤ) : Q p = (WithLp.ofLp : ℝ² → (Fin 2 → ℝ)) ⁻¹'
    (Set.univ.pi fun i => Set.Ico ((pt p) i - 1/2) ((pt p) i + 1/2)) := by
  ext x
  rw [mem_Q, Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_two, Set.mem_Ico, Set.mem_Ico,
    pt0, pt1]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩, fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨a, b, c, d⟩⟩

lemma meas_Q (p : ℤ × ℤ) : MeasurableSet (Q p) := by
  rw [Q_eq]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin 2)).measurable

lemma vol_Q (p : ℤ × ℤ) : volume (Q p) = 1 := by
  rw [Q_eq, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  have h : ∀ i, (pt p i + 1/2) - (pt p i - 1/2) = 1 := fun i => by ring
  simp only [h, ENNReal.ofReal_one, Finset.prod_const_one]

lemma Q_inj {p q : ℤ × ℤ} {x : ℝ²} (hp : x ∈ Q p) (hq : x ∈ Q q) : p = q := by
  obtain ⟨a1, a2, a3, a4⟩ := mem_Q.1 hp
  obtain ⟨b1, b2, b3, b4⟩ := mem_Q.1 hq
  have e1 : p.1 < q.1 + 1 := by
    have : (p.1 : ℝ) < q.1 + 1 := by linarith
    exact_mod_cast this
  have e2 : q.1 < p.1 + 1 := by
    have : (q.1 : ℝ) < p.1 + 1 := by linarith
    exact_mod_cast this
  have e3 : p.2 < q.2 + 1 := by
    have : (p.2 : ℝ) < q.2 + 1 := by linarith
    exact_mod_cast this
  have e4 : q.2 < p.2 + 1 := by
    have : (q.2 : ℝ) < p.2 + 1 := by linarith
    exact_mod_cast this
  exact Prod.ext (by omega) (by omega)

lemma close {p : ℤ × ℤ} {x : ℝ²} (hx : x ∈ Q p) : dist x (pt p) ≤ 1 := by
  obtain ⟨a1, a2, a3, a4⟩ := mem_Q.1 hx
  rw [d2, pt0, pt1]
  have h1 : (x 0 - p.1) ^ 2 ≤ 1 / 4 := by nlinarith
  have h2 : (x 1 - p.2) ^ 2 ≤ 1 / 4 := by nlinarith
  calc √((x 0 - p.1) ^ 2 + (x 1 - p.2) ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

lemma S_finite {r : ℝ} (hr : 0 ≤ r) : (S r).Finite := by
  have key : ∀ z : ℤ, (z : ℝ) ^ 2 ≤ r ^ 2 → z ∈ Set.Icc (-⌈r⌉) ⌈r⌉ := by
    intro z hz
    have h1 := abs_le.1 ((sq_le_sq.1 hz).trans_eq (abs_of_nonneg hr))
    have h2 := Int.le_ceil r
    constructor
    · have : (-(⌈r⌉ : ℝ)) ≤ z := by linarith [h1.1]
      exact_mod_cast this
    · have : (z : ℝ) ≤ ⌈r⌉ := by linarith [h1.2]
      exact_mod_cast this
  apply ((Set.finite_Icc (-⌈r⌉) ⌈r⌉).prod (Set.finite_Icc (-⌈r⌉) ⌈r⌉)).subset
  intro p hp
  rw [mem_S, dist0] at hp
  have hA : 0 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
  have hsq : (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ r ^ 2 := by
    have h0 := Real.sqrt_nonneg ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
    calc (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 = (√((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ 2 :=
          (Real.sq_sqrt hA).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ h0 hp 2
  have h1 : (p.1 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  have h2 : (p.2 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  exact Set.mem_prod.2 ⟨key _ h1, key _ h2⟩

lemma ofReal_ball (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal a ^ 2 * ENNReal.ofReal π = ENNReal.ofReal (a ^ 2 * π) := by
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul (by positivity)]

/-- Gauss: `π (r-1)² ≤ N(r) ≤ π (r+1)²` for `r ≥ 1`. -/
lemma bounds {r : ℝ} (hr : 1 ≤ r) :
    (r - 1) ^ 2 * π ≤ (N r : ℝ) ∧ (N r : ℝ) ≤ (r + 1) ^ 2 * π := by
  have hfin := S_finite (r := r) (by linarith)
  set F := hfin.toFinset with hF
  have hN : (N r : ℝ) = F.card := by
    rw [show N r = (S r).ncard from rfl, Set.ncard_eq_toFinset_card _ hfin]
  have hvol : volume (⋃ p ∈ F, Q p) = (F.card : ENNReal) := by
    rw [measure_biUnion_finset (fun p _ q _ hpq => Set.disjoint_left.2
      (fun x hx hy => hpq (Q_inj hx hy))) (fun p _ => meas_Q p)]
    simp [vol_Q]
  have hcard : (F.card : ENNReal) = ENNReal.ofReal (F.card : ℝ) := (ENNReal.ofReal_natCast _).symm
  rw [hN]
  constructor
  · have hsub : Metric.closedBall (0 : ℝ²) (r - 1) ⊆ ⋃ p ∈ F, Q p := by
      intro x hx
      rw [Metric.mem_closedBall] at hx
      set p : ℤ × ℤ := (⌊x 0 + 1/2⌋, ⌊x 1 + 1/2⌋) with hp
      have hxQ : x ∈ Q p := by
        rw [mem_Q]
        have f1 := Int.floor_le (x 0 + 1/2)
        have f2 := Int.lt_floor_add_one (x 0 + 1/2)
        have f3 := Int.floor_le (x 1 + 1/2)
        have f4 := Int.lt_floor_add_one (x 1 + 1/2)
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hpF : p ∈ F := by
        rw [hF, Set.Finite.mem_toFinset, mem_S]
        have := close hxQ
        rw [dist_comm] at this
        linarith [dist_triangle (pt p) x 0]
      exact Set.mem_biUnion hpF hxQ
    have h := measure_mono (μ := volume) hsub
    rw [hvol, EuclideanSpace.volume_closedBall_fin_two, ofReal_ball _ (by linarith), hcard,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  · have hsub : (⋃ p ∈ F, Q p) ⊆ Metric.closedBall (0 : ℝ²) (r + 1) := by
      intro x hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨p, hpF, hxQ⟩ := hx
      rw [hF, Set.Finite.mem_toFinset, mem_S] at hpF
      rw [Metric.mem_closedBall]
      have := close hxQ
      linarith [dist_triangle x (pt p) 0]
    have h := measure_mono (μ := volume) hsub
    rw [hvol, EuclideanSpace.volume_closedBall_fin_two, ofReal_ball _ (by linarith), hcard,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h

theorem error_le : ∀ᶠ r in atTop, |E r| ≤ 2 * √2 * π * r := by
  filter_upwards [eventually_ge_atTop 2] with r hr
  obtain ⟨hL, hU⟩ := bounds (r := r) (by linarith)
  have hs : (7 / 5 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hπ : 0 < π := Real.pi_pos
  have hk : 2 * r + 1 ≤ 2 * √2 * r := by
    have := mul_le_mul_of_nonneg_right hs.le (show (0 : ℝ) ≤ r by linarith)
    linarith
  have hk' := mul_le_mul_of_nonneg_left hk hπ.le
  show |(N r : ℝ) - π * r ^ 2| ≤ 2 * √2 * π * r
  rw [abs_le]
  constructor <;> nlinarith

end GaussCircleProblem

#print axioms GaussCircleProblem.error_le
