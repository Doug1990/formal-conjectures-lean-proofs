import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Set.Card

namespace Erdos1043

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ (restated from Erdos1043). -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

end Erdos1043

namespace Erdos1048

open Polynomial Erdos1043

namespace Pom

variable {n : ℕ} {ω c : ℂ}

/-- principal n-th root -/
noncomputable def ρ (n : ℕ) (w : ℂ) : ℂ := w ^ ((n : ℂ)⁻¹)

/-- the k-th piece -/
noncomputable def P (n : ℕ) (ω c : ℂ) (k : ℕ) : Set ℂ :=
  (fun w => ω ^ k * ρ n w) '' Metric.closedBall c 1

lemma slit (hc : 1 < c.re) {w : ℂ} (hw : w ∈ Metric.closedBall c 1) : w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - c)
  rw [Complex.sub_re] at h1
  have := (abs_le.1 (h1.trans hw)).1
  linarith

lemma ρ_pow (hn : n ≠ 0) (w : ℂ) : ρ n w ^ n = w := Complex.cpow_nat_inv_pow w hn

lemma ρ_ne (hn : n ≠ 0) {w : ℂ} (hw : w ≠ 0) : ρ n w ≠ 0 := by
  intro h
  apply hw
  rw [← ρ_pow hn w, h, zero_pow hn]

lemma cont (hc : 1 < c.re) (k : ℕ) :
    ContinuousOn (fun w => ω ^ k * ρ n w) (Metric.closedBall c 1) := by
  apply ContinuousOn.mul continuousOn_const
  exact ContinuousOn.cpow_const continuousOn_id (fun a ha => slit hc ha)

lemma isClosed_P (hc : 1 < c.re) (k : ℕ) : IsClosed (P n ω c k) :=
  ((isCompact_closedBall c 1).image_of_continuousOn (cont hc k)).isClosed

lemma isPreconnected_P (hc : 1 < c.re) (k : ℕ) : IsPreconnected (P n ω c k) :=
  (convex_closedBall c 1).isPreconnected.image _ (cont hc k)

lemma ne_zero_of (hc : 1 < c.re) {w : ℂ} (hw : w ∈ Metric.closedBall c 1) : w ≠ 0 := by
  intro h
  have := slit hc hw
  rw [h] at this
  exact Complex.zero_notMem_slitPlane this

lemma pow_P (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (k : ℕ) (w : ℂ) :
    (ω ^ k * ρ n w) ^ n = w := by
  rw [mul_pow, ρ_pow hn, ← pow_mul, mul_comm k n, pow_mul, hω.pow_eq_one, one_pow, one_mul]

lemma mem_union (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) {z : ℂ}
    (hz : z ^ n ∈ Metric.closedBall c 1) : ∃ k < n, z ∈ P n ω c k := by
  have hw0 := ne_zero_of hc hz
  have hρ := ρ_ne hn hw0
  have h1 : (z / ρ n (z ^ n)) ^ n = 1 := by
    rw [div_pow, ρ_pow hn, div_self hw0]
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, he⟩ := hω.eq_pow_of_pow_eq_one h1
  refine ⟨i, hi, z ^ n, hz, ?_⟩
  show ω ^ i * ρ n (z ^ n) = z
  rw [he, div_mul_cancel₀ _ hρ]

lemma disj (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) {j k : ℕ} (hj : j < n)
    (hk : k < n) (hjk : j ≠ k) : Disjoint (P n ω c j) (P n ω c k) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', he⟩
  have h2 : w' = w := by
    have := congrArg (· ^ n) he
    simpa only [pow_P hω hn] using this
  subst h2
  have hρ := ρ_ne hn (ne_zero_of hc hw)
  have : ω ^ k = ω ^ j := mul_right_cancel₀ hρ he
  exact hjk (hω.pow_inj hk hj this).symm

/-- L as a union of the pieces -/
lemma L_eq (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) :
    {z : ℂ | z ^ n ∈ Metric.closedBall c 1} = ⋃ k : Fin n, P n ω c k := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · intro hz
    obtain ⟨k, hk, h⟩ := mem_union hω hn hc hz
    exact ⟨⟨k, hk⟩, h⟩
  · rintro ⟨k, w, hw, rfl⟩
    show (ω ^ (k : ℕ) * ρ n w) ^ n ∈ Metric.closedBall c 1
    rw [pow_P hω hn]
    exact hw

lemma comp_eq (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) (k : Fin n) {z : ℂ}
    (hz : z ∈ P n ω c k) :
    connectedComponentIn (⋃ k : Fin n, P n ω c k) z = P n ω c k := by
  apply Set.Subset.antisymm
  · have hpc := isPreconnected_connectedComponentIn (F := ⋃ k : Fin n, P n ω c k) (x := z)
    have hU : IsClosed (⋃ j ∈ ({k}ᶜ : Set (Fin n)), P n ω c j) :=
      (Set.toFinite _).isClosed_biUnion (fun j _ => isClosed_P hc j)
    have hdis : Disjoint (P n ω c k) (⋃ j ∈ ({k}ᶜ : Set (Fin n)), P n ω c j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact disj hω hn hc k.2 j.2 (fun h => hj (Fin.ext h).symm)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hpc _ _ (isClosed_P hc k) hU
      (by
        intro x hx
        have hx' := connectedComponentIn_subset _ _ hx
        rw [Set.mem_iUnion] at hx'
        obtain ⟨j, hj⟩ := hx'
        by_cases hjk : j = k
        · subst hjk; exact Or.inl hj
        · exact Or.inr (Set.mem_biUnion (x := j) hjk hj))
      (by rw [hdis.inter_eq, Set.inter_empty]) with h | h
    · exact h
    · exfalso
      have hzc : z ∈ connectedComponentIn (⋃ k : Fin n, P n ω c k) z :=
        mem_connectedComponentIn (Set.mem_iUnion.2 ⟨k, hz⟩)
      exact Set.disjoint_left.1 hdis hz (h hzc)
  · exact (isPreconnected_P hc k).subset_connectedComponentIn hz
      (Set.subset_iUnion (fun j : Fin n => P n ω c j) k)

/-- Lipschitz bound for the principal n-th root on the disk. -/
lemma lip (hn : n ≠ 0) (hc : 1 < c.re) {M m : ℝ} (hm : 0 < m)
    (hM : ∀ v ∈ Metric.closedBall c 1, ‖ρ n v‖ ≤ M)
    (hm' : ∀ v ∈ Metric.closedBall c 1, m ≤ ‖v‖) {w w' : ℂ}
    (hw : w ∈ Metric.closedBall c 1) (hw' : w' ∈ Metric.closedBall c 1) :
    ‖ρ n w' - ρ n w‖ ≤ M / (n * m) * ‖w' - w‖ := by
  have hd : ∀ v ∈ Metric.closedBall c 1,
      HasDerivWithinAt (ρ n) ((n : ℂ)⁻¹ * (ρ n v / v)) (Metric.closedBall c 1) v := by
    intro v hv
    have h := (Complex.hasStrictDerivAt_cpow_const (c := (n : ℂ)⁻¹) (slit hc hv)).hasDerivAt
    have he : v ^ ((n : ℂ)⁻¹ - 1) = ρ n v / v := by
      rw [Complex.cpow_sub _ _ (ne_zero_of hc hv), Complex.cpow_one]
      rfl
    rw [he] at h
    exact h.hasDerivWithinAt
  refine (convex_closedBall c 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd ?_ hw hw'
  intro v hv
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le hm (hm' v hv)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM v hv)
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast, inv_mul_eq_div, div_div,
    div_le_div_iff₀ (mul_pos hv0 hn0) (mul_pos hn0 hm)]
  calc ‖ρ n v‖ * (n * m) = n * (‖ρ n v‖ * m) := by ring
    _ ≤ n * (M * ‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hM v hv) (hm' v hv) hm.le hM0) hn0.le
    _ = M * (‖v‖ * n) := by ring

lemma arith {r ε x N n : ℝ} (hr : 1 < r) (hε : 0 < ε) (hN : 4 * r / ((r - 1) * ε) < N)
    (hn : N ≤ n) (hx : r - 1 ≤ x) : 2 * r / (n * x) * 2 < ε := by
  have hpos : 0 < (r - 1) * ε := mul_pos (by linarith) hε
  have h0 := (div_lt_iff₀ hpos).1 hN
  have hN0 : 0 < N := by
    have : 0 < 4 * r / ((r - 1) * ε) := div_pos (by linarith) hpos
    linarith
  have hn0 : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos hn0 hx0)]
  have h1 : N * ((r - 1) * ε) ≤ n * ((r - 1) * ε) := mul_le_mul_of_nonneg_right hn hpos.le
  have h2 : n * ((r - 1) * ε) ≤ n * (x * ε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx hε.le) hn0.le
  linarith

end Pom

theorem erdos_1048.variants.pommerenke_diam_tendsto_zero (r : ℝ) (hr : 1 < r) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ f : ℂ[X], f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n) →
      ∀ z ∈ levelSet f,
        Metric.ediam (connectedComponentIn (levelSet f) z) < ENNReal.ofReal ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * r / ((r - 1) * ε))
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn f hf z hz => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hω := Complex.isPrimitiveRoot_exp n hn0
  set ω := Complex.exp (2 * Real.pi * Complex.I / n) with hωdef
  have hr0 : (0 : ℝ) < r := by linarith
  have hc : 1 < ((r : ℂ) ^ n).re := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact one_lt_pow₀ hr hn0
  have hL : levelSet f = ⋃ k : Fin n, Pom.P n ω ((r : ℂ) ^ n) k := by
    rw [← Pom.L_eq hω hn0 hc]
    ext z
    subst hf
    simp only [levelSet, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_C,
      Metric.mem_closedBall, dist_eq_norm]
  have hcn : ‖((r : ℂ) ^ n)‖ = r ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hrn : r ≤ r ^ n := le_self_pow₀ hr.le hn0
  -- bounds on the disk
  have hlow : ∀ v ∈ Metric.closedBall ((r : ℂ) ^ n) 1, r ^ n - 1 ≤ ‖v‖ := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have := norm_sub_norm_le ((r : ℂ) ^ n) v
    rw [hcn, norm_sub_rev] at this
    linarith
  have hup : ∀ v ∈ Metric.closedBall ((r : ℂ) ^ n) 1, ‖Pom.ρ n v‖ ≤ 2 * r := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have h1 : ‖v‖ ≤ r ^ n + 1 := by
      have := norm_le_norm_add_norm_sub' v ((r : ℂ) ^ n)
      rw [hcn] at this
      linarith
    have h2 : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
    have h4 : ‖Pom.ρ n v‖ ^ n ≤ (2 * r) ^ n := by
      rw [← norm_pow, Pom.ρ_pow hn0, mul_pow]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) hn0).1 h4
  rw [hL] at hz ⊢
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
  rw [Pom.comp_eq hω hn0 hc k hk]
  have hm : (0 : ℝ) < r ^ n - 1 := by linarith
  refine lt_of_le_of_lt (Metric.ediam_le (d := ENNReal.ofReal (2 * r / (n * (r ^ n - 1)) * 2))
    ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm, ← mul_sub, norm_mul, norm_pow, hω.norm'_eq_one hn0, one_pow, one_mul,
      norm_sub_rev]
    refine (Pom.lip hn0 hc hm hup hlow hw hw').trans ?_
    apply mul_le_mul_of_nonneg_left
    · rw [Metric.mem_closedBall, dist_eq_norm] at hw hw'
      calc ‖w' - w‖ = ‖(w' - (r : ℂ) ^ n) - (w - (r : ℂ) ^ n)‖ := by ring_nf
        _ ≤ ‖w' - (r : ℂ) ^ n‖ + ‖w - (r : ℂ) ^ n‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    · have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      positivity
  · rw [ENNReal.ofReal_lt_ofReal_iff hε]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
    exact Pom.arith hr hε hN hNn (by linarith)

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert < 1\}$ -/
def openLevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

theorem erdos_1048 :
    ¬ ∀ (r : ℝ) (f : ℂ[X]), 0 < r → r < 2 → f.Monic → f.degree ≥ 1 → (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
        Metric.ediam (connectedComponentIn (openLevelSet f) z) := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (erdos_1048.variants.pommerenke_diam_tendsto_zero (3 / 2) (by norm_num) (1 / 2) (by norm_num))
  have hn0 : N + 1 ≠ 0 := by omega
  have hmon : ((X : ℂ[X]) ^ (N + 1) - C (((3 / 2 : ℝ) : ℂ) ^ (N + 1))).Monic :=
    monic_X_pow_sub_C _ hn0
  obtain ⟨z, hz, hlt⟩ := h (3 / 2) ((X : ℂ[X]) ^ (N + 1) - C (((3 / 2 : ℝ) : ℂ) ^ (N + 1)))
    (by norm_num) (by norm_num) hmon
    (by
      rw [degree_X_pow_sub_C (by omega : 0 < N + 1)]
      exact_mod_cast (by omega : 1 ≤ N + 1))
    (by
      intro w hw
      rw [mem_roots hmon.ne_zero, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C,
        sub_eq_zero] at hw
      have h1 := congrArg norm hw
      rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h1
      exact (pow_le_pow_iff_left₀ (norm_nonneg w) (by norm_num) hn0).1 h1.le)
  have hsub : openLevelSet ((X : ℂ[X]) ^ (N + 1) - C (((3 / 2 : ℝ) : ℂ) ^ (N + 1))) ⊆
      levelSet ((X : ℂ[X]) ^ (N + 1) - C (((3 / 2 : ℝ) : ℂ) ^ (N + 1))) := by
    intro x hx
    simp only [openLevelSet, levelSet, Set.mem_ofPred_eq] at hx ⊢
    exact hx.le
  have hcomp := (isPreconnected_connectedComponentIn (x := z)).subset_connectedComponentIn
    (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans hsub)
  have h2 := hN (N + 1) (by omega) _ rfl z (hsub hz)
  have h3 := Metric.ediam_mono hcomp
  have h4 : (2 : ℝ) - 3 / 2 = 1 / 2 := by norm_num
  rw [h4] at hlt
  exact absurd (lt_of_le_of_lt h3 h2) (not_lt.2 hlt.le)

end Erdos1048

#print axioms Erdos1048.erdos_1048.variants.pommerenke_diam_tendsto_zero
#print axioms Erdos1048.erdos_1048
