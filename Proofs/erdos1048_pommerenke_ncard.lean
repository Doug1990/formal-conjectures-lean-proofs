import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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

lemma P_ne (c : ℂ) (k : ℕ) : (P n ω c k).Nonempty :=
  ⟨_, c, Metric.mem_closedBall_self zero_le_one, rfl⟩

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

lemma comps_eq (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) :
    {C : Set ℂ | ∃ z ∈ (⋃ k : Fin n, P n ω c k),
      C = connectedComponentIn (⋃ k : Fin n, P n ω c k) z} =
      Set.range (fun k : Fin n => P n ω c k) := by
  ext C
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
    exact ⟨k, (comp_eq hω hn hc k hk).symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨z, hz⟩ := P_ne (n := n) (ω := ω) c k
    exact ⟨z, Set.mem_iUnion.2 ⟨k, hz⟩, (comp_eq hω hn hc k hz).symm⟩

lemma card (hω : IsPrimitiveRoot ω n) (hn : n ≠ 0) (hc : 1 < c.re) :
    (Set.range (fun k : Fin n => P n ω c k)).ncard = n := by
  rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro j k hjk
  by_contra hne
  have hd := disj hω hn hc j.2 k.2 (fun h => hne (Fin.ext h))
  dsimp only at hjk
  rw [hjk, disjoint_self, Set.bot_eq_empty] at hd
  exact (P_ne c k).ne_empty hd

end Pom

theorem erdos_1048.variants.pommerenke_ncard_components (r : ℝ) (hr : 1 < r) (n : ℕ) (hn : 1 ≤ n)
    (f : ℂ[X]) (hf : f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n)) :
    {C : Set ℂ | ∃ z ∈ levelSet f, C = connectedComponentIn (levelSet f) z}.ncard = n := by
  have hn0 : n ≠ 0 := by omega
  have hω := Complex.isPrimitiveRoot_exp n hn0
  have hc : 1 < ((r : ℂ) ^ n).re := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact one_lt_pow₀ hr hn0
  have hL : levelSet f = ⋃ k : Fin n, Pom.P n (Complex.exp (2 * Real.pi * Complex.I / n))
      ((r : ℂ) ^ n) k := by
    rw [← Pom.L_eq hω hn0 hc]
    ext z
    subst hf
    simp only [levelSet, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_C,
      Metric.mem_closedBall, dist_eq_norm]
  rw [hL, Pom.comps_eq hω hn0 hc, Pom.card hω hn0 hc]

end Erdos1048

#print axioms Erdos1048.erdos_1048.variants.pommerenke_ncard_components
