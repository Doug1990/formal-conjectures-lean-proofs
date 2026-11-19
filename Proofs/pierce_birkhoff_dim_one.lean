import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Polynomial Set Filter Topology

namespace PierceBirkhoff

def IsSemiAlgebraic₁ (S : Set ℝ) : Prop :=
  ∃ (ι₀ ι₁ : Type) (p₀ : ι₀ → Polynomial ℝ) (p₁ : ι₁ → Polynomial ℝ), Finite ι₀ ∧ Finite ι₁ ∧
    S = (⋃ i, {x | Polynomial.eval x (p₀ i) = 0}) ∪ ⋃ i, {x | Polynomial.eval x (p₁ i) > 0}

def IsPiecewisePolynomial (f : ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set ℝ)
    (g : ι → Polynomial ℝ),
    Finite ι ∧
    (∀ (i : ι), IsClosed (P i)) ∧
    (∀ (i : ι), IsSemiAlgebraic₁ (P i)) ∧
    (⋃ (i : ι), P i) = Set.univ ∧
    ∀ᵉ (i : ι) (x ∈ P i), f x = Polynomial.eval x (g i)

namespace PB

/-! ## Sup-inf representable functions -/

def Rep (f : ℝ → ℝ) : Prop :=
  ∃ (ι κ : Type) (g : ι → κ → ℝ[X]), Finite ι ∧ Finite κ ∧ Nonempty ι ∧ Nonempty κ ∧
    ∀ x, f x = ⨆ i, ⨅ j, eval x (g i j)

lemma isSup {ι : Type} [Finite ι] [Nonempty ι] (u : ι → ℝ) (s : ℝ)
    (h1 : ∀ i, u i ≤ s) (h2 : ∃ i, u i = s) : (⨆ i, u i) = s := by
  obtain ⟨i, hi⟩ := h2
  refine le_antisymm (ciSup_le h1) ?_
  rw [← hi]
  exact le_ciSup (Finite.bddAbove_range u) i

lemma isInf {ι : Type} [Finite ι] [Nonempty ι] (u : ι → ℝ) (s : ℝ)
    (h1 : ∀ i, s ≤ u i) (h2 : ∃ i, u i = s) : (⨅ i, u i) = s := by
  obtain ⟨i, hi⟩ := h2
  refine le_antisymm ?_ (le_ciInf h1)
  rw [← hi]
  exact ciInf_le (Finite.bddBelow_range u) i

lemma sup_add {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (u : ι → ℝ) (v : κ → ℝ) :
    (⨆ p : ι × κ, (u p.1 + v p.2)) = (⨆ i, u i) + ⨆ k, v k := by
  apply isSup
  · intro p
    exact add_le_add (le_ciSup (Finite.bddAbove_range u) p.1)
      (le_ciSup (Finite.bddAbove_range v) p.2)
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := u)
    obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := v)
    exact ⟨(i, k), by rw [hi, hk]⟩

lemma inf_add {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (u : ι → ℝ) (v : κ → ℝ) :
    (⨅ p : ι × κ, (u p.1 + v p.2)) = (⨅ i, u i) + ⨅ k, v k := by
  apply isInf
  · intro p
    exact add_le_add (ciInf_le (Finite.bddBelow_range u) p.1)
      (ciInf_le (Finite.bddBelow_range v) p.2)
  · obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := u)
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := v)
    exact ⟨(i, k), by rw [hi, hk]⟩

lemma Rep_congr {f g : ℝ → ℝ} (hf : Rep f) (h : ∀ x, f x = g x) : Rep g := by
  obtain ⟨ι, κ, a, h1, h2, h3, h4, ha⟩ := hf
  exact ⟨ι, κ, a, h1, h2, h3, h4, fun x => (h x).symm.trans (ha x)⟩

lemma Rep_add {f g : ℝ → ℝ} (hf : Rep f) (hg : Rep g) : Rep (fun x => f x + g x) := by
  obtain ⟨ι, κ, a, h1, h2, h3, h4, ha⟩ := hf
  obtain ⟨ι', κ', b, h1', h2', h3', h4', hb⟩ := hg
  refine ⟨ι × ι', κ × κ', fun p q => a p.1 q.1 + b p.2 q.2, inferInstance, inferInstance,
    inferInstance, inferInstance, fun x => ?_⟩
  have e : ∀ p : ι × ι', (⨅ q : κ × κ', eval x (a p.1 q.1 + b p.2 q.2)) =
      (⨅ j, eval x (a p.1 j)) + ⨅ j, eval x (b p.2 j) := by
    intro p
    rw [← inf_add (fun j => eval x (a p.1 j)) (fun j => eval x (b p.2 j))]
    simp only [eval_add]
  calc f x + g x = (⨆ i, ⨅ j, eval x (a i j)) + ⨆ k, ⨅ j, eval x (b k j) := by rw [ha, hb]
    _ = ⨆ p : ι × ι', ((⨅ j, eval x (a p.1 j)) + ⨅ j, eval x (b p.2 j)) :=
        (sup_add (fun i => ⨅ j, eval x (a i j)) (fun k => ⨅ j, eval x (b k j))).symm
    _ = ⨆ p : ι × ι', ⨅ q : κ × κ', eval x (a p.1 q.1 + b p.2 q.2) :=
        iSup_congr fun p => (e p).symm

lemma Rep_poly (p : ℝ[X]) : Rep (fun x => eval x p) :=
  ⟨Unit, Unit, fun _ _ => p, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by simp only [ciInf_const, ciSup_const]⟩

lemma Rep_max0 (p : ℝ[X]) : Rep (fun x => max (eval x p) 0) := by
  refine ⟨Bool, Unit, fun b _ => if b then p else 0, inferInstance, inferInstance,
    inferInstance, inferInstance, fun x => ?_⟩
  simp only [ciInf_const]
  symm
  apply isSup
  · intro b; cases b <;> simp
  · rcases le_total (eval x p) 0 with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩

lemma Rep_min0 (p : ℝ[X]) : Rep (fun x => min (eval x p) 0) := by
  refine ⟨Unit, Bool, fun _ b => if b then p else 0, inferInstance, inferInstance,
    inferInstance, inferInstance, fun x => ?_⟩
  simp only [ciSup_const]
  symm
  apply isInf
  · intro b; cases b <;> simp
  · rcases le_total (eval x p) 0 with h | h
    · exact ⟨true, by simp [h]⟩
    · exact ⟨false, by simp [h]⟩

lemma Rep_sum (s : Finset ℝ) (F : ℝ → ℝ → ℝ) (h : ∀ a ∈ s, Rep (F a)) :
    Rep (fun x => ∑ a ∈ s, F a x) := by
  induction s using Finset.induction_on with
  | empty => exact Rep_congr (Rep_poly 0) (fun x => by simp)
  | @insert a s ha ih =>
    refine Rep_congr (Rep_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))) (fun x => ?_)
    rw [Finset.sum_insert ha]

noncomputable def jump (z : ℝ) (d : ℝ[X]) (y : ℝ) : ℝ := if z ≤ y then eval y d else 0

lemma Rep_jump (z : ℝ) (d : ℝ[X]) (hd : eval z d = 0) : Rep (jump z d) := by
  obtain ⟨r, hr⟩ : ∃ r, (X - C z) * r = d := ⟨_, mul_divByMonic_eq_iff_isRoot.2 hd⟩
  subst hr
  refine Rep_congr (Rep_add (Rep_max0 ((X - C z) * (C (1/4) * (r + 1)^2)))
    (Rep_min0 (-((X - C z) * (C (1/4) * (r - 1)^2))))) (fun x => ?_)
  simp only [jump, eval_mul, eval_sub, eval_X, eval_C, eval_pow, eval_add, eval_one, eval_neg]
  generalize eval x r = R
  have hA : 0 ≤ 1/4 * (R+1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have hB : 0 ≤ 1/4 * (R-1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  split_ifs with h
  · have hu : 0 ≤ x - z := sub_nonneg.2 h
    rw [max_eq_left (mul_nonneg hu hA), min_eq_left (neg_nonpos.2 (mul_nonneg hu hB))]
    ring
  · have hu : 0 ≤ -(x - z) := by linarith [not_le.1 h]
    have h1 := mul_nonneg hu hA
    have h2 := mul_nonneg hu hB
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    simp

/-! ## Local structure of a piecewise polynomial function -/

def Zs {ι : Type} (g : ι → ℝ[X]) : Set ℝ :=
  {z | ∃ i j, g i ≠ g j ∧ eval z (g i) = eval z (g j)}

lemma mk_Zs {ι : Type} (g : ι → ℝ[X]) {i j : ι} {z : ℝ} (h : g i ≠ g j)
    (e : eval z (g i) = eval z (g j)) : z ∈ Zs g := by
  unfold Zs; exact ⟨i, j, h, e⟩

lemma Zfin {ι : Type} [Finite ι] (g : ι → ℝ[X]) : (Zs g).Finite := by
  refine (Set.finite_iUnion (fun p : {p : ι × ι // g p.1 ≠ g p.2} =>
    Polynomial.finite_setOfPred_isRoot (sub_ne_zero.2 p.2))).subset ?_
  intro z hz
  unfold Zs at hz
  obtain ⟨i, j, hij, he⟩ := hz
  refine mem_iUnion.2 ⟨⟨(i, j), hij⟩, ?_⟩
  show IsRoot (g i - g j) z
  simp only [IsRoot.def, eval_sub, he, sub_self]

section
variable {ι : Type} [Finite ι] (P : ι → Set ℝ) (g : ι → ℝ[X]) (f : ℝ → ℝ)
    (hc : ∀ i, IsClosed (P i)) (hcov : ∀ x, ∃ i, x ∈ P i)
    (hf : ∀ i, ∀ x ∈ P i, f x = eval x (g i))
include hc hcov hf

lemma conn (s : Set ℝ) (hs : IsPreconnected s)
    (hcl : ∀ y ∈ s, ∀ i j, y ∈ P i → y ∈ P j → g i = g j)
    (y0 : ℝ) (hy0 : y0 ∈ s) (i0 : ι) (hi0 : y0 ∈ P i0) :
    ∀ y ∈ closure s, f y = eval y (g i0) := by
  have ht : IsClosed (⋃ i : {i // g i = g i0}, P i) := isClosed_iUnion_of_finite fun i => hc i
  have ht' : IsClosed (⋃ i : {i // g i ≠ g i0}, P i) := isClosed_iUnion_of_finite fun i => hc i
  have hcover : s ⊆ (⋃ i : {i // g i = g i0}, P i) ∪ ⋃ i : {i // g i ≠ g i0}, P i := by
    intro w _
    obtain ⟨k, hk⟩ := hcov w
    by_cases hk' : g k = g i0
    · exact Or.inl (mem_iUnion.2 ⟨⟨k, hk'⟩, hk⟩)
    · exact Or.inr (mem_iUnion.2 ⟨⟨k, hk'⟩, hk⟩)
  have hsub : s ⊆ ⋃ i : {i // g i = g i0}, P i := by
    intro y hy
    obtain ⟨i, hi⟩ := hcov y
    by_cases h : g i = g i0
    · exact mem_iUnion.2 ⟨⟨i, h⟩, hi⟩
    · exfalso
      obtain ⟨w, hws, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hs _ _ ht ht' hcover
        ⟨y0, hy0, mem_iUnion.2 ⟨⟨i0, rfl⟩, hi0⟩⟩ ⟨y, hy, mem_iUnion.2 ⟨⟨i, h⟩, hi⟩⟩
      obtain ⟨⟨a, ha⟩, hwa⟩ := mem_iUnion.1 hwt
      obtain ⟨⟨b, hb⟩, hwb⟩ := mem_iUnion.1 hwt'
      exact hb ((hcl w hws b a hwb hwa).trans ha)
  intro y hy
  obtain ⟨⟨i, hi⟩, hyi⟩ := mem_iUnion.1 (closure_minimal hsub ht hy)
  rw [hf i y hyi, hi]

lemma loc (x : ℝ) :
    ∃ ε > 0, ∃ iL iR : ι, (∀ y ∈ Icc (x - ε) x, f y = eval y (g iL)) ∧
      (∀ y ∈ Icc x (x + ε), f y = eval y (g iR)) ∧
      (∀ y ∈ Ioo (x - ε) (x + ε), y ≠ x → y ∉ Zs g) ∧ (x ∉ Zs g → g iL = g iR) := by
  have hZ := Zfin g
  have hn : (Zs g \ {x})ᶜ ∈ 𝓝 x :=
    (hZ.subset (fun y hy => hy.1)).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  have hfar : ∀ y ∈ Ioo (x - ε) (x + ε), y ≠ x → y ∉ Zs g := by
    intro y hy hyx hyZ
    have : y ∈ Metric.ball x ε := by rw [Real.ball_eq_Ioo]; exact hy
    exact hball this ⟨hyZ, hyx⟩
  have hclean : ∀ s ⊆ Ioo (x - ε) (x + ε), x ∉ s →
      ∀ y ∈ s, ∀ i j, y ∈ P i → y ∈ P j → g i = g j := by
    intro s hs hxs y hy i j hi hj
    by_contra hne
    exact hfar y (hs hy) (fun h => hxs (h ▸ hy))
      (mk_Zs g hne (by rw [← hf i y hi, ← hf j y hj]))
  obtain ⟨iR, hiR⟩ := hcov (x + ε/2)
  obtain ⟨iL, hiL⟩ := hcov (x - ε/2)
  have hR : ∀ y ∈ Icc x (x + ε), f y = eval y (g iR) := by
    have := conn P g f hc hcov hf (Ioo x (x + ε)) isPreconnected_Ioo
      (hclean _ (Ioo_subset_Ioo (by linarith) le_rfl) (fun h => lt_irrefl x h.1))
      (x + ε/2) ⟨by linarith, by linarith⟩ iR hiR
    rwa [closure_Ioo (ne_of_lt (by linarith : x < x + ε))] at this
  have hL : ∀ y ∈ Icc (x - ε) x, f y = eval y (g iL) := by
    have := conn P g f hc hcov hf (Ioo (x - ε) x) isPreconnected_Ioo
      (hclean _ (Ioo_subset_Ioo le_rfl (by linarith)) (fun h => lt_irrefl x h.2))
      (x - ε/2) ⟨by linarith, by linarith⟩ iL hiL
    rwa [closure_Ioo (ne_of_lt (by linarith : x - ε < x))] at this
  refine ⟨ε, hε, iL, iR, hL, hR, hfar, fun hx => ?_⟩
  by_contra hne
  exact hx (mk_Zs g hne (by rw [← hL x ⟨by linarith, le_rfl⟩, ← hR x ⟨le_rfl, by linarith⟩]))

end

/-! ## Globalisation -/

lemma glob (h : ℝ → ℝ) (H : ∀ x, ∃ Q : ℝ[X], ∀ᶠ y in 𝓝 x, h y = eval y Q) :
    ∃ Q : ℝ[X], ∀ y, h y = eval y Q := by
  obtain ⟨Q0, hQ0⟩ := H 0
  have hU : IsOpen {x | ∀ᶠ y in 𝓝 x, h y = eval y Q0} := isOpen_setOfPred_eventually_nhds
  have hUc : IsClosed {x | ∀ᶠ y in 𝓝 x, h y = eval y Q0} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨Q, hQ⟩ := H x
    filter_upwards [eventually_eventually_nhds.2 hQ] with y hy
    intro hyU
    apply hx
    have : Q = Q0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hmem : {w | eval w Q = eval w Q0} ∈ 𝓝 y := by
        filter_upwards [hy, hyU] with w h1 h2
        rw [← h1, ← h2]
      exact infinite_of_mem_nhds y hmem
    show ∀ᶠ y in 𝓝 x, h y = eval y Q0
    rw [← this]; exact hQ
  have huniv := IsClopen.eq_univ ⟨hUc, hU⟩ ⟨0, hQ0⟩
  refine ⟨Q0, fun y => ?_⟩
  have hy : y ∈ {x | ∀ᶠ y in 𝓝 x, h y = eval y Q0} := by rw [huniv]; trivial
  exact hy.self_of_nhds

/-! ## Main argument -/

theorem main {ι : Type} [Finite ι] (P : ι → Set ℝ) (g : ι → ℝ[X]) (f : ℝ → ℝ)
    (hc : ∀ i, IsClosed (P i)) (hcov : ∀ x, ∃ i, x ∈ P i)
    (hf : ∀ i, ∀ x ∈ P i, f x = eval x (g i)) : Rep f := by
  have hZ := Zfin g
  choose ε hε iL iR hL hR hZx hLR using loc P g f hc hcov hf
  set Zf := hZ.toFinset
  have hloc : ∀ x, ∃ Q : ℝ[X], ∀ᶠ y in 𝓝 x,
      f y - ∑ z ∈ Zf, jump z (g (iR z) - g (iL z)) y = eval y Q := by
    intro x
    have hfar : ∀ z ∈ Zf, z ≠ x → ∀ y ∈ Ioo (x - ε x) (x + ε x), (z ≤ y ↔ z ≤ x) := by
      intro z hz hzx y hy
      have hzZ : z ∈ Zs g := hZ.mem_toFinset.1 hz
      have hno : z ∉ Ioo (x - ε x) (x + ε x) := fun h => hZx x z h hzx hzZ
      rw [mem_Ioo] at hy
      rcases le_or_gt z (x - ε x) with h | h
      · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
      · have h2 : x + ε x ≤ z := by
          by_contra h'
          exact hno ⟨h, not_le.1 h'⟩
        exact ⟨fun h1 => by linarith, fun h1 => by linarith [hε x]⟩
    refine ⟨g (iL x) - ∑ z ∈ (Zf.erase x).filter (· ≤ x), (g (iR z) - g (iL z)), ?_⟩
    refine Filter.eventually_of_mem
      (Ioo_mem_nhds (by linarith [hε x] : x - ε x < x) (by linarith [hε x] : x < x + ε x))
      fun y hy => ?_
    have hrest : ∑ z ∈ Zf.erase x, jump z (g (iR z) - g (iL z)) y =
        ∑ z ∈ (Zf.erase x).filter (· ≤ x), eval y (g (iR z) - g (iL z)) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z hz => ?_
      have := hfar z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz) y hy
      simp only [jump, this]
    have hself : f y - (if x ∈ Zf then jump x (g (iR x) - g (iL x)) y else 0) =
        eval y (g (iL x)) := by
      have hy' := hy
      rw [mem_Ioo] at hy'
      by_cases hxy : x ≤ y
      · have e1 := hR x y ⟨hxy, hy'.2.le⟩
        split_ifs with hx
        · simp only [jump, if_pos hxy, eval_sub]; rw [e1]; ring
        · rw [e1, hLR x (fun h => hx (hZ.mem_toFinset.2 h))]; ring
      · have e1 := hL x y ⟨hy'.1.le, (not_le.1 hxy).le⟩
        split_ifs with hx
        · simp only [jump, if_neg hxy]; rw [e1]; ring
        · rw [e1]; ring
    rw [eval_sub, eval_finsetSum, ← hrest, ← hself]
    by_cases hx : x ∈ Zf
    · rw [if_pos hx, ← Finset.add_sum_erase Zf _ hx]; ring
    · rw [if_neg hx, Finset.erase_eq_self.2 hx]; ring
  obtain ⟨Q, hQ⟩ := glob _ hloc
  refine Rep_congr (Rep_add (Rep_poly Q) (Rep_sum Zf (fun z => jump z (g (iR z) - g (iL z)))
    fun z _ => Rep_jump z _ ?_)) (fun y => ?_)
  · have h1 := hL z z ⟨by linarith [hε z], le_rfl⟩
    have h2 := hR z z ⟨le_rfl, by linarith [hε z]⟩
    rw [eval_sub, ← h1, ← h2, sub_self]
  · rw [← hQ y]; ring

end PB

theorem pierce_birkhoff_conjecture_dim_one (f : ℝ → ℝ)
    (hf : IsPiecewisePolynomial f) :
    ∃ (ι κ : Type) (g : ι → κ → Polynomial ℝ), Finite ι ∧ Finite κ ∧
      ∀ x, f x = ⨆ i, ⨅ j, Polynomial.eval x (g i j) := by
  obtain ⟨ι, P, g, hfin, hc, -, hcov, hfg⟩ := hf
  have hcov' : ∀ x, ∃ i, x ∈ P i := by
    intro x
    have hx : x ∈ ⋃ i, P i := by rw [hcov]; exact Set.mem_univ x
    exact Set.mem_iUnion.1 hx
  obtain ⟨ι', κ, G, h1, h2, -, -, hG⟩ := PB.main P g f hc hcov' hfg
  exact ⟨ι', κ, G, h1, h2, hG⟩

end PierceBirkhoff

#print axioms PierceBirkhoff.pierce_birkhoff_conjecture_dim_one
