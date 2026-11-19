import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Lattice.Nat

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace SimpleGraph
/-- Restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/UnitDistancePlaneGraph.lean. -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]
end SimpleGraph

open Filter SimpleGraph

namespace Erdos1066

noncomputable def g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ X : Finset ℝ², X.card = n →
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
      m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}

namespace PL

lemma dsq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma lexmin (X : Finset ℝ²) (h : X.Nonempty) :
    ∃ v ∈ X, ∀ u ∈ X, v 0 < u 0 ∨ (v 0 = u 0 ∧ v 1 ≤ u 1) := by
  classical
  obtain ⟨a, ha, hamin⟩ := X.exists_min_image (fun u => u 0) h
  have hS : (X.filter (fun u => u 0 = a 0)).Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  obtain ⟨v, hv, hvmin⟩ := (X.filter (fun u => u 0 = a 0)).exists_min_image (fun u => u 1) hS
  rw [Finset.mem_filter] at hv
  refine ⟨v, hv.1, fun u hu => ?_⟩
  rcases lt_or_eq_of_le (hamin u hu) with h1 | h1
  · left; rw [hv.2]; exact h1
  · right
    exact ⟨by rw [hv.2, h1], hvmin u (Finset.mem_filter.mpr ⟨hu, h1.symm⟩)⟩

lemma nbr_card (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y))
    (v : ℝ²) (hmin : ∀ u ∈ X, v 0 < u 0 ∨ (v 0 = u 0 ∧ v 1 ≤ u 1)) :
    (X.filter (fun u => dist v u = 1)).card ≤ 3 := by
  classical
  by_contra hc
  push Not at hc
  set N := X.filter (fun u => dist v u = 1) with hNdef
  let θ : ℝ² → ℝ := fun u => Real.arcsin (u 1 - v 1)
  have key : ∀ u ∈ N, -(Real.pi / 2) < θ u ∧ θ u ≤ Real.pi / 2 ∧
      Real.cos (θ u) = u 0 - v 0 ∧ Real.sin (θ u) = u 1 - v 1 ∧
      (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = 1 := by
    intro u hu
    rw [hNdef, Finset.mem_filter] at hu
    obtain ⟨huX, hd⟩ := hu
    have h1 : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = 1 := by
      have := dsq v u
      rw [hd] at this
      linear_combination -this
    have h0 : 0 ≤ u 0 - v 0 := by rcases hmin u huX with h | ⟨h, _⟩ <;> linarith
    have hy : (u 1 - v 1) ^ 2 ≤ 1 := by linarith [sq_nonneg (u 0 - v 0)]
    have hy' := abs_le.mp (sq_le_one_iff_abs_le_one _ |>.mp hy)
    have hy1 : -1 ≤ u 1 - v 1 := hy'.1
    have hy2 : u 1 - v 1 ≤ 1 := hy'.2
    have hgt : -1 < u 1 - v 1 := by
      rcases hmin u huX with h | ⟨h, h'⟩
      · by_contra hc
        push Not at hc
        have e : u 1 - v 1 = -1 := le_antisymm hc hy1
        have e2 : (u 0 - v 0) ^ 2 = 0 := by rw [e] at h1; linarith
        have e3 : u 0 - v 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
        linarith
      · linarith
    refine ⟨Real.neg_pi_div_two_lt_arcsin.mpr hgt, Real.arcsin_le_pi_div_two _, ?_,
      Real.sin_arcsin hy1 hy2, h1⟩
    show Real.cos (Real.arcsin (u 1 - v 1)) = u 0 - v 0
    rw [Real.cos_arcsin]
    have : 1 - (u 1 - v 1) ^ 2 = (u 0 - v 0) ^ 2 := by linarith
    rw [this, Real.sqrt_sq h0]
  have hsep : ∀ u ∈ N, ∀ u' ∈ N, u ≠ u' → Real.pi / 3 ≤ |θ u - θ u'| := by
    intro u hu u' hu' hne
    obtain ⟨-, -, c1, s1, n1⟩ := key u hu
    obtain ⟨-, -, c2, s2, n2⟩ := key u' hu'
    have hd : 1 ≤ dist u u' :=
      hX (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 hne
    have hsq : 1 ≤ (u 0 - u' 0) ^ 2 + (u 1 - u' 1) ^ 2 := by
      rw [← dsq]; exact one_le_pow₀ hd
    have e : (u 0 - u' 0) ^ 2 + (u 1 - u' 1) ^ 2 =
        ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2) + ((u' 0 - v 0) ^ 2 + (u' 1 - v 1) ^ 2) -
          2 * ((u 0 - v 0) * (u' 0 - v 0) + (u 1 - v 1) * (u' 1 - v 1)) := by ring
    rw [n1, n2] at e
    have hcos : Real.cos (θ u - θ u') ≤ 1 / 2 := by
      rw [Real.cos_sub, c1, c2, s1, s2]
      linarith
    by_contra hlt
    push Not at hlt
    have : 1 / 2 < Real.cos (θ u - θ u') := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) hlt
    linarith
  have hp : 0 < Real.pi / 3 := by linarith [Real.pi_pos]
  let f : ℝ² → ℤ := fun u => ⌈(θ u + Real.pi / 2) / (Real.pi / 3)⌉
  have hmaps : Set.MapsTo f N (Finset.Icc (1 : ℤ) 3) := by
    intro u hu
    obtain ⟨a1, a2, -, -, -⟩ := key u hu
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · have : 0 < (θ u + Real.pi / 2) / (Real.pi / 3) := div_pos (by linarith) hp
      have := Int.ceil_pos.mpr this
      show (1 : ℤ) ≤ ⌈(θ u + Real.pi / 2) / (Real.pi / 3)⌉
      omega
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ hp]
      push_cast
      linarith
  have hcard : (Finset.Icc (1 : ℤ) 3).card < N.card := by
    simp only [Int.card_Icc]
    omega
  obtain ⟨u, hu, u', hu', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hs := hsep u hu u' hu' hne
  set a := (θ u + Real.pi / 2) / (Real.pi / 3) with ha
  set b := (θ u' + Real.pi / 2) / (Real.pi / 3) with hb
  have ha1 : a ≤ (f u : ℝ) := Int.le_ceil a
  have ha2 : (f u : ℝ) < a + 1 := Int.ceil_lt_add_one a
  have hb1 : b ≤ (f u' : ℝ) := Int.le_ceil b
  have hb2 : (f u' : ℝ) < b + 1 := Int.ceil_lt_add_one b
  rw [heq] at ha1 ha2
  have hab : |a - b| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hθ : θ u - θ u' = (a - b) * (Real.pi / 3) := by
    rw [sub_mul, ha, hb, div_mul_cancel₀ _ hp.ne', div_mul_cancel₀ _ hp.ne']; ring
  rw [hθ, abs_mul, abs_of_pos hp] at hs
  have := mul_lt_of_lt_one_left hp hab
  linarith

theorem main : ∀ (k : ℕ) (X : Finset ℝ²), X.card = k →
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
    ∃ I ⊆ X, (I : Set ℝ²).Pairwise (fun x y ↦ dist x y ≠ 1) ∧ X.card ≤ 4 * I.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X hk hX
  classical
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨v, hv, hmin⟩ := lexmin X hne
  have hN := nbr_card X hX v hmin
  set N := X.filter (fun u => dist v u = 1) with hNdef
  set X' := X \ insert v N with hX'def
  have hX'sub : X' ⊆ X := Finset.sdiff_subset
  have hvX' : v ∉ X' := by
    rw [hX'def, Finset.mem_sdiff, not_and, not_not]
    intro _; exact Finset.mem_insert_self _ _
  have hlt : X'.card < k := by
    rw [← hk]
    exact Finset.card_lt_card ⟨hX'sub, fun h => hvX' (h hv)⟩
  have hge : X.card ≤ X'.card + 4 := by
    have h1 : X.card ≤ X'.card + (insert v N).card := Finset.card_le_card_sdiff_add_card
    have h2 := Finset.card_insert_le v N
    omega
  obtain ⟨I', hI'sub, hI'pw, hI'card⟩ :=
    ih _ hlt X' rfl (hX.mono (Finset.coe_subset.mpr hX'sub))
  have hvI' : v ∉ I' := fun h => hvX' (hI'sub h)
  refine ⟨insert v I', Finset.insert_subset hv (hI'sub.trans hX'sub), ?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hI'pw.insert ?_
    intro b hb _
    have hbX' : b ∈ X' := hI'sub hb
    rw [hX'def, Finset.mem_sdiff, Finset.mem_insert, not_or] at hbX'
    have : dist v b ≠ 1 := fun h => hbX'.2.2 (Finset.mem_filter.mpr ⟨hbX'.1, h⟩)
    exact ⟨this, by rwa [dist_comm]⟩
  · rw [Finset.card_insert_of_notMem hvI']
    omega

lemma indep_le (Y : Finset ℝ²) : (UnitDistancePlaneGraph (Y : Set ℝ²)).indepNum ≤ Y.card := by
  classical
  obtain ⟨s, hs⟩ := (UnitDistancePlaneGraph (Y : Set ℝ²)).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  calc s.card = (s.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
    _ ≤ Y.card := Finset.card_le_card (fun x hx => by
        rw [Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2)

noncomputable def P (i : ℕ) : ℝ² := EuclideanSpace.single 0 (i : ℝ)

lemma P0 (i : ℕ) : P i 0 = i := by simp [P]
lemma P1 (i : ℕ) : P i 1 = 0 := by simp [P]

lemma P_inj {i j : ℕ} (h : P i = P j) : i = j := by
  have := congrArg (fun x : ℝ² => x 0) h
  simp only [P0] at this
  exact_mod_cast this

noncomputable def S (n : ℕ) : Finset ℝ² := (Finset.range n).image P

lemma card_S (n : ℕ) : (S n).card = n := by
  rw [S, Finset.card_image_of_injective _ (fun i j h => P_inj h), Finset.card_range]

lemma sep_S (n : ℕ) : (S n : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, S, Finset.mem_image] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  have hd := dsq (P i) (P j)
  rw [P0, P0, P1, P1] at hd
  have h1 : 1 ≤ ((i : ℝ) - j) ^ 2 := by
    rw [one_le_sq_iff_one_le_abs, le_abs]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      right; linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      left; linarith
  have h2 : 1 ≤ dist (P i) (P j) ^ 2 := by
    rw [hd]; linarith [sq_nonneg ((0 : ℝ) - 0)]
  rw [one_le_sq_iff_one_le_abs, abs_of_nonneg dist_nonneg] at h2
  exact h2

lemma indep_ge (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    (X.card + 3) / 4 ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum := by
  classical
  obtain ⟨I, hIX, hIpw, hIc⟩ := main _ X rfl hX
  have ht : (UnitDistancePlaneGraph (X : Set ℝ²)).IsIndepSet
      (I.subtype (fun x => x ∈ (X : Set ℝ²))) := by
    intro a ha b hb hab hadj
    change dist a b = 1 at hadj
    rw [Subtype.dist_eq] at hadj
    rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
    exact hIpw ha hb (fun h => hab (Subtype.ext h)) hadj
  have hc : (I.subtype (fun x => x ∈ (X : Set ℝ²))).card = I.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => Finset.mem_coe.mpr (hIX hx))]
  have := ht.card_le_indepNum
  rw [hc] at this
  omega

end PL
end Erdos1066
namespace Erdos1066
theorem erdos_1066.variants.pollack (n : ℕ) : (n : ℝ) / 4 ≤ (g n : ℝ) := by
  classical
  have hmem : (n + 3) / 4 ∈ {m : ℕ | ∀ X : Finset ℝ², X.card = n →
      (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
        m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum} := by
    intro X hXc hX
    have := PL.indep_ge X hX
    rw [hXc] at this
    exact this
  have hbdd : BddAbove {m : ℕ | ∀ X : Finset ℝ², X.card = n →
      (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
        m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum} := by
    refine ⟨n, fun m hm => ?_⟩
    have := hm (PL.S n) (PL.card_S n) (PL.sep_S n)
    have h2 := PL.indep_le (PL.S n)
    rw [PL.card_S] at h2
    omega
  have h1 : (n + 3) / 4 ≤ g n := le_csSup hbdd hmem
  have h2 : n ≤ 4 * ((n + 3) / 4) := by omega
  have h3 : (n : ℝ) ≤ 4 * (((n + 3) / 4 : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : (((n + 3) / 4 : ℕ) : ℝ) ≤ (g n : ℝ) := by exact_mod_cast h1
  linarith

end Erdos1066

#print axioms Erdos1066.erdos_1066.variants.pollack
