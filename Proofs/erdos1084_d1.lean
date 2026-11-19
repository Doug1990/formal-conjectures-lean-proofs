import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.MetricSpace.Defs

open scoped Finset

/-- Restated from FormalConjecturesForMathlib/Geometry/Metric.lean. -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric
/-- Restated from FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean. -/
def IsSeparated' {X : Type*} [PseudoEMetricSpace X] (ε : ENNReal) (s : Set X) : Prop :=
  s.Pairwise (ε ≤ edist · ·)
end Metric

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open Finset Filter Metric Real

namespace Erdos1084
variable {n : ℕ}

noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

namespace D1

lemma dist_out {X : Type*} [MetricSpace X] (a b : X) :
    dist (s(a, b)).out.1 (s(a, b)).out.2 = dist a b := by
  have h : s((s(a, b)).out.1, (s(a, b)).out.2) = s(a, b) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

lemma ub {X : Type*} [MetricSpace X] (c : X → ℝ) (hc : ∀ x y, dist x y = |c x - c y|)
    (s : Finset X) : unitDistNum s ≤ s.card - 1 := by
  classical
  have cinj : ∀ x y, c x = c y → x = y := by
    intro x y h
    have := hc x y
    rw [h, sub_self, abs_zero] at this
    exact dist_eq_zero.mp this
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [unitDistNum]
  obtain ⟨m, hm, hmin⟩ := s.exists_min_image c hne
  let g : Sym2 X → X := fun p => if c p.out.1 < c p.out.2 then p.out.2 else p.out.1
  have key : ∀ p ∈ s.sym2, dist p.out.1 p.out.2 = 1 →
      g p ∈ s ∧ ∃ x ∈ s, c x = c (g p) - 1 ∧ p = s(x, g p) := by
    intro p hp1 hp2
    obtain ⟨⟨a, b⟩, hab⟩ : ∃ q, p.out = q := ⟨_, rfl⟩
    have hpe : p = s(a, b) := by rw [← Quot.out_eq p, hab]
    rw [hpe, Finset.mk_mem_sym2_iff] at hp1
    rw [hab, hc] at hp2
    simp only at hp2
    have hg : g p = if c a < c b then b else a := by simp only [g, hab]
    rw [hg]
    split_ifs with hlt
    · refine ⟨hp1.2, a, hp1.1, ?_, hpe⟩
      rw [abs_of_neg (by linarith)] at hp2
      linarith
    · refine ⟨hp1.1, b, hp1.2, ?_, ?_⟩
      · rw [abs_of_nonneg (by linarith)] at hp2
        linarith
      · rw [hpe, Sym2.eq_swap]
  unfold unitDistNum
  calc #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1} ≤ (s.erase m).card := by
        apply Finset.card_le_card_of_injOn g
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_filter] at hp
          obtain ⟨hgs, x, hx, hcx, -⟩ := key p hp.1 hp.2
          rw [Finset.mem_coe, Finset.mem_erase]
          refine ⟨?_, hgs⟩
          intro hgm
          have := hmin x hx
          rw [← hgm] at this
          linarith
        · intro p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_filter] at hp hq
          obtain ⟨-, x, -, hcx, hp'⟩ := key p hp.1 hp.2
          obtain ⟨-, y, -, hcy, hq'⟩ := key q hq.1 hq.2
          have hxy : x = y := cinj x y (by rw [hcx, hcy, hpq])
          calc p = s(x, g p) := hp'
            _ = s(y, g q) := by rw [hxy, hpq]
            _ = q := hq'.symm
    _ = s.card - 1 := Finset.card_erase_of_mem hm

lemma hc1 (x y : ℝ^ 1) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]

noncomputable def P (i : ℕ) : ℝ^ 1 := EuclideanSpace.single 0 (i : ℝ)

lemma P0 (i : ℕ) : P i 0 = i := by simp [P]

lemma P_inj {i j : ℕ} (h : P i = P j) : i = j := by
  have := congrArg (fun x : ℝ^ 1 => x 0) h
  simp only [P0] at this
  exact_mod_cast this

lemma distP (i j : ℕ) : dist (P i) (P j) = |(i : ℝ) - j| := by rw [hc1, P0, P0]

noncomputable def S (n : ℕ) : Finset (ℝ^ 1) := (range n).image P

lemma card_S (n : ℕ) : (S n).card = n := by
  rw [S, Finset.card_image_of_injective _ (fun i j h => P_inj h), card_range]

lemma sep_S (n : ℕ) : IsSeparated' 1 (S n : Set (ℝ^ 1)) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, S, Finset.mem_image] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  rw [edist_dist, distP, ENNReal.one_le_ofReal]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith

lemma lb (n : ℕ) : n - 1 ≤ unitDistNum (S n) := by
  unfold unitDistNum
  calc n - 1 = (range (n - 1)).card := (card_range _).symm
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn (fun i => s(P i, P (i + 1)))
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_range] at hi
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mk_mem_sym2_iff, dist_out, distP]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
        · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
        · push_cast
          rw [show (i : ℝ) - (i + 1) = -1 by ring, abs_neg, abs_one]
      · intro i _ j _ h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact P_inj h1
        · have := P_inj h1
          have := P_inj h2
          omega

end D1

theorem erdos_1084.variants.upper_d1 : f 1 n = n - 1 := by
  have B : ∀ s : Finset (ℝ^ 1),
      (⨆ (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ 1))), unitDistNum s) ≤ n - 1 := by
    intro s
    apply ciSup_le'
    intro hs
    apply ciSup_le'
    intro _
    rw [← hs]
    exact D1.ub (fun x => x 0) D1.hc1 s
  apply le_antisymm
  · exact ciSup_le' B
  · refine le_ciSup_of_le ⟨n - 1, by rintro _ ⟨s, rfl⟩; exact B s⟩ (D1.S n) ?_
    refine le_ciSup_of_le (Set.finite_range _).bddAbove (D1.card_S n) ?_
    refine le_ciSup_of_le (Set.finite_range _).bddAbove (D1.sep_S n) ?_
    exact D1.lb n

end Erdos1084

#print axioms Erdos1084.erdos_1084.variants.upper_d1
