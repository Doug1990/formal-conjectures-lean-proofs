import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
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

namespace D2

/-- angle gap below π/3 gives cosine above 1/2 -/
lemma cos_gt (d : ℝ) (h : |d| < π / 3) : 1 / 2 < Real.cos d := by
  rw [← Real.cos_pi_div_three]
  have hpi := Real.pi_pos
  rcases le_or_gt 0 d with hd | hd
  · rw [abs_of_nonneg hd] at h
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hd (by linarith) h
  · rw [abs_of_neg hd] at h
    rw [← Real.cos_neg d]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h

lemma norm_mk (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : ‖(⟨x, y⟩ : ℂ)‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_mk,
    show x * x + y * y = x ^ 2 + y ^ 2 by ring, h, Real.sqrt_one]

lemma close (x y x' y' : ℝ) (h : x ^ 2 + y ^ 2 = 1) (h' : x' ^ 2 + y' ^ 2 = 1)
    (ha : |Complex.arg ⟨x, y⟩ - Complex.arg ⟨x', y'⟩| < π / 3) :
    (x - x') ^ 2 + (y - y') ^ 2 < 1 := by
  have n1 := norm_mk x y h
  have n2 := norm_mk x' y' h'
  have z1 : (⟨x, y⟩ : ℂ) ≠ 0 := by
    intro hz; rw [hz, norm_zero] at n1; exact zero_ne_one n1
  have z2 : (⟨x', y'⟩ : ℂ) ≠ 0 := by
    intro hz; rw [hz, norm_zero] at n2; exact zero_ne_one n2
  have c1 := Complex.cos_arg z1
  have c2 := Complex.cos_arg z2
  have s1 := Complex.sin_arg (⟨x, y⟩ : ℂ)
  have s2 := Complex.sin_arg (⟨x', y'⟩ : ℂ)
  rw [n1, div_one] at c1 s1
  rw [n2, div_one] at c2 s2
  have hc := cos_gt _ ha
  rw [Real.cos_sub, c1, c2, s1, s2] at hc
  simp only at hc
  nlinarith

/-- the angular class of a vector -/
noncomputable def cls (x y : ℝ) : ℤ := ⌈(Complex.arg ⟨x, y⟩ + π) * 3 / π⌉

lemma cls_eq (x y x' y' : ℝ) (h : cls x y = cls x' y') :
    |Complex.arg ⟨x, y⟩ - Complex.arg ⟨x', y'⟩| < π / 3 := by
  unfold cls at h
  have hpi := Real.pi_pos
  have a1 := Int.ceil_lt_add_one ((Complex.arg ⟨x, y⟩ + π) * 3 / π)
  have a2 := Int.le_ceil ((Complex.arg ⟨x, y⟩ + π) * 3 / π)
  have b1 := Int.ceil_lt_add_one ((Complex.arg ⟨x', y'⟩ + π) * 3 / π)
  have b2 := Int.le_ceil ((Complex.arg ⟨x', y'⟩ + π) * 3 / π)
  rw [h] at a1 a2
  generalize ((⌈(Complex.arg ⟨x', y'⟩ + π) * 3 / π⌉ : ℤ) : ℝ) = c at a1 a2 b1 b2
  generalize Complex.arg ⟨x, y⟩ = a at a1 a2 b1 b2 ⊢
  generalize Complex.arg ⟨x', y'⟩ = b at a1 a2 b1 b2 ⊢
  have e : ∀ t : ℝ, t * 3 / π = t / (π / 3) := by intro t; field_simp
  rw [e] at a1 a2 b1 b2
  have k : (0 : ℝ) < π / 3 := by linarith
  have ea := div_mul_cancel₀ (a + π) (ne_of_gt k)
  have eb := div_mul_cancel₀ (b + π) (ne_of_gt k)
  generalize (a + π) / (π / 3) = A at a1 a2 ea
  generalize (b + π) / (π / 3) = B at b1 b2 eb
  have h1 : (A - B) * (π / 3) < 1 * (π / 3) := mul_lt_mul_of_pos_right (by linarith) k
  have h2 : (-1) * (π / 3) < (A - B) * (π / 3) := mul_lt_mul_of_pos_right (by linarith) k
  rw [abs_lt]
  constructor <;> nlinarith

lemma cls_mem (x y : ℝ) : cls x y ∈ Icc (1 : ℤ) 6 := by
  have hpi := Real.pi_pos
  have l := Complex.neg_pi_lt_arg ⟨x, y⟩
  have u := Complex.arg_le_pi ⟨x, y⟩
  rw [Finset.mem_Icc, cls]
  constructor
  · rw [Int.one_le_ceil_iff]
    apply div_pos _ hpi
    nlinarith
  · rw [Int.ceil_le, div_le_iff₀ hpi]
    push_cast
    nlinarith

lemma cls_mem' (x y : ℝ) (hx : 0 ≤ x) : cls x y ∈ Icc (2 : ℤ) 5 := by
  have hpi := Real.pi_pos
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr (show 0 ≤ (⟨x, y⟩ : ℂ).re from hx)
  rw [abs_le] at h
  rw [Finset.mem_Icc, cls]
  constructor
  · rw [Int.le_ceil_iff, lt_div_iff₀ hpi]
    push_cast
    nlinarith
  · rw [Int.ceil_le, div_le_iff₀ hpi]
    push_cast
    nlinarith

lemma dsq (a b : ℝ^ 2) : dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- degree bound: neighbours have pairwise distinct classes -/
lemma deg_le (s : Finset (ℝ^ 2)) (hs : IsSeparated' 1 (s : Set (ℝ^ 2))) (v : ℝ^ 2)
    (T : Finset ℤ) (hT : ∀ w ∈ s, dist v w = 1 → cls (w 0 - v 0) (w 1 - v 1) ∈ T) :
    #{w ∈ s | dist v w = 1} ≤ T.card := by
  apply Finset.card_le_card_of_injOn (fun w => cls (w 0 - v 0) (w 1 - v 1))
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw
    exact hT w hw.1 hw.2
  · intro w hw w' hw' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    by_contra hne
    have sep := hs (Finset.mem_coe.mpr hw.1) (Finset.mem_coe.mpr hw'.1) hne
    simp only at sep
    rw [edist_dist, ENNReal.one_le_ofReal] at sep
    have d1 := dsq w w'
    have d2 := dsq v w
    have d3 := dsq v w'
    rw [hw.2] at d2
    rw [hw'.2] at d3
    have := close (w 0 - v 0) (w 1 - v 1) (w' 0 - v 0) (w' 1 - v 1) (by nlinarith) (by nlinarith)
      (cls_eq _ _ _ _ heq)
    nlinarith

/-- handshake: twice the number of unit pairs is at most the degree sum -/
lemma two_mul_le (s : Finset (ℝ^ 2)) :
    2 * unitDistNum s ≤ ∑ v ∈ s, #{w ∈ s | dist v w = 1} := by
  unfold unitDistNum
  have hD : ∑ v ∈ s, #{w ∈ s | dist v w = 1} = #{q ∈ s ×ˢ s | dist q.1 q.2 = 1} := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.card_filter]
  rw [hD]
  calc 2 * #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}
      = #((univ : Finset Bool) ×ˢ {p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}) := by
        rw [card_product, card_univ, Fintype.card_bool]
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn
        (fun bp : Bool × Sym2 (ℝ^ 2) => if bp.1 then bp.2.out else bp.2.out.swap)
      · rintro ⟨b, p⟩ hbp
        rw [mem_coe, mem_product, mem_filter] at hbp
        obtain ⟨-, hp1, hp2⟩ := hbp
        obtain ⟨⟨a, c⟩, hab⟩ : ∃ q, p.out = q := ⟨_, rfl⟩
        have hpe : p = s(a, c) := by rw [← Quot.out_eq p, hab]
        rw [hpe, mk_mem_sym2_iff] at hp1
        rw [hab] at hp2
        simp only at hp2
        rw [mem_coe, mem_filter, mem_product]
        cases b
        · simp only [hab, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk]
          exact ⟨⟨hp1.2, hp1.1⟩, by rw [dist_comm]; exact hp2⟩
        · simp only [hab, ↓reduceIte]
          exact ⟨hp1, hp2⟩
      · rintro ⟨b, p⟩ hbp ⟨b', q⟩ hbq heq
        rw [mem_coe, mem_product, mem_filter] at hbp hbq
        obtain ⟨⟨a, c⟩, hab⟩ : ∃ r, p.out = r := ⟨_, rfl⟩
        obtain ⟨⟨a', c'⟩, hab'⟩ : ∃ r, q.out = r := ⟨_, rfl⟩
        have hpe : p = s(a, c) := by rw [← Quot.out_eq p, hab]
        have hqe : q = s(a', c') := by rw [← Quot.out_eq q, hab']
        have hd := hbp.2.2
        rw [hab] at hd
        simp only at hd
        have hac : a ≠ c := by
          intro h; rw [h, dist_self] at hd; exact zero_ne_one hd
        simp only at heq
        rw [hab, hab'] at heq
        cases b <;> cases b' <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk, Prod.mk.injEq] at heq
        · obtain ⟨h1, h2⟩ := heq
          subst h1; subst h2
          rw [hpe, hqe]
        · exfalso
          obtain ⟨h1, h2⟩ := heq
          have : p = q := by rw [hpe, hqe, ← h1, ← h2, Sym2.eq_swap]
          rw [this, hab'] at hab
          simp only [Prod.mk.injEq] at hab
          exact hac (h2.trans hab.2)
        · exfalso
          obtain ⟨h1, h2⟩ := heq
          have : p = q := by rw [hpe, hqe, h1, h2, Sym2.eq_swap]
          rw [this, hab'] at hab
          simp only [Prod.mk.injEq] at hab
          exact hac (hab.1.symm.trans h2.symm)
        · obtain ⟨h1, h2⟩ := heq
          subst h1; subst h2
          rw [hpe, hqe]

lemma main (s : Finset (ℝ^ 2)) (hs : IsSeparated' 1 (s : Set (ℝ^ 2))) (hne : s.Nonempty) :
    2 * unitDistNum s + 2 ≤ 6 * s.card := by
  obtain ⟨m, hm, hmin⟩ := s.exists_min_image (fun v => v 0) hne
  have h1 := two_mul_le s
  rw [← Finset.add_sum_erase s _ hm] at h1
  have hm4 : #{w ∈ s | dist m w = 1} ≤ 4 := by
    have := deg_le s hs m (Icc 2 5) (fun w hw _ => cls_mem' _ _ (by linarith [hmin w hw]))
    simpa using this
  have h6 : ∀ v ∈ s.erase m, #{w ∈ s | dist v w = 1} ≤ 6 := by
    intro v _
    have := deg_le s hs v (Icc 1 6) (fun w _ _ => cls_mem _ _)
    simpa using this
  have := Finset.sum_le_card_nsmul (s.erase m) _ 6 h6
  rw [card_erase_of_mem hm, smul_eq_mul] at this
  have hc : 1 ≤ s.card := card_pos.mpr hne
  omega

end D2

theorem erdos_1084.variants.easy_upper_d2 (hn : n ≠ 0) : f 2 n < 3 * n := by
  have B : ∀ s : Finset (ℝ^ 2),
      (⨆ (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ 2))), unitDistNum s) ≤ 3 * n - 1 := by
    intro s
    apply ciSup_le'
    intro hs
    apply ciSup_le'
    intro hsep
    have hne : s.Nonempty := by rw [← card_pos, hs]; omega
    have := D2.main s hsep hne
    omega
  have h : f 2 n ≤ 3 * n - 1 := ciSup_le' B
  omega

end Erdos1084

#print axioms Erdos1084.erdos_1084.variants.easy_upper_d2
