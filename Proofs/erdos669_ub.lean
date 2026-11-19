import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp

open Filter
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Erdos669

noncomputable def linesWithAtLeastPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | k ≤ (↑L ∩ S).ncard }

noncomputable def lineCountsAtLeast (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧ (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard = m}

noncomputable def maxLinesAtLeast (k n : ℕ) : ℕ :=
  sSup (lineCountsAtLeast k n)

namespace UB

lemma line_eq {a b p q : ℝ²} (hab : a ≠ b) (hpq : p ≠ q) (hp : p ∈ affineSpan ℝ {a, b})
    (hq : q ∈ affineSpan ℝ {a, b}) : affineSpan ℝ {p, q} = affineSpan ℝ {a, b} := by
  have hle : affineSpan ℝ {p, q} ≤ affineSpan ℝ {a, b} := affineSpan_pair_le_of_mem_of_mem hp hq
  refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_ ?_ hle
  · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair,
      finrank_span_singleton (vsub_ne_zero.mpr hpq), finrank_span_singleton (vsub_ne_zero.mpr hab)]
  · exact ⟨p, mem_affineSpan ℝ (Set.mem_insert _ _)⟩

lemma fin (k : ℕ) (S : Finset ℝ²) : (linesWithAtLeastPointsFor k (S : Set ℝ²)).Finite := by
  refine ((S.finite_toSet.prod S.finite_toSet).image
    (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
  rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
  exact ⟨(p, q), Set.mk_mem_prod hp hq, rfl⟩

open Classical in
lemma count (k : ℕ) (S : Finset ℝ²) :
    (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard * k.choose 2 ≤ S.card.choose 2 := by
  rw [Set.ncard_eq_toFinset_card _ (fin k S)]
  set T := (fin k S).toFinset with hT
  let P : AffineSubspace ℝ ℝ² → Finset (Finset ℝ²) := fun L =>
    (S.filter (· ∈ L)).powersetCard 2
  have hcardP : ∀ L ∈ T, k.choose 2 ≤ (P L).card := by
    intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    have h2 : k ≤ ((L : Set ℝ²) ∩ (S : Set ℝ²)).ncard := hL.2
    have e : ((L : Set ℝ²) ∩ (S : Set ℝ²)).ncard = (S.filter (· ∈ L)).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp only [Finset.coe_filter, Set.mem_inter_iff, SetLike.mem_coe]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    show k.choose 2 ≤ ((S.filter (· ∈ L)).powersetCard 2).card
    rw [Finset.card_powersetCard]
    apply Nat.choose_le_choose
    omega
  have hdisj : (T : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint P := by
    intro L hL L' hL' hne
    show Disjoint (P L) (P L')
    rw [Finset.disjoint_left]
    intro e he he'
    apply hne
    rw [Finset.mem_powersetCard] at he he'
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp he.2
    have mp : p ∈ ({p, q} : Finset ℝ²) := Finset.mem_insert_self p {q}
    have mq : q ∈ ({p, q} : Finset ℝ²) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    have hp : p ∈ L := (Finset.mem_filter.mp (he.1 mp)).2
    have hq : q ∈ L := (Finset.mem_filter.mp (he.1 mq)).2
    have hp' : p ∈ L' := (Finset.mem_filter.mp (he'.1 mp)).2
    have hq' : q ∈ L' := (Finset.mem_filter.mp (he'.1 mq)).2
    have hL1 := (Set.Finite.mem_toFinset _).mp (Finset.mem_coe.mp hL)
    have hL2 := (Set.Finite.mem_toFinset _).mp (Finset.mem_coe.mp hL')
    obtain ⟨⟨a, -, b, -, hab, rfl⟩, -⟩ := hL1
    obtain ⟨⟨a', -, b', -, hab', rfl⟩, -⟩ := hL2
    rw [← line_eq hab hpq hp hq, ← line_eq hab' hpq hp' hq']
  have hsub : T.biUnion P ⊆ S.powersetCard 2 := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨L, -, he⟩ := he
    have he2 : e ∈ (S.filter (· ∈ L)).powersetCard 2 := he
    rw [Finset.mem_powersetCard] at he2 ⊢
    exact ⟨he2.1.trans (Finset.filter_subset _ _), he2.2⟩
  calc T.card * k.choose 2 = ∑ L ∈ T, k.choose 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ L ∈ T, (P L).card := Finset.sum_le_sum hcardP
    _ = (T.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (S.powersetCard 2).card := Finset.card_le_card hsub
    _ = S.card.choose 2 := Finset.card_powersetCard _ _

lemma upper_nat (k n : ℕ) (hk : 2 ≤ k) : maxLinesAtLeast k n ≤ n.choose 2 / k.choose 2 := by
  have hpos : 0 < k.choose 2 := Nat.choose_pos hk
  refine csSup_le' ?_
  rintro _ ⟨S, rfl, rfl⟩
  rw [Nat.le_div_iff_mul_le hpos]
  exact count k S

end UB

theorem erdos_669.variants.upper_bound (k n : ℕ) (hk : 2 ≤ k) :
    (maxLinesAtLeast k n : ℝ) ≤ (n.choose 2 : ℝ) / (k.choose 2 : ℝ) :=
  (Nat.cast_le.mpr (UB.upper_nat k n hk)).trans Nat.cast_div_le

theorem erdos_669.variants.limit_le (k : ℕ) (hk : 2 ≤ k) (L : ℝ)
    (hL : Tendsto (fun n : ℕ => (maxLinesAtLeast k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 L)) :
    L ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k * (k - 1) := by nlinarith
  apply le_of_tendsto' hL
  intro n
  have h1 := erdos_669.variants.upper_bound k n hk
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show ((0 : ℕ) : ℝ) ^ 2 = 0 by simp, div_zero]
    exact (one_div_pos.mpr hk0).le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : (maxLinesAtLeast k n : ℝ) ≤ n * (n - 1) / (k * (k - 1)) := by
    have e : (n : ℝ) * (n - 1) / 2 / (k * (k - 1) / 2) = n * (n - 1) / (k * (k - 1)) := by
      rw [div_div_div_cancel_right₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    rw [← e]
    exact h1
  rw [le_div_iff₀ hk0] at hF
  rw [div_le_div_iff₀ (pow_pos hn' 2) hk0]
  nlinarith

end Erdos669

#print axioms Erdos669.erdos_669.variants.upper_bound
#print axioms Erdos669.erdos_669.variants.limit_le
