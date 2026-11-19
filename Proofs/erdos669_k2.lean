import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.LinearCombination

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanGeometry

noncomputable def linesWithPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | (↑L ∩ S).ncard = k }

end EuclideanGeometry

namespace Erdos669

noncomputable def linesWithAtLeastPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | k ≤ (↑L ∩ S).ncard }

noncomputable def lineCountsAtLeast (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧ (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard = m}

noncomputable def lineCountsExactly (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧
    (EuclideanGeometry.linesWithPointsFor k (S : Set ℝ²)).ncard = m}

noncomputable def maxLinesAtLeast (k n : ℕ) : ℕ :=
  sSup (lineCountsAtLeast k n)

noncomputable def maxLinesExactly (k n : ℕ) : ℕ :=
  sSup (lineCountsExactly k n)

namespace K2

open Classical

noncomputable def img (S : Finset ℝ²) : Finset (AffineSubspace ℝ ℝ²) :=
  (S.powersetCard 2).image (fun t : Finset ℝ² => affineSpan ℝ (t : Set ℝ²))

lemma sub_img (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²))
    (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ affineSpan ℝ {p, q} = L) :
    T ⊆ ↑(img S) := by
  intro L hL
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := hT L hL
  rw [img, Finset.coe_image]
  refine ⟨{p, q}, ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hpq⟩
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  · simp only [Finset.coe_pair]

lemma ub (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²))
    (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ affineSpan ℝ {p, q} = L) :
    T.ncard ≤ S.card.choose 2 := by
  refine (Set.ncard_le_ncard (sub_img S T hT) (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset, img]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_powersetCard]

noncomputable def pt (x : ℝ) : ℝ² := !₂[x, x ^ 2]

lemma pt0 (x : ℝ) : pt x 0 = x := by simp [pt]
lemma pt1 (x : ℝ) : pt x 1 = x ^ 2 := by simp [pt]

lemma pt_inj {x y : ℝ} (h : pt x = pt y) : x = y := by
  have := congrArg (fun v : ℝ² => v 0) h
  simpa [pt0] using this

lemma on_line {a b c : ℝ} (hab : a ≠ b) (h : pt c ∈ affineSpan ℝ {pt a, pt b}) :
    c = a ∨ c = b := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  rw [AffineMap.lineMap_apply_module] at hr
  have h0' := congrArg (fun v : ℝ² => v 0) hr
  have h1' := congrArg (fun v : ℝ² => v 1) hr
  have h0 : (1 - r) * a + r * b = c := by
    simpa [pt0] using h0'
  have h1 : (1 - r) * a ^ 2 + r * b ^ 2 = c ^ 2 := by
    simpa [pt1] using h1'
  have key : r * (r - 1) * (b - a) ^ 2 = 0 := by
    linear_combination ((1 - r) * a + r * b + c) * h0 - h1
  have hba : (b - a) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hab))
  rcases mul_eq_zero.mp key with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · left; rw [← h0, h3]; ring
    · right; rw [← h0, sub_eq_zero.mp h3]; ring
  · exact absurd h2 hba

noncomputable def S (n : ℕ) : Finset ℝ² := (Finset.range n).image (fun i : ℕ => pt (i : ℝ))

lemma card_S (n : ℕ) : (S n).card = n := by
  rw [S, Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  exact Nat.cast_injective (pt_inj h)

lemma mem_S {n : ℕ} {p : ℝ²} (h : p ∈ S n) : ∃ x : ℝ, p = pt x := by
  rw [S, Finset.mem_image] at h
  obtain ⟨i, -, rfl⟩ := h
  exact ⟨i, rfl⟩

lemma inter {n : ℕ} {p q : ℝ²} (hp : p ∈ S n) (hq : q ∈ S n) (hpq : p ≠ q) :
    (affineSpan ℝ {p, q} : Set ℝ²) ∩ ↑(S n) = {p, q} := by
  ext x
  constructor
  · rintro ⟨hx, hxS⟩
    obtain ⟨a, rfl⟩ := mem_S hp
    obtain ⟨b, rfl⟩ := mem_S hq
    obtain ⟨c, rfl⟩ := mem_S (Finset.mem_coe.mp hxS)
    have hab : a ≠ b := fun h => hpq (by rw [h])
    rcases on_line hab hx with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · rintro hx
    rcases hx with rfl | hx
    · exact ⟨left_mem_affineSpan_pair _ _ _, hp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨right_mem_affineSpan_pair _ _ _, hq⟩

lemma injOn (n : ℕ) : Set.InjOn (fun t : Finset ℝ² => affineSpan ℝ (t : Set ℝ²))
    ↑((S n).powersetCard 2) := by
  intro t ht t' ht' h
  rw [Finset.mem_coe, Finset.mem_powersetCard] at ht ht'
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ht.2
  obtain ⟨p', q', hpq', rfl⟩ := Finset.card_eq_two.mp ht'.2
  simp only [Finset.coe_pair] at h
  have hp : p ∈ S n := ht.1 (by simp)
  have hq : q ∈ S n := ht.1 (by simp)
  have hp' : p' ∈ S n := ht'.1 (by simp)
  have hq' : q' ∈ S n := ht'.1 (by simp)
  have e := inter hp hq hpq
  rw [h, inter hp' hq' hpq'] at e
  have e2 : (({p', q'} : Finset ℝ²) : Set ℝ²) = (({p, q} : Finset ℝ²) : Set ℝ²) := by
    simp only [Finset.coe_pair]; exact e
  exact (Finset.coe_injective e2).symm

lemma card_img (n : ℕ) : (img (S n)).card = n.choose 2 := by
  rw [img, Finset.card_image_of_injOn (injOn n), Finset.card_powersetCard, card_S]

lemma img_sub (n : ℕ) (L : AffineSubspace ℝ ℝ²) (hL : L ∈ img (S n)) :
    ∃ p ∈ S n, ∃ q ∈ S n, p ≠ q ∧ affineSpan ℝ {p, q} = L ∧
      (L : Set ℝ²) ∩ ↑(S n) = {p, q} := by
  rw [img, Finset.mem_image] at hL
  obtain ⟨t, ht, rfl⟩ := hL
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ht.2
  have hp : p ∈ S n := ht.1 (by simp)
  have hq : q ∈ S n := ht.1 (by simp)
  refine ⟨p, hp, q, hq, hpq, by simp only [Finset.coe_pair], ?_⟩
  simp only [Finset.coe_pair]
  exact inter hp hq hpq

lemma exact_eq (n : ℕ) :
    EuclideanGeometry.linesWithPointsFor 2 (S n : Set ℝ²) = ↑(img (S n)) := by
  apply Set.Subset.antisymm
  · apply sub_img
    rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, -⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  · intro L hL
    obtain ⟨p, hp, q, hq, hpq, hL1, hL2⟩ := img_sub n L hL
    refine ⟨⟨p, hp, q, hq, hpq, hL1⟩, ?_⟩
    show ((L : Set ℝ²) ∩ ↑(S n)).ncard = 2
    rw [hL2, Set.ncard_pair hpq]

lemma atLeast_eq (n : ℕ) :
    linesWithAtLeastPointsFor 2 (S n : Set ℝ²) = ↑(img (S n)) := by
  apply Set.Subset.antisymm
  · apply sub_img
    rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, -⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  · intro L hL
    obtain ⟨p, hp, q, hq, hpq, hL1, hL2⟩ := img_sub n L hL
    refine ⟨⟨p, hp, q, hq, hpq, hL1⟩, ?_⟩
    show 2 ≤ ((L : Set ℝ²) ∩ ↑(S n)).ncard
    rw [hL2, Set.ncard_pair hpq]

end K2

open K2 in
theorem erdos_669.variants.k_two (n : ℕ) :
    maxLinesExactly 2 n = n.choose 2 ∧ maxLinesAtLeast 2 n = n.choose 2 := by
  have hE : n.choose 2 ∈ lineCountsExactly 2 n :=
    ⟨S n, card_S n, by rw [exact_eq, Set.ncard_coe_finset, card_img]⟩
  have hA : n.choose 2 ∈ lineCountsAtLeast 2 n :=
    ⟨S n, card_S n, by rw [atLeast_eq, Set.ncard_coe_finset, card_img]⟩
  have bE : ∀ m ∈ lineCountsExactly 2 n, m ≤ n.choose 2 := by
    rintro _ ⟨T, hT, rfl⟩
    rw [← hT]
    apply ub
    rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, -⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  have bA : ∀ m ∈ lineCountsAtLeast 2 n, m ≤ n.choose 2 := by
    rintro _ ⟨T, hT, rfl⟩
    rw [← hT]
    apply ub
    rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, -⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  constructor
  · exact le_antisymm (csSup_le ⟨_, hE⟩ bE) (le_csSup ⟨_, bE⟩ hE)
  · exact le_antisymm (csSup_le ⟨_, hA⟩ bA) (le_csSup ⟨_, bA⟩ hA)

end Erdos669

#print axioms Erdos669.erdos_669.variants.k_two
