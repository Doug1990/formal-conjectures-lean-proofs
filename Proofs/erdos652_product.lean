import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical in
noncomputable def distinctDistancesFrom {X : Type*} [MetricSpace X] (points : Finset X)
    (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

namespace Erdos652

namespace Prod2

lemma fib {p q : ℝ²} (hpq : p ≠ q) (F : Finset ℝ²) (r s : ℝ)
    (hF : ∀ x ∈ F, dist x p = r ∧ dist x q = s) : F.card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  have := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) hpq hab
    (hF a ha).1 (hF b hb).1 (hF c hc).1 (hF a ha).2 (hF b hb).2 (hF c hc).2
  rcases this with h1 | h1
  · exact hac h1.symm
  · exact hbc h1.symm

lemma dDF_eq (points : Finset ℝ²) (p : ℝ²) :
    distinctDistancesFrom points p = #((points.erase p).image fun x => dist x p) := by
  unfold distinctDistancesFrom
  congr 2
  ext x
  simp only [Finset.mem_erase]

lemma main (points : Finset ℝ²) {p q : ℝ²} (hp : p ∈ points) (hq : q ∈ points)
    (hpq : p ≠ q) :
    points.card ≤ 4 * (distinctDistancesFrom points p * distinctDistancesFrom points q) := by
  set s := (points.erase p).erase q with hs
  let f : ℝ² → ℝ × ℝ := fun x => (dist x p, dist x q)
  have h1 := Finset.card_le_mul_card_image s 2 (f := f) (by
    intro a _
    refine fib hpq _ a.1 a.2 ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [← hx.2]
    exact ⟨rfl, rfl⟩)
  have hsub : s.image f ⊆ ((points.erase p).image fun x => dist x p) ×ˢ
      ((points.erase q).image fun x => dist x q) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hs, Finset.mem_erase, Finset.mem_erase] at hx
    rw [Finset.mem_product]
    refine ⟨Finset.mem_image.mpr ⟨x, ?_, rfl⟩, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
    · exact Finset.mem_erase.mpr ⟨hx.2.1, hx.2.2⟩
    · exact Finset.mem_erase.mpr ⟨hx.1, hx.2.2⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_product] at h2
  have hRp : 1 ≤ distinctDistancesFrom points p := by
    rw [dDF_eq]
    exact Finset.card_pos.mpr ⟨_, Finset.mem_image.mpr
      ⟨q, Finset.mem_erase.mpr ⟨hpq.symm, hq⟩, rfl⟩⟩
  have hRq : 1 ≤ distinctDistancesFrom points q := by
    rw [dDF_eq]
    exact Finset.card_pos.mpr ⟨_, Finset.mem_image.mpr
      ⟨p, Finset.mem_erase.mpr ⟨hpq, hp⟩, rfl⟩⟩
  have hcard : points.card = s.card + 2 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩),
      Finset.card_erase_of_mem hp]
    have : 2 ≤ points.card := by
      have h := Finset.card_le_card (Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hq))
      rwa [Finset.card_pair hpq] at h
    omega
  have h3 : s.card ≤ 2 * (distinctDistancesFrom points p * distinctDistancesFrom points q) := by
    rw [dDF_eq, dDF_eq]
    exact h1.trans (Nat.mul_le_mul_left 2 h2)
  have h4 : 1 ≤ distinctDistancesFrom points p * distinctDistancesFrom points q :=
    Nat.mul_le_mul hRp hRq
  omega

end Prod2

theorem erdos_652.variants.product :
    ∃ c : ℝ, 0 < c ∧ ∀ points : Finset ℝ²,
      ∀ p ∈ points, ∀ q ∈ points, p ≠ q →
        c * points.card ≤
          (distinctDistancesFrom points p : ℝ) * distinctDistancesFrom points q := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro points p hp q hq hpq
  have h := Prod2.main points hp hq hpq
  have h' : (points.card : ℝ) ≤ 4 * ((distinctDistancesFrom points p : ℝ) *
      distinctDistancesFrom points q) := by exact_mod_cast h
  linarith

end Erdos652

#print axioms Erdos652.erdos_652.variants.product
