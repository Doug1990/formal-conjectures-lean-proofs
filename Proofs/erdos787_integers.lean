import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/-- Local copy of FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean. -/
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Erdos787

noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

theorem disjoint_restrictedSumset_iff {G : Type*} [Add G] [DecidableEq G] (A B : Finset G) :
    Disjoint B.restrictedSumset A ↔ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A := by
  unfold Finset.restrictedSumset
  rw [Finset.disjoint_left]
  constructor
  · intro h b₁ hb₁ b₂ hb₂ hne hmem
    have hmem' : b₁ + b₂ ∈ Finset.image (fun p : G × G => p.1 + p.2) B.offDiag :=
      Finset.mem_image.2 ⟨(b₁, b₂), Finset.mem_offDiag.2 ⟨hb₁, hb₂, hne⟩, rfl⟩
    exact h hmem' hmem
  · intro h x hx hxA
    obtain ⟨⟨b₁, b₂⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hb₁, hb₂, hne⟩ := Finset.mem_offDiag.1 hp
    exact h b₁ hb₁ b₂ hb₂ hne hxA

namespace IZ

/-- Pull a good subset back along a map that is injective on `A` and preserves the
relations `x + y = z` inside `A`. -/
lemma pull {α β : Type*} [Add α] [Add β] [DecidableEq α] [DecidableEq β]
    (A : Finset α) (e : α → β) (hinj : Set.InjOn e A)
    (hrel : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A → e (x + y) = e x + e y) {m : ℕ}
    (h : ∃ B' ⊆ A.image e, m ≤ B'.card ∧ Disjoint B'.restrictedSumset (A.image e)) :
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A := by
  obtain ⟨B', hB'A, hm, hdis⟩ := h
  rw [disjoint_restrictedSumset_iff] at hdis
  refine ⟨A.filter (fun a => e a ∈ B'), Finset.filter_subset _ _, ?_, ?_⟩
  · have hsub : B' ⊆ (A.filter (fun a => e a ∈ B')).image e := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hB'A hb)
      exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hb⟩, rfl⟩
    exact hm.trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  · rw [disjoint_restrictedSumset_iff]
    intro b₁ hb₁ b₂ hb₂ hne hmem
    obtain ⟨hb₁A, hb₁'⟩ := Finset.mem_filter.1 hb₁
    obtain ⟨hb₂A, hb₂'⟩ := Finset.mem_filter.1 hb₂
    refine hdis (e b₁) hb₁' (e b₂) hb₂' (fun h => hne (hinj hb₁A hb₂A h)) ?_
    rw [← hrel b₁ hb₁A b₂ hb₂A hmem]
    exact Finset.mem_image.2 ⟨_, hmem, rfl⟩

/-- A ℚ-linear functional on ℝ that does not vanish on a given finite set of nonzero reals. -/
lemma sep (D : Finset ℝ) : (0 : ℝ) ∉ D → ∃ f : ℝ →ₗ[ℚ] ℚ, ∀ w ∈ D, f w ≠ 0 := by
  induction D using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp⟩
  | @insert v D hvD ih =>
    intro h0
    obtain ⟨f, hf⟩ := ih (fun h => h0 (Finset.mem_insert_of_mem h))
    have hv : v ≠ 0 := fun h => h0 (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℚ hv
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset ((insert v D).image (fun w => -f w / g w))
    refine ⟨f + q • g, ?_⟩
    intro w hw hzero
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hzero
    by_cases hgw : g w = 0
    · rw [hgw, mul_zero, add_zero] at hzero
      rcases Finset.mem_insert.1 hw with hw' | hw'
      · rw [hw'] at hgw; exact hg hgw
      · exact hf w hw' hzero
    · apply hq
      refine Finset.mem_image.2 ⟨w, hw, ?_⟩
      show -f w / g w = q
      rw [div_eq_iff hgw]
      linarith

lemma den_mul (q : ℚ) : (q.den : ℚ) * q = q.num := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have h := Rat.num_div_den q
  calc (q.den : ℚ) * q = q.den * (q.num / q.den) := by rw [h]
    _ = q.num := by field_simp

/-- A common denominator. -/
lemma common (S : Finset ℚ) : ∃ d : ℕ, 0 < d ∧ ∀ q ∈ S, ∃ z : ℤ, (z : ℚ) = d * q := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert q S hqS ih =>
    obtain ⟨d, hd, hS⟩ := ih
    refine ⟨d * q.den, Nat.mul_pos hd q.den_pos, ?_⟩
    intro r hr
    rcases Finset.mem_insert.1 hr with hr | hr
    · refine ⟨d * q.num, ?_⟩
      rw [hr]; push_cast
      rw [mul_assoc, den_mul]
    · obtain ⟨z, hz⟩ := hS r hr
      refine ⟨z * q.den, ?_⟩
      push_cast
      rw [hz]; ring

/-- Every finite set of reals has an additive, injective image in ℤ. -/
lemma to_int (A : Finset ℝ) : ∃ e : ℝ → ℤ, Set.InjOn e A ∧
    ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A → e (x + y) = e x + e y := by
  classical
  obtain ⟨f, hf⟩ := sep ((A.offDiag).image (fun p => p.1 - p.2)) (by
    intro h
    obtain ⟨p, hp, hp0⟩ := Finset.mem_image.1 h
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.1 hp
    exact hne (sub_eq_zero.1 hp0))
  obtain ⟨d, hd, hdS⟩ := common (A.image f)
  have hex : ∀ a ∈ A, ∃ z : ℤ, (z : ℚ) = d * f a := fun a ha =>
    hdS (f a) (Finset.mem_image.2 ⟨a, ha, rfl⟩)
  let e : ℝ → ℤ := fun a => if h : ∃ z : ℤ, (z : ℚ) = d * f a then h.choose else 0
  have he : ∀ a ∈ A, (e a : ℚ) = d * f a := by
    intro a ha
    have h := hex a ha
    simp only [e, dif_pos h]
    exact h.choose_spec
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  refine ⟨e, ?_, ?_⟩
  · intro a ha b hb hab
    by_contra hne
    have h1 : (e a : ℚ) = e b := by rw [hab]
    rw [he a ha, he b hb] at h1
    have h2 : f (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact mul_left_cancel₀ hd0 h1
    exact hf (a - b) (Finset.mem_image.2 ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hne⟩, rfl⟩) h2
  · intro x hx y hy hxy
    have h : ((e (x + y) : ℤ) : ℚ) = ((e x + e y : ℤ) : ℚ) := by
      push_cast
      rw [he _ hxy, he x hx, he y hy, map_add]
      ring
    exact_mod_cast h

end IZ

theorem erdos_787.variants.integers (n : ℕ) : g ℤ n = g ℝ n := by
  unfold g
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h A hA
    obtain ⟨e, hinj, hadd⟩ := IZ.to_int A
    have hcard : (A.image e).card = n := by
      rw [Finset.card_image_of_injOn hinj, hA]
    exact IZ.pull A e hinj hadd (h _ hcard)
  · intro h A hA
    have hinj : Set.InjOn (fun z : ℤ => (z : ℝ)) A := fun a _ b _ hab => Int.cast_injective hab
    have hcard : (A.image (fun z : ℤ => (z : ℝ))).card = n := by
      rw [Finset.card_image_of_injOn hinj, hA]
    exact IZ.pull A _ hinj (fun x _ y _ _ => Int.cast_add x y) (h _ hcard)

end Erdos787

#print axioms Erdos787.erdos_787.variants.integers
