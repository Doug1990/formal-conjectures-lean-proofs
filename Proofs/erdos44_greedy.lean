import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

open Function Set Finset

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Erdos44

/-- Covering map: every element that cannot be added to a Sidon set `A` lies in `g '' A³`. -/
def g (t : ℕ × ℕ × ℕ) : ℕ :=
  if t.2.1 < t.1 ∧ t.2.2 = t.1 then (t.1 + t.2.1) / 2 else t.1 + t.2.1 - t.2.2

lemma insert_sidon (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (x : ℕ)
    (hx : x ∉ (A ×ˢ A ×ˢ A).image g) : IsSidon ((insert x A : Finset ℕ) : Set ℕ) := by
  have hmem : ∀ b ∈ A, ∀ c ∈ A, ∀ a ∈ A, g (b, c, a) ≠ x := by
    intro b hb c hc a ha h
    exact hx (Finset.mem_image.2 ⟨(b, c, a), by simp [hb, hc, ha], h⟩)
  have hxA : x ∉ A := by
    intro h
    exact hmem x h x h x h (by simp [g])
  have F1 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, x + a ≠ b + c := by
    intro a ha b hb c hc h
    by_cases hcb : c < b ∧ a = b
    · exact hxA (by rw [show x = c by omega]; exact hc)
    · apply hmem b hb c hc a ha
      simp only [g, hcb, if_false]
      omega
  have F2 : ∀ b ∈ A, ∀ c ∈ A, x + x ≠ b + c := by
    intro b hb c hc h
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · apply hmem b hb c hc b hb
      simp only [g, hcb, and_self, if_true]
      omega
    · exact hxA (by rw [show x = b by omega]; exact hb)
    · apply hmem c hc b hb c hc
      simp only [g, hcb, and_self, if_true]
      omega
  intro i₁ hi1 j₁ hj1 i₂ hi2 j₂ hj2 heq
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi1 hj1 hi2 hj2
  rcases hi1 with hi1 | hi1 <;> rcases hj1 with hj1 | hj1 <;>
    rcases hi2 with hi2 | hi2 <;> rcases hj2 with hj2 | hj2
  all_goals first
    | omega
    | exact hA _ hi1 _ hj1 _ hi2 _ hj2 heq
    | (exfalso; first
        | exact F1 _ hi2 _ hj1 _ hj2 (by omega)
        | exact F1 _ hi1 _ hj1 _ hj2 (by omega)
        | exact F1 _ hj2 _ hi1 _ hi2 (by omega)
        | exact F1 _ hj1 _ hi1 _ hi2 (by omega)
        | exact F2 _ hj1 _ hj2 (by omega)
        | exact F2 _ hi1 _ hi2 (by omega))

theorem greedy_sidon_construction (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3 := by
  classical
  set S := (Finset.Icc 1 N).powerset.filter (fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)) with hS
  have hne : S.Nonempty := ⟨∅, by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro i₁ hi1
    simp at hi1⟩
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hAS
  obtain ⟨hAsub, hA⟩ := hAS
  refine ⟨A, hAsub, hA, ?_⟩
  have hcov : Finset.Icc 1 N ⊆ (A ×ˢ A ×ˢ A).image g := by
    intro x hx
    by_contra hn
    have hxA : x ∉ A := by
      intro h
      exact hn (Finset.mem_image.2 ⟨(x, x, x), by simp [h], by simp [g]⟩)
    have hmem : insert x A ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hx hAsub, insert_sidon A hA x hn⟩
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hxA] at this
    omega
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_image_le (s := A ×ˢ A ×ˢ A) (f := g)
  rw [Finset.card_product, Finset.card_product] at h2
  rw [Nat.card_Icc] at h1
  have h3 : A.card * (A.card * A.card) = A.card ^ 3 := by ring
  omega

end Erdos44

#print axioms Erdos44.greedy_sidon_construction
