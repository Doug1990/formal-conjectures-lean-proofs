import Mathlib.Topology.Bases
import Mathlib.Data.Finset.Lattice.Fold

open TopologicalSpace Topology Filter

namespace WeaklyFirstCountable

class WeaklyFirstCountableTopology (X : Type*) [TopologicalSpace X] : Prop where
  nhds_countable_weak_basis :
    ∃ V : X → ℕ → Set X,
      (∀ (x : X), Antitone (V x) ∧ ∀ (n : ℕ), x ∈ V x n) ∧
        ∀ O : Set X, IsOpen O ↔ ∀ x ∈ O, ∃ k : ℕ, V x k ⊆ O

/-- Arens-type space: a top point, a sequence of middle points, and below each middle point a
sequence of isolated points. -/
inductive A
  | top
  | mid (i : ℕ)
  | low (i j : ℕ)

def V : A → ℕ → Set A
  | .top, n => {y | y = .top ∨ ∃ i, n ≤ i ∧ y = .mid i}
  | .mid i, n => {y | y = .mid i ∨ ∃ j, n ≤ j ∧ y = .low i j}
  | .low i j, _ => {y | y = .low i j}

lemma mem_V_top {n : ℕ} {y : A} : y ∈ V .top n ↔ y = .top ∨ ∃ i, n ≤ i ∧ y = .mid i := Iff.rfl

lemma mem_V_mid {i n : ℕ} {y : A} :
    y ∈ V (.mid i) n ↔ y = .mid i ∨ ∃ j, n ≤ j ∧ y = .low i j := Iff.rfl

lemma mem_V_low {i j n : ℕ} {y : A} : y ∈ V (.low i j) n ↔ y = .low i j := Iff.rfl

lemma V_anti (x : A) : Antitone (V x) := by
  intro a b hab y hy
  cases x with
  | top =>
    rw [mem_V_top] at hy ⊢
    rcases hy with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, le_trans hab hi, h⟩
  | mid i =>
    rw [mem_V_mid] at hy ⊢
    rcases hy with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, le_trans hab hj, h⟩
  | low i j =>
    rw [mem_V_low] at hy ⊢
    exact hy

lemma V_mem (x : A) (n : ℕ) : x ∈ V x n := by
  cases x with
  | top => exact mem_V_top.2 (Or.inl rfl)
  | mid i => exact mem_V_mid.2 (Or.inl rfl)
  | low i j => exact mem_V_low.2 rfl

instance : TopologicalSpace A where
  IsOpen O := ∀ x ∈ O, ∃ k, V x k ⊆ O
  isOpen_univ := fun _ _ => ⟨0, Set.subset_univ _⟩
  isOpen_inter := fun s t hs ht x hx => by
    obtain ⟨a, ha⟩ := hs x hx.1
    obtain ⟨b, hb⟩ := ht x hx.2
    exact ⟨max a b, Set.subset_inter ((V_anti x (le_max_left a b)).trans ha)
      ((V_anti x (le_max_right a b)).trans hb)⟩
  isOpen_sUnion := fun S hS x hx => by
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨k, hk⟩ := hS s hsS x hxs
    exact ⟨k, hk.trans (Set.subset_sUnion_of_mem hsS)⟩

lemma isOpen_A {O : Set A} : IsOpen O ↔ ∀ x ∈ O, ∃ k, V x k ⊆ O := Iff.rfl

lemma not_fc : ¬ FirstCountableTopology A := by
  intro hfc
  have := hfc.nhds_generated_countable A.top
  obtain ⟨u, hu⟩ := (𝓝 A.top).exists_antitone_basis
  have hO : ∀ m, ∃ O : Set A, IsOpen O ∧ A.top ∈ O ∧ O ⊆ u m := fun m => by
    obtain ⟨O, hOu, hOo, hOt⟩ := mem_nhds_iff.1 (hu.mem m)
    exact ⟨O, hOo, hOt, hOu⟩
  choose O hOo hOt hOu using hO
  have hn : ∀ m, ∃ n, V A.top n ⊆ O m := fun m => isOpen_A.1 (hOo m) _ (hOt m)
  choose n hn using hn
  have hk : ∀ m i, ∃ k, A.mid i ∈ O m → V (A.mid i) k ⊆ O m := by
    intro m i
    by_cases h : A.mid i ∈ O m
    · obtain ⟨k, hk⟩ := isOpen_A.1 (hOo m) _ h
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose k hk using hk
  obtain ⟨h, hle⟩ : ∃ h : ℕ → ℕ, ∀ m i, m ≤ i → k m i ≤ h i :=
    ⟨fun i => (Finset.range (i + 1)).sup (fun m => k m i), fun m i hmi =>
      Finset.le_sup (f := fun m => k m i) (Finset.mem_range.2 (by omega))⟩
  let W : Set A := {y | ∀ i j, y = A.low i j → h i < j}
  have hW : IsOpen W := by
    rw [isOpen_A]
    intro x hx
    cases x with
    | top =>
      refine ⟨0, fun y hy => ?_⟩
      rw [mem_V_top] at hy
      rcases hy with rfl | ⟨i, -, rfl⟩
      · intro a b hab; cases hab
      · intro a b hab; cases hab
    | mid i =>
      refine ⟨h i + 1, fun y hy => ?_⟩
      rw [mem_V_mid] at hy
      rcases hy with rfl | ⟨j, hj, rfl⟩
      · intro a b hab; cases hab
      · intro a b hab
        cases hab
        omega
    | low i j =>
      refine ⟨0, fun y hy => ?_⟩
      rw [mem_V_low] at hy
      rw [hy]
      exact hx
  have hWt : A.top ∈ W := by
    intro a b hab
    cases hab
  obtain ⟨m, hm⟩ := hu.mem_iff.1 (hW.mem_nhds hWt)
  have hi : A.mid (max m (n m)) ∈ O m :=
    hn m (mem_V_top.2 (Or.inr ⟨_, le_max_right _ _, rfl⟩))
  have hlow : A.low (max m (n m)) (h (max m (n m))) ∈ O m :=
    hk m _ hi (mem_V_mid.2 (Or.inr ⟨_, hle m _ (le_max_left _ _), rfl⟩))
  exact lt_irrefl _ (hm (hOu m hlow) _ _ rfl)

theorem exists_weakly_first_countable_not_first_countable : ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ ¬ FirstCountableTopology X :=
  ⟨A, inferInstance, ⟨⟨V, fun x => ⟨V_anti x, V_mem x⟩, fun _ => Iff.rfl⟩⟩, not_fc⟩

end WeaklyFirstCountable

#print axioms WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable
