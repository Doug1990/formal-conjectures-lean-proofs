import Mathlib.Data.Set.Card
import Mathlib.Order.Monotone.Basic

namespace Erdos602

def IsMonochromatic {α : Type*} (f : α → Fin 2) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

def HasPropertyB {α : Type*} (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → Fin 2, ∀ i, ¬IsMonochromatic f (A i)

/-- Bernstein's lemma: every sequence of infinite sets has Property B. -/
lemma bernstein {α : Type*} (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) :
    HasPropertyB ℕ A := by
  classical
  have h2 : ∀ (n : ℕ) (F : Finset α), ∃ p : α × α,
      p.1 ∈ A n ∧ p.2 ∈ A n ∧ p.1 ≠ p.2 ∧ p.1 ∉ F ∧ p.2 ∉ F := by
    intro n F
    set B : Set α := A n \ (F : Set α) with hB
    have hinf : B.Infinite := (hA n).sdiff F.finite_toSet
    obtain ⟨a, ha⟩ := hinf.nonempty
    have hinf2 : (B \ {a}).Infinite := hinf.sdiff (Set.finite_singleton a)
    obtain ⟨b, hb⟩ := hinf2.nonempty
    refine ⟨(a, b), ha.1, hb.1.1, ?_, ha.2, hb.1.2⟩
    intro hab
    exact hb.2 hab.symm
  choose pick hpick using h2
  let S : ℕ → Finset α := fun n => Nat.rec (motive := fun _ => Finset α) ∅
    (fun k s => insert (pick k s).1 (insert (pick k s).2 s)) n
  have hS : ∀ k, S (k + 1) = insert (pick k (S k)).1 (insert (pick k (S k)).2 (S k)) :=
    fun k => rfl
  have hstep : ∀ k, S k ≤ S (k + 1) := by
    intro k
    rw [hS]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have mono : Monotone S := monotone_nat_of_le_succ hstep
  have hx : ∀ k, (pick k (S k)).1 ∈ S (k + 1) := by
    intro k
    rw [hS]
    exact Finset.mem_insert_self _ _
  have hy : ∀ k, (pick k (S k)).2 ∈ S (k + 1) := by
    intro k
    rw [hS]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have key : ∀ n m, (pick n (S n)).1 ≠ (pick m (S m)).2 := by
    intro n m h
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · have hsub : S (m + 1) ⊆ S n := mono (Nat.succ_le_of_lt hmn)
      have hmem := hsub (hy m)
      rw [← h] at hmem
      exact (hpick n (S n)).2.2.2.1 hmem
    · subst hmn
      exact (hpick m (S m)).2.2.1 h
    · have hsub : S (n + 1) ⊆ S m := mono (Nat.succ_le_of_lt hmn)
      have hmem := hsub (hx n)
      rw [h] at hmem
      exact (hpick m (S m)).2.2.2.2 hmem
  let f : α → Fin 2 := fun z => if ∃ m, z = (pick m (S m)).2 then 1 else 0
  refine ⟨f, fun i hmono => ?_⟩
  have h0 : f (pick i (S i)).1 = 0 := by
    simp only [f]
    rw [if_neg]
    rintro ⟨m, hm⟩
    exact key i m hm
  have h1 : f (pick i (S i)).2 = 1 := by
    simp only [f]
    rw [if_pos ⟨i, rfl⟩]
  have hne := hmono _ (hpick i (S i)).1 _ (hpick i (S i)).2.1
  rw [h0, h1] at hne
  exact absurd hne (by decide)

theorem erdos_602.variants.countable_index :
    ∀ {α : Type*} (A : ℕ → Set α),
      (∀ i, (A i).Countable ∧ (A i).Infinite) →
      (∀ i j, i ≠ j → (A i ∩ A j).Finite) →
      (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 1) →
      HasPropertyB ℕ A := by
  intro α A hA _ _
  exact bernstein A (fun i => (hA i).2)

end Erdos602

#print axioms Erdos602.erdos_602.variants.countable_index
