import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

namespace P2

/-- Multiset of 2-sums, generic. -/
def S {α : Type*} [AddCommMonoid α] (A : Finset α) : Multiset α :=
  (A.powersetCard 2).val.map fun s => s.sum id

/-- Cross sums. -/
def X {α : Type*} [AddCommMonoid α] (A B : Finset α) : Multiset α :=
  B.val.bind (fun y => A.val.map (fun x => y + x))

lemma S_insert {α : Type*} [DecidableEq α] [AddCommMonoid α] {y : α} {s : Finset α}
    (h : y ∉ s) : S (insert y s) = S s + s.val.map (fun x => y + x) := by
  unfold S
  have e := Finset.powersetCard_succ_insert h 1
  have hd : Disjoint (s.powersetCard (Nat.succ 1)) ((s.powersetCard 1).image (insert y)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    have h1 := (Finset.mem_powersetCard.mp ht).1
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht'
    exact h (h1 (Finset.mem_insert_self y u))
  rw [← Finset.disjUnion_eq_union _ _ hd] at e
  have e2 : (2 : ℕ) = Nat.succ 1 := rfl
  rw [e2, e, Finset.disjUnion_val, Multiset.map_add]
  congr 1
  have hinj : Set.InjOn (insert y) (↑(s.powersetCard 1) : Set (Finset α)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.powersetCard_one] at ha hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have hab' : insert y ({a'} : Finset α) = insert y ({b'} : Finset α) := hab
    have hm : a' ∈ insert y ({b'} : Finset α) := by
      rw [← hab']
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact absurd (hm ▸ ha') h
    · simp [hm]
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map, Finset.powersetCard_one,
    Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x hx => ?_)
  have hxy : y ≠ x := fun hh => h (hh ▸ Finset.mem_val.mp hx)
  simp only [Function.comp, Function.Embedding.coeFn_mk]
  rw [Finset.sum_insert (by simpa using hxy), Finset.sum_singleton]
  rfl

lemma S_union {α : Type*} [DecidableEq α] [AddCommMonoid α] (A B : Finset α)
    (h : Disjoint A B) : S (A ∪ B) = S A + S B + X A B := by
  induction B using Finset.induction_on with
  | empty =>
    have : S (∅ : Finset α) = 0 := by
      unfold S
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      rfl
    simp [this, X]
  | insert b B hb ih =>
    have hbA : b ∉ A := fun hh => Finset.disjoint_left.mp h hh (Finset.mem_insert_self b B)
    have hAB : Disjoint A B := Finset.disjoint_of_subset_right (Finset.subset_insert b B) h
    have hbAB : b ∉ A ∪ B := by
      rw [Finset.mem_union]
      rintro (hh | hh)
      · exact hbA hh
      · exact hb hh
    rw [Finset.union_insert, S_insert hbAB, ih hAB, S_insert hb]
    rw [← Finset.disjUnion_eq_union _ _ hAB, Finset.disjUnion_val, Multiset.map_add]
    unfold X
    rw [Finset.insert_val_of_notMem hb, Multiset.cons_bind]
    abel

lemma X_comm {α : Type*} [AddCommMonoid α] (A B : Finset α) : X A B = X B A := by
  unfold X
  have h1 : ∀ (s : Multiset α) (f : α → α), s.map f = s.bind (fun x => {f x}) :=
    fun s f => (Multiset.bind_singleton s f).symm
  simp only [h1]
  rw [Multiset.bind_bind]
  congr 1
  funext x
  congr 1
  funext y
  rw [add_comm]

lemma S_add (A : Finset ℕ) (d : ℕ) :
    S (A.map (addRightEmbedding d)) = (S A).map (fun z => z + 2 * d) := by
  unfold S
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun s hs => ?_)
  have hc := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).2
  show (s.map (addRightEmbedding d)).sum id = s.sum id + 2 * d
  rw [Finset.sum_map]
  simp only [addRightEmbedding_apply, id, Finset.sum_add_distrib, Finset.sum_const, hc,
    smul_eq_mul]

lemma X_add (A B : Finset ℕ) (d : ℕ) :
    X A (B.map (addRightEmbedding d)) = (X A B).map (fun z => z + d) := by
  unfold X
  rw [Finset.map_val, Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext y
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp only [Function.comp, addRightEmbedding_apply]
  ring

lemma constr : ∀ l : ℕ, ∃ A B : Finset ℕ, A.card = 2 ^ l ∧ B.card = 2 ^ l ∧ A ≠ B ∧
    S A = S B ∧ (∀ x ∈ A, x < 2 ^ (l + 1)) ∧ (∀ x ∈ B, x < 2 ^ (l + 1)) := by
  intro l
  induction l with
  | zero =>
    refine ⟨{0}, {1}, rfl, rfl, by decide, ?_, by simp, by simp⟩
    unfold S
    rw [Finset.powersetCard_eq_empty.mpr (by simp), Finset.powersetCard_eq_empty.mpr (by simp)]
  | succ l ih =>
    obtain ⟨A, B, hA, hB, hne, hS, hAl, hBl⟩ := ih
    set d := 2 ^ (l + 1) with hd
    have hAB : Disjoint A (B.map (addRightEmbedding d)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx'
      have := hAl _ hx
      simp only [addRightEmbedding_apply] at this
      omega
    have hBA : Disjoint B (A.map (addRightEmbedding d)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx'
      have := hBl _ hx
      simp only [addRightEmbedding_apply] at this
      omega
    have hpow : 2 ^ (l + 1 + 1) = 2 ^ (l + 1) + 2 ^ (l + 1) := by ring
    refine ⟨A ∪ B.map (addRightEmbedding d), B ∪ A.map (addRightEmbedding d), ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hAB, Finset.card_map, hA, hB, hd]
      ring
    · rw [Finset.card_union_of_disjoint hBA, Finset.card_map, hA, hB, hd]
      ring
    · intro heq
      apply hne
      ext x
      constructor
      · intro hx
        have h1 : x ∈ B ∪ A.map (addRightEmbedding d) := heq ▸ Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp h1 with h2 | h2
        · exact h2
        · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp h2
          have := hAl _ hx
          simp only [addRightEmbedding_apply] at this
          omega
      · intro hx
        have h1 : x ∈ A ∪ B.map (addRightEmbedding d) := heq.symm ▸ Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp h1 with h2 | h2
        · exact h2
        · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp h2
          have := hBl _ hx
          simp only [addRightEmbedding_apply] at this
          omega
    · rw [S_union _ _ hAB, S_union _ _ hBA, S_add, S_add, X_add, X_add, X_comm A B, hS]
    · intro x hx
      rcases Finset.mem_union.mp hx with h2 | h2
      · have := hAl _ h2
        omega
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp h2
        have := hBl _ hy
        simp only [addRightEmbedding_apply]
        omega
    · intro x hx
      rcases Finset.mem_union.mp hx with h2 | h2
      · have := hBl _ h2
        omega
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp h2
        have := hAl _ hy
        simp only [addRightEmbedding_apply]
        omega

/-- The natural-number embedding into `ℂ`. -/
noncomputable def e : ℕ ↪ ℂ := ⟨Nat.cast, Nat.cast_injective⟩

lemma S_cast (A : Finset ℕ) : S (A.map e) = (S A).map (fun z : ℕ => (z : ℂ)) := by
  unfold S
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun s _ => ?_)
  show (s.map e).sum id = ((s.sum id : ℕ) : ℂ)
  rw [Finset.sum_map, Nat.cast_sum]
  rfl

end P2

theorem erdos_494.variants.k_eq_2_card_pow_two :
    ∀ card : ℕ, (∃ l : ℕ, card = 2 ^ l) → ¬Erdos494Unique 2 card := by
  rintro card ⟨l, rfl⟩ h
  obtain ⟨A, B, hA, hB, hne, hS, -, -⟩ := P2.constr l
  apply hne
  apply Finset.map_injective P2.e
  apply h _ _ (by rw [Finset.card_map, hA]) (by rw [Finset.card_map, hB])
  show P2.S (A.map P2.e) = P2.S (B.map P2.e)
  rw [P2.S_cast, P2.S_cast, hS]

end Erdos494

#print axioms Erdos494.erdos_494.variants.k_eq_2_card_pow_two
