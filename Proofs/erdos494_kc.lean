import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

namespace KC

/-- If `|X| = k`, the multiset of `k`-sums is the single total sum. -/
lemma self_card (X : Finset ℂ) (k : ℕ) (hX : X.card = k) :
    sumMultiset X k = {X.sum id} := by
  unfold sumMultiset
  rw [← hX, Finset.powersetCard_self]
  simp

/-- The natural-number embedding into `ℂ`. -/
noncomputable def e : ℕ ↪ ℂ := ⟨Nat.cast, Nat.cast_injective⟩

lemma sum_e (s : Finset ℕ) : (s.map e).sum id = ((∑ x ∈ s, x : ℕ) : ℂ) := by
  rw [Finset.sum_map, Nat.cast_sum]
  rfl

/-- The negation embedding. -/
def ng : ℂ ↪ ℂ := (Equiv.neg ℂ).toEmbedding

lemma neg_sub (A s : Finset ℂ) (hA : A.sum id = 0) (hs : s ⊆ A) :
    (s.map ng).sum id = (A \ s).sum id := by
  rw [Finset.sum_map]
  have h := Finset.sum_sdiff hs (f := id)
  rw [hA] at h
  have : ∑ x ∈ s, id (ng x) = -(∑ x ∈ s, id x) := by
    rw [← Finset.sum_neg_distrib]
    rfl
  rw [this]
  exact (eq_neg_of_add_eq_zero_left h).symm

lemma compl_val (A : Finset ℂ) (k : ℕ) (hc : A.card = 2 * k) :
    (A.powersetCard k).val.map (A \ ·) = (A.powersetCard k).val := by
  have hinj : Set.InjOn (A \ ·) ↑(A.powersetCard k) := by
    intro s hs t ht h
    have hs' := (Finset.mem_powersetCard.mp hs).1
    have ht' := (Finset.mem_powersetCard.mp ht).1
    simp only at h
    rw [← sdiff_sdiff_eq_self hs', ← sdiff_sdiff_eq_self ht', h]
  have himg : (A.powersetCard k).image (A \ ·) = A.powersetCard k := by
    ext t
    simp only [Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · rintro ⟨s, ⟨hs, hsc⟩, rfl⟩
      exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hs]; omega⟩
    · rintro ⟨ht, htc⟩
      exact ⟨A \ t, ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset ht]; omega⟩,
        sdiff_sdiff_eq_self ht⟩
  rw [← Finset.image_val_of_injOn hinj, himg]

lemma neg_multiset (A : Finset ℂ) (k : ℕ) (hA : A.sum id = 0) (hc : A.card = 2 * k) :
    sumMultiset (A.map ng) k = sumMultiset A k := by
  unfold sumMultiset
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map]
  have h1 : (A.powersetCard k).val.map
      ((fun s : Finset ℂ => s.sum id) ∘ ⇑(Finset.mapEmbedding ng).toEmbedding) =
      (A.powersetCard k).val.map (fun s => (A \ s).sum id) := by
    refine Multiset.map_congr rfl (fun s hs => ?_)
    have hs' := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).1
    exact neg_sub A s hA hs'
  rw [h1]
  have h2 : (A.powersetCard k).val.map (fun s => (A \ s).sum id) =
      ((A.powersetCard k).val.map (A \ ·)).map (fun s => s.sum id) := by
    rw [Multiset.map_map]
    rfl
  rw [h2, compl_val A k hc]

end KC

theorem erdos_494.variants.k_eq_card :
    ∀ k > 2, ¬Erdos494Unique k k := by
  intro k hk h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  let C : Finset ℕ := Finset.Ico 5 (m + 5)
  let A' : Finset ℕ := insert 1 (insert 4 C)
  let B' : Finset ℕ := insert 2 (insert 3 C)
  have hA' : A'.card = m + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [C]), Finset.card_insert_of_notMem (by simp [C])]
    simp [C]
  have hB' : B'.card = m + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [C]), Finset.card_insert_of_notMem (by simp [C])]
    simp [C]
  have hsum : ∑ x ∈ A', x = ∑ x ∈ B', x := by
    rw [Finset.sum_insert (by simp [C]), Finset.sum_insert (by simp [C]),
      Finset.sum_insert (by simp [C]), Finset.sum_insert (by simp [C])]
    omega
  have hcA : (A'.map KC.e).card = m + 2 := by rw [Finset.card_map, hA']
  have hcB : (B'.map KC.e).card = m + 2 := by rw [Finset.card_map, hB']
  have hAB := h _ _ hcA hcB (by
    rw [KC.self_card _ _ hcA, KC.self_card _ _ hcB, KC.sum_e, KC.sum_e, hsum])
  have hAB' : A' = B' := Finset.map_injective KC.e hAB
  have h1 : (1 : ℕ) ∈ B' := hAB' ▸ (by simp [A'])
  simp [B', C] at h1

theorem erdos_494.variants.card_eq_2k :
    ∀ k > 2, ¬Erdos494Unique k (2 * k) := by
  intro k hk h
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 3 := ⟨2 * k - 3, by omega⟩
  let T' : Finset ℕ := (Finset.range (m + 2)).map ⟨fun i => i + 1, add_left_injective 1⟩
  let S : ℕ := ∑ x ∈ T', x
  have hS : m + 2 < S := by
    have e1 : S = ∑ i ∈ Finset.range (m + 2), (i + 1) := by
      simp only [S, T', Finset.sum_map, Function.Embedding.coeFn_mk]
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ]
    omega
  let T : Finset ℂ := T'.map KC.e
  have hTsum : T.sum id = (S : ℂ) := KC.sum_e T'
  have hmemT : ∀ x ∈ T, ∃ j : ℕ, x = ((j + 1 : ℕ) : ℂ) := by
    intro x hx
    simp only [T, T', Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
    obtain ⟨a, ⟨j, _, rfl⟩, rfl⟩ := hx
    exact ⟨j, rfl⟩
  have notT : ∀ n : ℕ, -((n : ℕ) : ℂ) ∉ T := by
    intro n hn
    obtain ⟨j, hj⟩ := hmemT _ hn
    have : ((n + (j + 1) : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add, ← hj]
      ring
    rw [Nat.cast_eq_zero] at this
    omega
  let A : Finset ℂ := insert (-(S : ℂ)) T
  have hAc : A.card = 2 * k := by
    rw [Finset.card_insert_of_notMem (notT S), Finset.card_map, Finset.card_map,
      Finset.card_range]
    omega
  have hAs : A.sum id = 0 := by
    rw [Finset.sum_insert (notT S), hTsum]
    simp
  have hBc : (A.map KC.ng).card = 2 * k := by rw [Finset.card_map, hAc]
  have hAB := h _ _ hAc hBc (KC.neg_multiset A k hAs hAc).symm
  -- the element `m + 2` of `T` gives `-(m+2) ∈ A.map ng`, which is not in `A`
  have htop : (((m + 1 + 1 : ℕ)) : ℂ) ∈ T := by
    simp only [T, T', Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    exact ⟨m + 1 + 1, ⟨m + 1, by omega, rfl⟩, rfl⟩
  have hin : -(((m + 1 + 1 : ℕ)) : ℂ) ∈ A.map KC.ng := by
    rw [Finset.mem_map]
    exact ⟨_, Finset.mem_insert_of_mem htop, rfl⟩
  rw [← hAB] at hin
  rcases Finset.mem_insert.mp hin with h1 | h1
  · rw [neg_inj, Nat.cast_inj] at h1
    omega
  · exact notT _ h1

end Erdos494

#print axioms Erdos494.erdos_494.variants.k_eq_card
#print axioms Erdos494.erdos_494.variants.card_eq_2k
