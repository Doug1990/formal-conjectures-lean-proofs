import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Even
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Arxiv.«1609.08688»

def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (_hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  classical
  let f : Fin s.length → ℕ × ℕ := fun k => (s[k] 0, s[k] 1)
  let t : Finset (ℕ × ℕ) := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  have ht_card : t.card < (Finset.univ : Finset (Fin s.length)).card := by
    simp only [t, Finset.card_univ, Fintype.card_fin, Finset.card_product,
      Nat.card_Icc, Nat.add_sub_cancel, ← sq]
    exact hs₂
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin s.length)), f k ∈ t := by
    intro k _
    have hmem : s[k] ∈ s := List.getElem_mem k.isLt
    have h0 := hs₁ _ hmem ⟨0, rfl⟩
    have h1 := hs₁ _ hmem ⟨1, rfl⟩
    rw [Set.mem_Icc] at h0 h1
    simp only [t, f, Finset.mem_product, Finset.mem_Icc]
    exact ⟨h0, h1⟩
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht_card hf
  exact ⟨i, j, hij, congrArg Prod.fst hfij, congrArg Prod.snd hfij⟩

lemma bdd (n : ℕ) : BddAbove
    { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) } := by
  refine ⟨(n + 2) ^ 2, ?_⟩
  rintro _ ⟨s, hs_range, hs_inc, rfl⟩
  by_contra hle
  have hs_length : (n + 2) ^ 2 < s.length := Nat.lt_of_not_ge hle
  obtain ⟨i, j, hij, h0, h1⟩ :=
    exists_pair_of_mem_Icc (n := n + 2) (by omega)
      (fun a ha => (hs_range a ha).trans (Set.Icc_subset_Icc_right (by omega))) hs_length
  have hp : s.Pairwise lt₂ := hs_inc
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 (by decide) h0.ge h1.ge)
      (List.pairwise_iff_get.1 hp i j hij)
  · exact (not_lt₂_of_exists 0 1 (by decide) h0.le h1.le)
      (List.pairwise_iff_get.1 hp j i hji)

lemma key {k a b c d : ℕ} (hab : a < b) (hc : c < k) : a * k + c < b * k + d := by
  have := Nat.mul_le_mul_right k (show a + 1 ≤ b from hab)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

def T (k x y z : ℕ) : Fin 3 → ℕ := ![x * k + y + 1, x * k + z + 1, y * k + z + 1]

def L (k : ℕ) : List (Fin 3 → ℕ) :=
  (List.range k).flatMap fun x => (List.range k).flatMap fun y =>
    (List.range k).map fun z => T k x y z

lemma caseZ {k x y z z' : ℕ} (h : z < z') : T k x y z <₂ T k x y z' :=
  ⟨1, 2, by decide, show x * k + z + 1 < x * k + z' + 1 by omega,
    show y * k + z + 1 < y * k + z' + 1 by omega⟩

lemma caseY {k x y y' z z' : ℕ} (h : y < y') (hz : z < k) : T k x y z <₂ T k x y' z' :=
  ⟨0, 2, by decide, show x * k + y + 1 < x * k + y' + 1 by omega,
    show y * k + z + 1 < y' * k + z' + 1 by have := key (d := z') h hz; omega⟩

lemma caseX {k x x' y y' z z' : ℕ} (h : x < x') (hy : y < k) (hz : z < k) :
    T k x y z <₂ T k x' y' z' :=
  ⟨0, 1, by decide,
    show x * k + y + 1 < x' * k + y' + 1 by have := key (d := y') h hy; omega,
    show x * k + z + 1 < x' * k + z' + 1 by have := key (d := z') h hz; omega⟩

lemma pairwise_L (k : ℕ) : IsIncreasing₂ (L k) := by
  unfold IsIncreasing₂ L
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun y _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact List.pairwise_lt_range.imp fun h => caseZ h
    · refine List.pairwise_lt_range.imp_of_mem fun {y y'} _ _ h => ?_
      intro a ha b hb
      simp only [List.mem_map, List.mem_range] at ha hb
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨z', _, rfl⟩ := hb
      exact caseY h hz
  · refine List.pairwise_lt_range.imp_of_mem fun {x x'} _ _ h => ?_
    intro a ha b hb
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨y', _, z', _, rfl⟩ := hb
    exact caseX h hy hz

lemma range_L (k : ℕ) : ∀ a ∈ L k, Set.range a ⊆ Set.Icc 1 (k * k) := by
  intro a ha
  simp only [L, List.mem_flatMap, List.mem_map, List.mem_range] at ha
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := ha
  have b1 := key (d := 0) hx hy
  have b2 := key (d := 0) hx hz
  have b3 := key (d := 0) hy hz
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨by simp [T], show x * k + y + 1 ≤ k * k by omega⟩
  · exact ⟨by simp [T], show x * k + z + 1 ≤ k * k by omega⟩
  · exact ⟨by simp [T], show y * k + z + 1 ≤ k * k by omega⟩

lemma length_L (k : ℕ) : (L k).length = k ^ 3 := by
  simp [L, List.length_flatMap, pow_succ]
  exact (Nat.mul_assoc _ _ _).symm

theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.sqrt_eq]
  unfold maximalLength
  exact le_csSup (bdd (k * k)) ⟨L k, range_L k, pairwise_L k, length_L k⟩

end Arxiv.«1609.08688»

#print axioms Arxiv.«1609.08688».maximalLength_ge_of_isSquare
