import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter
namespace Erdos36

def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ := ((A.product B).filter <| fun (a, b) => a - b = k).card

noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ := iSup <| Overlap A B

noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

noncomputable def MinOverlapQuotient (N : ℕ) := (M N : ℝ) / N

lemma overlap_le_card_left (A B : Finset ℤ) (k : ℤ) : Overlap A B k ≤ A.card := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq h => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · obtain ⟨-, hpk⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hqk⟩ := Finset.mem_filter.mp hq
    exact Prod.ext h (by omega)

lemma bddAbove_range_overlap (A B : Finset ℤ) :
    BddAbove (Set.range (Overlap A B)) := by
  refine ⟨A.card, ?_⟩
  rintro x ⟨k, rfl⟩
  exact overlap_le_card_left A B k

lemma maxOverlap_le_card_left (A B : Finset ℤ) : MaxOverlap A B ≤ A.card :=
  ciSup_le fun k => overlap_le_card_left A B k

lemma M_mem (n : ℕ) : ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Icc (1 : ℤ) (2 * n) ∧
    A.card = B.card ∧ M n = MaxOverlap A B := by
  have hne : Set.Nonempty {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)} := by
    refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc ((n : ℤ) + 1) (2 * n), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_Icc] at ha hb
      omega
    · ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · simp only [Int.card_Icc]
      omega
  obtain ⟨A, B, h1, h2, h3, h4⟩ := Nat.sInf_mem hne
  exact ⟨A, B, h1, h2, h3, h4.symm⟩

lemma card_A (n : ℕ) (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) : A.card = n := by
  have := Finset.card_union_of_disjoint hd
  rw [hu, Int.card_Icc] at this
  omega

lemma key (n : ℕ) (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) (hn : 1 ≤ n) :
    n ≤ 4 * MaxOverlap A B := by
  have hA := card_A n A B hd hu hc
  have hB : B.card = n := hc ▸ hA
  have hmem : ((A ×ˢ B : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).MapsTo (fun p : ℤ × ℤ => p.1 - p.2)
      (Finset.Icc (1 - 2 * (n : ℤ)) (2 * n - 1) : Finset ℤ) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    have ha : p.1 ∈ Finset.Icc (1 : ℤ) (2 * n) := hu ▸ Finset.mem_union_left _ hp.1
    have hb : p.2 ∈ Finset.Icc (1 : ℤ) (2 * n) := hu ▸ Finset.mem_union_right _ hp.2
    simp only [Finset.mem_Icc, Finset.mem_coe] at ha hb ⊢
    omega
  have hsum := Finset.card_eq_sum_card_fiberwise hmem
  have hle : ∀ k ∈ Finset.Icc (1 - 2 * (n : ℤ)) (2 * n - 1),
      ((A ×ˢ B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k)).card ≤ MaxOverlap A B := by
    intro k _
    exact le_ciSup (bddAbove_range_overlap A B) k
  have h2 := Finset.sum_le_sum hle
  rw [← hsum, Finset.sum_const, smul_eq_mul, Finset.card_product, hA, hB,
    Int.card_Icc] at h2
  have e : (2 * (n : ℤ) - 1 + 1 - (1 - 2 * n)).toNat = 4 * (n - 1) + 3 := by omega
  rw [e] at h2
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  by_contra h
  have h3 : 4 * MaxOverlap A B ≤ j := by omega
  nlinarith [Nat.mul_le_mul_left (4 * j + 3) h3]

lemma M_le (n : ℕ) : M n ≤ n := by
  obtain ⟨A, B, hd, hu, hc, h⟩ := M_mem n
  rw [h, ← card_A n A B hd hu hc]
  exact maxOverlap_le_card_left A B

lemma four_M (n : ℕ) (hn : 1 ≤ n) : n ≤ 4 * M n := by
  obtain ⟨A, B, hd, hu, hc, h⟩ := M_mem n
  rw [h]
  exact key n A B hd hu hc hn

theorem minimum_overlap.variants.lower.erdos_1955 :
    (1 : ℝ) / 4 ≤ atTop.liminf MinOverlapQuotient := by
  apply le_liminf_of_le
  · apply isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
    intro n
    unfold MinOverlapQuotient
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast M_le n
  · rw [eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    unfold MinOverlapQuotient
    have h := four_M n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hpos]
    have : (n : ℝ) ≤ 4 * (M n : ℝ) := by exact_mod_cast h
    linarith

end Erdos36

#print axioms Erdos36.minimum_overlap.variants.lower.erdos_1955
