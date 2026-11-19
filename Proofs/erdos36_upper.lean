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

/-- The middle block. -/
def midA (n : ℕ) : Finset ℤ := Finset.Icc (((n / 2 : ℕ) : ℤ) + 1) (((n / 2 : ℕ) : ℤ) + n)

/-- The two outer blocks. -/
def outB (n : ℕ) : Finset ℤ :=
  Finset.Icc 1 ((n / 2 : ℕ) : ℤ) ∪ Finset.Icc (((n / 2 : ℕ) : ℤ) + n + 1) (2 * n)

lemma overlap_mid (n : ℕ) (k : ℤ) : Overlap (midA n) (outB n) k ≤ (n + 1) / 2 := by
  rcases lt_or_ge 0 k with hk | hk
  · calc Overlap (midA n) (outB n) k ≤ (Finset.Icc (1 : ℤ) ((n / 2 : ℕ) : ℤ)).card := by
          refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp q hq e => ?_)
          · obtain ⟨hp1, hpk⟩ := Finset.mem_filter.mp hp
            obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
            simp only [midA, outB, Finset.mem_union, Finset.mem_Icc] at ha hb
            simp only [Finset.mem_coe, Finset.mem_Icc]
            omega
          · obtain ⟨-, hpk⟩ := Finset.mem_filter.mp hp
            obtain ⟨-, hqk⟩ := Finset.mem_filter.mp hq
            exact Prod.ext (by omega) e
      _ ≤ (n + 1) / 2 := by
          rw [Int.card_Icc]
          omega
  · calc Overlap (midA n) (outB n) k ≤
          (Finset.Icc (((n / 2 : ℕ) : ℤ) + n + 1) (2 * n)).card := by
          refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp q hq e => ?_)
          · obtain ⟨hp1, hpk⟩ := Finset.mem_filter.mp hp
            obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
            simp only [midA, outB, Finset.mem_union, Finset.mem_Icc] at ha hb
            simp only [Finset.mem_coe, Finset.mem_Icc]
            omega
          · obtain ⟨-, hpk⟩ := Finset.mem_filter.mp hp
            obtain ⟨-, hqk⟩ := Finset.mem_filter.mp hq
            exact Prod.ext (by omega) e
      _ ≤ (n + 1) / 2 := by
          rw [Int.card_Icc]
          omega

lemma M_le_half (n : ℕ) : 2 * M n ≤ n + 1 := by
  have hd : Disjoint (midA n) (outB n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [midA, outB, Finset.mem_union, Finset.mem_Icc] at ha hb
    omega
  have hu : midA n ∪ outB n = Finset.Icc (1 : ℤ) (2 * n) := by
    ext x
    simp only [midA, outB, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdB : Disjoint (Finset.Icc 1 ((n / 2 : ℕ) : ℤ))
      (Finset.Icc (((n / 2 : ℕ) : ℤ) + n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hc : (midA n).card = (outB n).card := by
    rw [outB, Finset.card_union_of_disjoint hdB, midA, Int.card_Icc, Int.card_Icc, Int.card_Icc]
    omega
  have h1 : M n ≤ MaxOverlap (midA n) (outB n) := Nat.sInf_le ⟨_, _, hd, hu, hc, rfl⟩
  have h2 : MaxOverlap (midA n) (outB n) ≤ (n + 1) / 2 :=
    ciSup_le fun k => overlap_mid n k
  omega

theorem minimum_overlap.variants.upper.erdos_1955 :
    atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le
  · apply isCoboundedUnder_le_of_le atTop (x := (0 : ℝ))
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [eventually_atTop]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N + 1, fun n hn => ?_⟩
    unfold MinOverlapQuotient
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    have h1 : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp (hN.trans_le hNn)
    have h2 : (2 : ℝ) * M n ≤ n + 1 := by exact_mod_cast M_le_half n
    rw [div_le_iff₀ hpos]
    nlinarith

end Erdos36

#print axioms Erdos36.minimum_overlap.variants.upper.erdos_1955
