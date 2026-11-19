import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Parity

namespace OeisA237271

open Nat Finset List

def a (n : ℕ) : ℕ :=
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k
  1 + count

def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k
  1 + num_jumps

/-- In a consecutive pair of divisors (d, d'), d' > 2d iff d' is odd and d' ≥ 2d:
if d' were even, d'/2 would be a divisor strictly between d and d'. -/
lemma pair_iff (n : ℕ) (x : ℕ × ℕ)
    (hx : x ∈ (n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail) :
    (Odd x.2 ∧ x.2 ≥ 2 * x.1) ↔ x.2 > 2 * x.1 := by
  set D := n.divisors.sort (· ≤ ·) with hD
  have hpw : D.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnd : D.Nodup := Finset.sort_nodup _ _
  have hle : ∀ i j (hi : i < D.length) (hj : j < D.length), i ≤ j → D[i] ≤ D[j] := by
    intro i j hi hj hij
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hpw i j hi hj h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen : i + 1 < D.length := by simp at hi; omega
  simp only [List.getElem_zip, List.getElem_tail]
  have hlt : D[i] < D[i + 1] := by
    refine lt_of_le_of_ne (hle i (i + 1) (by omega) hlen (by omega)) ?_
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp heq
    omega
  constructor
  · rintro ⟨ho, hge⟩
    rcases Nat.eq_or_lt_of_le hge with h | h
    · exfalso
      rw [← h] at ho
      exact (Nat.not_even_iff_odd.mpr ho) (even_two_mul _)
    · exact h
  · intro hgt
    refine ⟨?_, hgt.le⟩
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨c, hc⟩ := hev
    have hmem : D[i + 1] ∈ n.divisors := (Finset.mem_sort _).mp (List.getElem_mem hlen)
    rw [Nat.mem_divisors] at hmem
    have hcmem : c ∈ D := by
      rw [hD, Finset.mem_sort, Nat.mem_divisors]
      refine ⟨?_, hmem.2⟩
      exact Nat.dvd_trans ⟨2, by omega⟩ hmem.1
    obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.mp hcmem
    rcases Nat.lt_or_ge i j with h | h
    · have := hle (i + 1) j hlen hj (by omega)
      omega
    · have := hle j i hj (by omega) h
      omega

theorem conjecture_2 (n : ℕ) : a n = num2DenseSublists n := by
  unfold a num2DenseSublists sortedDivisorsList
  simp only
  congr 1
  apply List.countP_congr
  intro x hx
  simp only [decide_eq_true_eq]
  exact pair_iff n x hx

theorem conjecture_3 (n : ℕ) :
    a n = 1 + ((sortedDivisorsList n).zip (sortedDivisorsList n).tail).countP
      fun pair => pair.snd > 2 * pair.fst :=
  conjecture_2 n

#print axioms conjecture_2
#print axioms conjecture_3

end OeisA237271
