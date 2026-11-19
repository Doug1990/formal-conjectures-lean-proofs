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

lemma sort_divisors_prime_pow (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors.sort (· ≤ ·) = (List.range (k + 1)).map (p ^ ·) := by
  rw [Nat.divisors_prime_pow hp k]
  have hmono : StrictMonoOn (⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ : ℕ ↪ ℕ)
      (Finset.range (k + 1)) := by
    intro i _ j _ hij
    exact Nat.pow_lt_pow_right hp.one_lt hij
  rw [← hmono.map_finsetSort, Finset.sort_range]
  rfl

theorem a_odd_prime_pow (p k : ℕ) (hp : p.Prime) (ho : Odd p) :
    a (p ^ k) = k + 1 := by
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h; exact absurd ho (by decide)
    · have := hp.two_le
      by_contra hc
      have : p = 2 := by omega
      subst this; exact absurd ho (by decide)
  unfold a
  simp only
  rw [sort_divisors_prime_pow p k hp]
  set L := (List.range (k + 1)).map (p ^ ·) with hL
  have hlen : (L.zip L.tail).length = k := by
    simp [hL, List.length_zip]
  have hall : ∀ x ∈ L.zip L.tail, Odd x.2 ∧ x.2 ≥ 2 * x.1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < k := by rw [hlen] at hi; exact hi
    simp only [List.getElem_zip, List.getElem_tail, hL, List.getElem_map, List.getElem_range]
    refine ⟨ho.pow, ?_⟩
    rw [pow_succ]
    rw [Nat.mul_comm 2]
    exact Nat.mul_le_mul_left _ (by omega)
  rw [List.countP_eq_length.mpr (by simpa using hall), hlen]
  omega

#print axioms a_odd_prime_pow

end OeisA237271
