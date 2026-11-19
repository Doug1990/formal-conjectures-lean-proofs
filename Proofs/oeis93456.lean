import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite

namespace OeisA93456

/-- Product of all composite numbers in the interval $[\binom{n}{2} + 1, \binom{n+1}{2}]$. -/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  ((Finset.Icc L R).filter fun k => 1 < k ∧ ¬ k.Prime).prod id

namespace P

lemma choose_succ_two (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  have h := Nat.choose_succ_succ k 1
  rw [Nat.choose_one_right] at h
  exact h.trans (Nat.add_comm _ _)

lemma four_le (m : ℕ) (hm : 9 ≤ m) : 4 * m ≤ m.choose 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [choose_succ_two]
    omega

lemma small (m p : ℕ) (h : m.choose 2 < 2 * p) (hp : 20 ≤ p) : 2 * m + 1 ≤ p := by
  by_contra hc
  have := four_le m (by omega)
  omega

lemma not_prime_two_mul (p : ℕ) (hp : 2 ≤ p) : ¬ (2 * p).Prime := by
  intro h
  have := h.eq_one_or_self_of_dvd 2 (Dvd.intro p rfl)
  omega

lemma dvd_a (p m : ℕ) (hp : p.Prime) (h1 : m.choose 2 < 2 * p)
    (h2 : 2 * p ≤ (m + 1).choose 2) : p ∣ a m := by
  have e : a m = ((Finset.Icc (m.choose 2 + 1) ((m + 1).choose 2)).filter
      fun k => 1 < k ∧ ¬ k.Prime).prod id := rfl
  rw [e]
  have h2p := hp.two_le
  have hmem : 2 * p ∈ (Finset.Icc (m.choose 2 + 1) ((m + 1).choose 2)).filter
      (fun k => 1 < k ∧ ¬ k.Prime) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, h2⟩, by omega, not_prime_two_mul p h2p⟩
  exact (Prime.dvd_finsetProd_iff hp.prime id).mpr ⟨2 * p, hmem, Dvd.intro_left 2 rfl⟩

lemma not_dvd_a (p m : ℕ) (hp : p.Prime) (h1 : m.choose 2 < 2 * p)
    (h2 : 2 * p ≤ (m + 1).choose 2) (h3 : 2 * m + 1 ≤ p) : ¬ p ∣ a (m + 1) := by
  have e : a (m + 1) = ((Finset.Icc ((m + 1).choose 2 + 1) ((m + 1 + 1).choose 2)).filter
      fun k => 1 < k ∧ ¬ k.Prime).prod id := rfl
  rw [e]
  intro h
  obtain ⟨k, hk, j, rfl⟩ := (Prime.dvd_finsetProd_iff hp.prime id).mp h
  rw [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hk2⟩, -⟩ := hk
  have e1 := choose_succ_two m
  have e2 := choose_succ_two (m + 1)
  rcases Nat.lt_or_ge j 3 with hj | hj
  · have := Nat.mul_le_mul_left p (show j ≤ 2 by omega)
    omega
  · have := Nat.mul_le_mul_left p hj
    omega

lemma exists_m (p : ℕ) (hp : 1 ≤ p) :
    ∃ m, m.choose 2 < 2 * p ∧ 2 * p ≤ (m + 1).choose 2 := by
  classical
  have hex : ∃ m, 2 * p ≤ (m + 1).choose 2 := ⟨2 * p, by rw [choose_succ_two]; omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | k
  · have : (0 : ℕ).choose 2 = 0 := rfl
    omega
  · have := Nat.find_min hex (show k < Nat.find hex by omega)
    omega

end P

theorem conjecture :
    ¬ Set.Finite {n : ℕ | 1 < n ∧ ¬ (a (n - 1) ∣ a n)} := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes ((N + 1).choose 2 + 20)
  obtain ⟨m, h1, h2⟩ := P.exists_m p (by omega)
  have h3 := P.small m p h1 (by omega)
  have hmN : N < m := by
    by_contra hc
    have := Nat.choose_le_choose 2 (show m + 1 ≤ N + 1 by omega)
    omega
  refine ⟨m + 1, ⟨by omega, ?_⟩, by omega⟩
  intro hd
  simp only [Nat.add_sub_cancel] at hd
  exact P.not_dvd_a p m hp h1 h2 h3 ((P.dvd_a p m hp h1 h2).trans hd)

end OeisA93456

#print axioms OeisA93456.conjecture
