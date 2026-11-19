import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Associated

namespace Erdos828

open scoped Nat

lemma two_not_four (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) :
    ¬ 4 ∣ ∏ p ∈ S, p := by
  intro h
  rw [← Finset.mul_prod_erase S (fun p => p) h2] at h
  have h' : 2 ∣ ∏ x ∈ S.erase 2, x :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (by simpa using h)
  obtain ⟨q, hq, hq2⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h'
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hS q (Finset.mem_of_mem_erase hq))).1 hq2
  exact (Finset.ne_of_mem_erase hq) this.symm

lemma two_mem (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (h : 2 ∣ ∏ p ∈ S, p) : 2 ∈ S := by
  obtain ⟨q, hq, hq2⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h
  rwa [(Nat.prime_dvd_prime_iff_eq Nat.prime_two (hS q hq)).1 hq2]

lemma key (n : ℕ) (hn : 2 ≤ n) (h : φ n ∣ n) :
    (∏ p ∈ n.primeFactors, (p - 1)) ∣ ∏ p ∈ n.primeFactors, p := by
  obtain ⟨c, hc⟩ := h
  have e := Nat.totient_mul_prod_primeFactors n
  have hpos : 0 < φ n := Nat.totient_pos.2 (by omega)
  refine ⟨c, ?_⟩
  have e' : φ n * ∏ p ∈ n.primeFactors, p = φ n * ((∏ p ∈ n.primeFactors, (p - 1)) * c) := by
    calc φ n * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p - 1) := e
      _ = φ n * c * ∏ p ∈ n.primeFactors, (p - 1) := by rw [← hc]
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left hpos e'

lemma phi_pow (a b : ℕ) (ha : 0 < a) : φ (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.totient_mul (Nat.Coprime.pow _ _ (by decide)), Nat.totient_prime_pow Nat.prime_two ha]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact ⟨2, by simp; ring⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [Nat.totient_prime_pow Nat.prime_three hb]
    exact ⟨3, by simp; ring⟩

lemma odd_dvd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 2 ∣ p - 1 := by
  rcases hp.eq_two_or_odd' with h | ⟨k, hk⟩
  · exact absurd h h2
  · exact ⟨k, by omega⟩

lemma forward (n : ℕ) (hn : 2 ≤ n) (h : φ n ∣ n) : ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b := by
  have hS : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ := key n hn h
  have hdQ : ∀ p ∈ n.primeFactors, (p - 1) ∣ ∏ p ∈ n.primeFactors, p :=
    fun p hp => (Finset.dvd_prod_of_mem (fun p => p - 1) hp).trans hQ
  have h2 : 2 ∈ n.primeFactors := by
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 (by omega : 1 < n)
    by_cases hp2 : p = 2
    · rwa [← hp2]
    · exact two_mem _ hS ((odd_dvd (hS p hp) hp2).trans (hdQ p hp))
  have huniq : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ 2 → q ≠ 2 → p = q := by
    intro p hp q hq hp2 hq2
    by_contra hpq
    have hsub := Finset.prod_dvd_prod_of_subset {p, q} n.primeFactors (fun p => p - 1)
      (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
    rw [Finset.prod_pair hpq] at hsub
    apply two_not_four _ hS h2
    refine dvd_trans ?_ (hsub.trans hQ)
    obtain ⟨k, hk⟩ := odd_dvd (hS p hp) hp2
    obtain ⟨l, hl⟩ := odd_dvd (hS q hq) hq2
    exact ⟨k * l, by rw [hk, hl]; ring⟩
  have h3 : ∀ p ∈ n.primeFactors, p ≠ 2 → p = 3 := by
    intro p hp hp2
    have hSeq : n.primeFactors = {2, p} := by
      apply Finset.Subset.antisymm
      · intro x hx
        by_cases hx2 : x = 2
        · simp [hx2]
        · simp [huniq x hx p hp hx2 hp2]
      · exact Finset.insert_subset h2 (Finset.singleton_subset_iff.2 hp)
    have hne : (2 : ℕ) ≠ p := fun h => hp2 h.symm
    have hQ' := hQ
    rw [hSeq, Finset.prod_pair hne, Finset.prod_pair hne] at hQ'
    have hp3 := (hS p hp).two_le
    have hd : (p - 1) ∣ 2 * (p - 1) + 2 := by
      have : 2 * (p - 1) + 2 = 2 * p := by omega
      rw [this]
      simpa using hQ'
    have := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_left (p - 1) 2)).1 hd)
    omega
  have hn0 : n ≠ 0 := by omega
  have hsupp : n.factorization.support ⊆ {2, 3} := by
    rw [Nat.support_factorization]
    intro x hx
    by_cases hx2 : x = 2
    · simp [hx2]
    · simp [h3 x hx hx2]
  have e := Nat.prod_factorization_pow_eq_self hn0
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (by decide)] at e
  refine ⟨n.factorization 2, ?_, n.factorization 3, e.symm⟩
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (Nat.dvd_of_mem_primeFactors h2)

theorem erdos_828.variants.phi_dvd_self_iff_pow2_pow3 {n : ℕ} :
    φ n ∣ n ↔ n ≤ 1 ∨ ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr (forward n (by omega) h)
  · rintro (hn | ⟨a, ha, b, rfl⟩)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> simp
    · exact phi_pow a b ha

end Erdos828

#print axioms Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3
