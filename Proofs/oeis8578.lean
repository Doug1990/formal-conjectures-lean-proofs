import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OeisA8578

open ArithmeticFunction

/-- The predicate for the sequence: $n = 1$ or $n$ is prime. -/
def A (n : ℕ) : Prop := n = 1 ∨ n.Prime

namespace P

lemma geom (c : ℕ) : ∀ n : ℕ, (∑ k ∈ Finset.range n, (c + 1) ^ k) * c + 1 = (c + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_mul, add_right_comm, geom c n, pow_succ]
    ring

lemma geom_le {P : ℕ} (hP : 1 ≤ P) (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1), P ^ k) * (P - 1) ≤ P ^ (e + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, P = c + 1 := ⟨P - 1, by omega⟩
  have := geom c (e + 1)
  rw [Nat.add_sub_cancel]
  omega

lemma coprime_pow {P r : ℕ} (hP : P.Prime) (hr : ¬ P ∣ r) (e : ℕ) : Nat.Coprime (P ^ e) r :=
  Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hP).2 hr)

/-- σ(m) ≤ (Q-1) m when all prime factors of m are < Q. -/
lemma sigma_le (Q : ℕ) (hQ : 2 ≤ Q) : ∀ m : ℕ, m ≠ 0 →
    (∀ p, p.Prime → p ∣ m → p < Q) → sigma 1 m ≤ (Q - 1) * m := by
  induction Q, hQ using Nat.le_induction with
  | base =>
    intro m hm h
    have : m = 1 := by
      by_contra h1
      have := h _ (Nat.minFac_prime h1) (Nat.minFac_dvd m)
      have := (Nat.minFac_prime h1).two_le
      omega
    subst this
    simp
  | succ Q hQ ih =>
    intro m hm h
    by_cases hc : Q.Prime ∧ Q ∣ m
    · obtain ⟨hQp, -⟩ := hc
      obtain ⟨e, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm Q hQp.one_lt.ne'
      have hr0 : r ≠ 0 := by rintro rfl; simp at hm
      have hr' : ∀ p, p.Prime → p ∣ r → p < Q := by
        intro p hp hpr
        have h1 := h p hp (Dvd.dvd.mul_left hpr _)
        have h2 : p ≠ Q := by rintro rfl; exact hr hpr
        omega
      have ihr := ih r hr0 hr'
      rw [isMultiplicative_sigma.map_mul_of_coprime (coprime_pow hQp hr e),
        sigma_one_apply_prime_pow hQp]
      have hg := geom_le (P := Q) (by omega) e
      rw [Nat.add_sub_cancel]
      calc (∑ k ∈ Finset.range (e + 1), Q ^ k) * sigma 1 r
          ≤ (∑ k ∈ Finset.range (e + 1), Q ^ k) * ((Q - 1) * r) :=
            Nat.mul_le_mul_left _ ihr
        _ = ((∑ k ∈ Finset.range (e + 1), Q ^ k) * (Q - 1)) * r := by ring
        _ ≤ Q ^ (e + 1) * r := Nat.mul_le_mul_right _ hg
        _ = Q * (Q ^ e * r) := by ring
    · have h' : ∀ p, p.Prime → p ∣ m → p < Q := by
        intro p hp hpm
        have h1 := h p hp hpm
        have h2 : p ≠ Q := by rintro rfl; exact hc ⟨hp, hpm⟩
        omega
      have := ih m hm h'
      rw [Nat.add_sub_cancel]
      calc sigma 1 m ≤ (Q - 1) * m := this
        _ ≤ Q * m := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- σ(P m) ≤ (P+1) σ(m). -/
lemma sigma_prime_mul {P m : ℕ} (hP : P.Prime) (hm : m ≠ 0) :
    sigma 1 (P * m) ≤ (P + 1) * sigma 1 m := by
  obtain ⟨e, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm P hP.one_lt.ne'
  rw [← mul_assoc, ← pow_succ', isMultiplicative_sigma.map_mul_of_coprime (coprime_pow hP hr _),
    isMultiplicative_sigma.map_mul_of_coprime (coprime_pow hP hr _),
    sigma_one_apply_prime_pow hP, sigma_one_apply_prime_pow hP]
  have g : ∑ k ∈ Finset.range (e + 1 + 1), P ^ k = P * ∑ k ∈ Finset.range (e + 1), P ^ k + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ']
  have hS : 1 ≤ ∑ k ∈ Finset.range (e + 1), P ^ k := by
    rw [Finset.sum_range_succ']
    simp
  rw [g]
  nlinarith [Nat.mul_le_mul_right (sigma 1 r) hS]

lemma sigma_two_two : sigma 1 4 = 7 := by
  rw [show (4 : ℕ) = 2 ^ 2 by rfl, sigma_one_apply_prime_pow Nat.prime_two]
  simp [Finset.sum_range_succ]

lemma sigma_prime {q : ℕ} (hq : q.Prime) : sigma 1 q = q + 1 := by
  have := sigma_one_apply_prime_pow hq (i := 1)
  simp [Finset.sum_range_succ] at this
  rw [this]; ring

/-- Main bound: σ(n) ≤ n Ω(n) when Ω(n) ≥ 2. -/
lemma main : ∀ n : ℕ, 2 ≤ cardFactors n → sigma 1 n ≤ n * cardFactors n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h2
  have hn0 : n ≠ 0 := by rintro rfl; simp at h2
  have hn1 : 1 < n := by
    by_contra h
    have : n = 1 := by omega
    subst this; simp at h2
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hn1
  set P := n.primeFactors.max' hne with hPdef
  have hPmem : P ∈ n.primeFactors := Finset.max'_mem _ _
  have hPp : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPd : P ∣ n := Nat.dvd_of_mem_primeFactors hPmem
  obtain ⟨m, hm⟩ := hPd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn0 hm
  have hprimes : ∀ p, p.Prime → p ∣ m → p < P + 1 := by
    intro p hp hpm
    have : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hp, hm ▸ Dvd.dvd.mul_left hpm P, hn0⟩
    have := Finset.le_max' _ _ this
    omega
  have hσm : sigma 1 m ≤ P * m := by
    have := sigma_le (P + 1) (by have := hPp.two_le; omega) m hm0 hprimes
    simpa using this
  have hΩ : cardFactors n = cardFactors m + 1 := by
    rw [hm, cardFactors_mul hPp.ne_zero hm0, cardFactors_apply_prime hPp]; ring
  have hT := sigma_prime_mul hPp hm0
  rw [← hm] at hT
  have hP2 := hPp.two_le
  rcases (show 2 ≤ cardFactors m ∨ cardFactors m = 1 by omega) with hc | hc
  · have hmn : m < n := by
      rw [hm]
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      nlinarith
    have ihm := ih m hmn hc
    rw [hΩ, hm]
    rw [hm] at hT
    nlinarith [Nat.mul_le_mul_left P ihm]
  · have hq : m.Prime := cardFactors_eq_one_iff_prime.1 hc
    have hqP : m ≤ P := by have := hprimes m hq dvd_rfl; omega
    have hq2 := hq.two_le
    rw [sigma_prime hq] at hT
    rw [hΩ, hc]
    by_cases hP3 : P = 2
    · have : m = 2 := by omega
      subst this
      rw [hP3] at hm
      rw [hm, sigma_two_two]
      omega
    · have hP3' : 3 ≤ P := by omega
      rw [hm] at hT ⊢
      nlinarith

end P

theorem conjecture (k : ℕ) : A k ↔ k * cardFactors k < sigma 1 k := by
  constructor
  · rintro (rfl | hp)
    · simp
    · rw [cardFactors_apply_prime hp, P.sigma_prime hp]
      omega
  · intro h
    by_cases h0 : k = 0
    · subst h0; simp at h
    rcases (show cardFactors k = 0 ∨ cardFactors k = 1 ∨ 2 ≤ cardFactors k by omega)
      with h1 | h1 | h1
    · left
      rcases cardFactors_eq_zero_iff_eq_zero_or_one.1 h1 with h | h
      · exact absurd h h0
      · exact h
    · right; exact cardFactors_eq_one_iff_prime.1 h1
    · exfalso
      have := P.main k h1
      omega

end OeisA8578

#print axioms OeisA8578.conjecture
