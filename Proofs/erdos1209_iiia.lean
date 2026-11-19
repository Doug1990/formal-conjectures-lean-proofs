import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum

open Nat Set

namespace Erdos1209

lemma lt2 (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

lemma main (n : ℕ) (hn3 : 3 ≤ n) (h : ∀ k : ℕ, (n + 2 ^ (2 ^ k)).Prime) : False := by
  have hp := h n
  have hnN : 2 ^ n < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by norm_num) (lt2 n)
  have hn2 := lt2 n
  generalize hN : 2 ^ (2 ^ n) = N at hp hnN
  have hp1 : n + N - 1 ≠ 0 := by omega
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd hp1
  have htpos : 0 < t := by obtain ⟨d, hd⟩ := ht; omega
  -- s < n
  have hs : s < n := by
    by_contra hsn
    have hsn' : n ≤ s := Nat.le_of_not_lt hsn
    have h1 : 2 ^ n ∣ n + N - 1 := by
      rw [hst]; exact (pow_dvd_pow 2 hsn').trans (dvd_mul_right _ _)
    have h2 : 2 ^ n ∣ N := by rw [← hN]; exact pow_dvd_pow 2 (lt2 n).le
    have h3 : 2 ^ n ∣ n - 1 := by
      have e : n - 1 = (n + N - 1) - N := by omega
      rw [e]; exact Nat.dvd_sub h1 h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  -- Euler mod t
  have hcop : Nat.Coprime 2 t := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rintro ⟨c, hc⟩; obtain ⟨d, hd⟩ := ht; omega
  have hE : 2 ^ φ t ≡ 1 [MOD t] := Nat.ModEq.pow_totient hcop
  have htd : t ∣ 2 ^ φ t - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hE.symm
  have hphi : 0 < φ t := Nat.totient_pos.mpr htpos
  set k' := n + φ t with hk'
  have hdiff : 2 ^ k' - 2 ^ n = 2 ^ n * (2 ^ φ t - 1) := by
    rw [hk', pow_add, Nat.mul_sub_one]
  have hdvd : n + N - 1 ∣ 2 ^ k' - 2 ^ n := by
    rw [hdiff, hst]; exact mul_dvd_mul (pow_dvd_pow 2 hs.le) htd
  obtain ⟨e, he⟩ := hdvd
  have hle : 2 ^ n ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (2 ^ k') = N * (2 ^ (n + N - 1)) ^ e := by
    rw [← pow_mul, ← he, ← hN, ← pow_add]; congr 1; omega
  -- Fermat mod p
  have hF : 2 ^ (n + N - 1) ≡ 1 [MOD n + N] := by
    have hcop2 : Nat.Coprime 2 (n + N) := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have := Nat.ModEq.pow_totient hcop2
    rwa [Nat.totient_prime hp] at this
  have hcong : 2 ^ (2 ^ k') ≡ N [MOD n + N] := by
    rw [hpow]
    have := (hF.pow e).mul_left N
    simpa using this
  have hq := h k'
  have hdq : n + N ∣ n + 2 ^ (2 ^ k') := by
    have h1 : n + 2 ^ (2 ^ k') ≡ n + N [MOD n + N] := hcong.add_left n
    exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)))
  have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdq
  have hlt : N < 2 ^ (2 ^ k') := by
    rw [← hN]; exact Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  omega

theorem erdos_1209.parts.iii.a :
    ¬ ∃ n : ℕ, ∀ k : ℕ, (n + 2 ^ (2 ^ k)).Prime := by
  rintro ⟨n, hn⟩
  rcases Nat.even_or_odd n with ⟨c, hc⟩ | ⟨c, hc⟩
  · have h1 := hn 1
    have e : n + 2 ^ (2 ^ 1) = 2 * (c + 2) := by norm_num; omega
    rw [e] at h1
    exact Nat.not_prime_mul (by norm_num) (by omega) h1
  · rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · have h5 := hn 5
      rw [show n + 2 ^ (2 ^ 5) = 641 * 6700417 by subst hc; norm_num] at h5
      exact Nat.not_prime_mul (by norm_num) (by norm_num) h5
    · exact main n (by omega) hn

end Erdos1209

#print axioms Erdos1209.erdos_1209.parts.iii.a
