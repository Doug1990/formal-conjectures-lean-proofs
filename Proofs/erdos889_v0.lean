import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

open Finset Nat

namespace Erdos889

/-- Restated from FormalConjectures/ErdosProblems/889.lean. -/
def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ range k, ¬ p ∣ n + i)).card

noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

namespace VS

lemma two_pow_mod (b : ℕ) (hb : 3 ≤ b) : 2 ^ b % 8 = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [pow_add]
  norm_num [Nat.mul_mod_right]

lemma three_pow_mod (e : ℕ) : 3 ^ e % 8 = 1 ∨ 3 ^ e % 8 = 3 := by
  induction e with
  | zero => left; rfl
  | succ e ih => rw [pow_succ]; omega

lemma four_pow_mod (g : ℕ) : 4 ^ g % 3 = 1 := by
  induction g with
  | zero => rfl
  | succ g ih => rw [pow_succ]; omega

lemma K' (e b : ℕ) (h : 3 ^ e + 1 = 2 ^ b) : b ≤ 2 := by
  by_contra hb
  have h1 := two_pow_mod b (by omega)
  rcases three_pow_mod e with h2 | h2 <;> omega

lemma K (e m : ℕ) (h : 3 ^ e = 2 ^ m + 1) : m ≤ 3 := by
  by_contra hm
  have h1 := two_pow_mod m (by omega)
  rcases Nat.even_or_odd e with ⟨f, hf⟩ | ⟨f, hf⟩
  · subst hf
    rw [pow_add] at h
    obtain ⟨z, hz⟩ : ∃ z, 3 ^ f = z + 1 :=
      ⟨3 ^ f - 1, by have := Nat.one_le_pow f 3 (by norm_num); omega⟩
    rw [hz] at h
    have h4 : 2 ^ m = (z + 1 + 1) * z := by linarith
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro z h4.symm)
    have hi2 := K' f i (by rw [hz]; exact hi')
    have h2i : 2 ^ i ≤ 4 :=
      calc 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hi2
        _ = 4 := by norm_num
    have h16 : 16 ≤ 2 ^ m :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hz2 : z ≤ 2 := by omega
    have h9 : (z + 1) * (z + 1) ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
    linarith
  · subst hf
    have e9 : (3 : ℕ) ^ (2 * f + 1) = 9 ^ f * 3 := by rw [pow_succ, pow_mul]; norm_num
    have h9 : 9 ^ f % 8 = 1 := by
      clear h e9
      induction f with
      | zero => rfl
      | succ f ih => rw [pow_succ]; omega
    rw [e9] at h
    omega

lemma D1 (g : ℕ) : 3 ∣ 2 ^ (2 * g + 1) + 1 := by
  have h := four_pow_mod g
  have e4 : (2 : ℕ) ^ (2 * g + 1) = 4 ^ g * 2 := by rw [pow_succ, pow_mul]; norm_num
  rw [e4]; omega

lemma D2 (g n : ℕ) (h : n + 1 = 2 ^ (g + g)) : 3 ∣ n := by
  have e4 : (2 : ℕ) ^ (g + g) = 4 ^ g := by rw [← two_mul, pow_mul]; norm_num
  rw [e4] at h
  have := four_pow_mod g
  omega

lemma P (x : ℕ) (hx : x ≠ 0) :
    (∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ x ∧ q ∣ x) ∨ ∃ e, x = x.minFac ^ e := by
  by_cases h : ∀ d : ℕ, Nat.Prime d → d ∣ x → d = x.minFac
  · exact Or.inr ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hx (fun hd hdx => h _ hd hdx)⟩
  · left
    simp only [not_forall] at h
    obtain ⟨d, hd, hdx, hne⟩ := h
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hd.one_lt.ne' (Nat.dvd_one.1 hdx)
    exact ⟨d, x.minFac, hd, Nat.minFac_prime hx1, hne, hdx, Nat.minFac_dvd x⟩

lemma nsucc (r m : ℕ) (hr : r.Prime) (h : r ∣ m + 1) : ¬ r ∣ m := fun h' =>
  hr.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h').1 h))

lemma two_le (n k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpd : p ∣ n + k) (hqd : q ∣ n + k) (hnk : n + k ≠ 0)
    (hp' : ∀ i ∈ range k, ¬ p ∣ n + i) (hq' : ∀ i ∈ range k, ¬ q ∣ n + i) :
    2 ≤ v n k := by
  unfold v
  have hsub : ({p, q} : Finset ℕ) ⊆
      (n + k).primeFactors.filter (fun p => ∀ i ∈ range k, ¬ p ∣ n + i) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpd, hnk⟩, hp'⟩
    · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hq, hqd, hnk⟩, hq'⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hpq] at this

lemma new2 (n r : ℕ) (hr : r.Prime) (hrd : r ∣ n + 2) (hr2 : r ≠ 2) :
    ∀ i ∈ range 2, ¬ r ∣ n + i := by
  intro i hi h
  rw [Finset.mem_range] at hi
  interval_cases i
  · have h0 : r ∣ n := by simpa using h
    have : r ∣ 2 := (Nat.dvd_add_right h0).1 hrd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  · have h' : r ∣ (n + 1) + 1 := by rw [show n + 1 + 1 = n + 2 by omega]; exact hrd
    exact nsucc r (n + 1) hr h' h

lemma Q (g : ℕ) (hg : 2 ≤ g) : ∃ r s, r.Prime ∧ s.Prime ∧ r ≠ s ∧ r ∣ 2 ^ (2 * g + 1) + 1 ∧
    s ∣ 2 ^ (2 * g + 1) + 1 ∧ r ≠ 2 ∧ s ≠ 2 := by
  have h3 := D1 g
  have hodd : ¬ 2 ∣ 2 ^ (2 * g + 1) + 1 := by rw [pow_succ]; omega
  rcases P (2 ^ (2 * g + 1) + 1) (by omega) with ⟨r, s, hr, hs, hrs, hrd, hsd⟩ | ⟨e, he⟩
  · refine ⟨r, s, hr, hs, hrs, hrd, hsd, ?_, ?_⟩
    · rintro rfl; exact hodd hrd
    · rintro rfl; exact hodd hsd
  · exfalso
    have hpos : 0 < 2 ^ (2 * g + 1) := pow_pos (by norm_num) _
    have hx1 : 2 ^ (2 * g + 1) + 1 ≠ 1 := by omega
    have hmp := Nat.minFac_prime hx1
    have h3' : 3 ∣ (2 ^ (2 * g + 1) + 1).minFac ^ e := by rw [← he]; exact h3
    have h3m := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hmp).1
      (Nat.prime_three.dvd_of_dvd_pow h3')
    rw [← h3m] at he
    have := K e (2 * g + 1) he.symm
    omega

end VS

theorem erdos_889.variants.v0_gt_1 :
    ∀ n : ℕ, n ∉ ({0, 1, 2, 3, 4, 7, 8, 16} : Finset ℕ) → 1 < v₀ n := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨h0, h1, h2, h3, h4, h7, h8, h16⟩ := hn
  suffices H : ∃ k, 2 ≤ v n k by
    obtain ⟨k, hk⟩ := H
    have hk' : ((2 : ℕ) : ℕ∞) ≤ (v n k : ℕ∞) := by exact_mod_cast hk
    have h12 : (1 : ℕ∞) < ((2 : ℕ) : ℕ∞) := by exact_mod_cast (show (1 : ℕ) < 2 by omega)
    exact lt_of_lt_of_le h12 (hk'.trans (le_iSup (fun k => (v n k : ℕ∞)) k))
  rcases VS.P n h0 with ⟨p, q, hp, hq, hpq, hpd, hqd⟩ | ⟨e, he⟩
  · exact ⟨0, VS.two_le n 0 p q hp hq hpq (by simpa using hpd) (by simpa using hqd)
      (by simpa using h0) (by simp) (by simp)⟩
  have hpP : n.minFac.Prime := Nat.minFac_prime h1
  rcases VS.P (n + 1) (by omega) with ⟨p, q, hp, hq, hpq, hpd, hqd⟩ | ⟨f, hf⟩
  · refine ⟨1, VS.two_le n 1 p q hp hq hpq hpd hqd (by omega) ?_ ?_⟩
    · intro i hi
      rw [Finset.mem_range] at hi
      obtain rfl : i = 0 := by omega
      simpa using VS.nsucc p n hp hpd
    · intro i hi
      rw [Finset.mem_range] at hi
      obtain rfl : i = 0 := by omega
      simpa using VS.nsucc q n hq hqd
  have hqP : (n + 1).minFac.Prime := Nat.minFac_prime (by omega)
  suffices H2 : ∃ r s, r.Prime ∧ s.Prime ∧ r ≠ s ∧ r ∣ n + 2 ∧ s ∣ n + 2 ∧ r ≠ 2 ∧ s ≠ 2 by
    obtain ⟨r, s, hr, hs, hrs, hrd, hsd, hr2, hs2⟩ := H2
    exact ⟨2, VS.two_le n 2 r s hr hs hrs hrd hsd (by omega)
      (VS.new2 n r hr hrd hr2) (VS.new2 n s hs hsd hs2)⟩
  rcases Nat.even_or_odd n with hev | hod
  · -- n is a power of 2
    have h2p : n.minFac = 2 := by
      have h2d : 2 ∣ n.minFac ^ e := by rw [← he]; exact even_iff_two_dvd.1 hev
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpP).1
        (Nat.prime_two.dvd_of_dvd_pow h2d)).symm
    rw [h2p] at he
    have he5 : 5 ≤ e := by
      by_contra hlt
      interval_cases e <;> norm_num at he <;> omega
    rcases Nat.even_or_odd e with ⟨g, hg⟩ | ⟨g, hg⟩
    · obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      obtain ⟨r, s, hr, hs, hrs, hrd, hsd, hr2, hs2⟩ := VS.Q g' (by omega)
      have hn2 : n + 2 = 2 * (2 ^ (2 * g' + 1) + 1) := by rw [he, hg]; ring
      refine ⟨r, s, hr, hs, hrs, ?_, ?_, hr2, hs2⟩
      · rw [hn2]; exact Dvd.dvd.mul_left hrd 2
      · rw [hn2]; exact Dvd.dvd.mul_left hsd 2
    · exfalso
      have h3d : 3 ∣ (n + 1).minFac ^ f := by
        rw [← hf, he, hg]; exact VS.D1 g
      have hq3 : (n + 1).minFac = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqP).1
        (Nat.prime_three.dvd_of_dvd_pow h3d)).symm
      rw [hq3, he] at hf
      have := VS.K f e hf.symm
      omega
  · -- n + 1 is a power of 2
    have h2q : (n + 1).minFac = 2 := by
      have h2d : 2 ∣ (n + 1).minFac ^ f := by
        rw [← hf]; obtain ⟨k, hk⟩ := hod; exact ⟨k + 1, by omega⟩
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqP).1
        (Nat.prime_two.dvd_of_dvd_pow h2d)).symm
    rw [h2q] at hf
    have hf4 : 4 ≤ f := by
      by_contra hlt
      interval_cases f <;> norm_num at hf <;> omega
    rcases Nat.even_or_odd f with ⟨g, hg⟩ | ⟨g, hg⟩
    · exfalso
      have h3d : 3 ∣ n.minFac ^ e := by
        rw [← he]; exact VS.D2 g n (by rw [hf, hg])
      have hp3 : n.minFac = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpP).1
        (Nat.prime_three.dvd_of_dvd_pow h3d)).symm
      rw [hp3] at he
      have := VS.K' e f (by rw [← he]; exact hf)
      omega
    · obtain ⟨r, s, hr, hs, hrs, hrd, hsd, hr2, hs2⟩ := VS.Q g (by omega)
      have hn2 : n + 2 = 2 ^ (2 * g + 1) + 1 := by rw [← hg]; omega
      exact ⟨r, s, hr, hs, hrs, hn2 ▸ hrd, hn2 ▸ hsd, hr2, hs2⟩

end Erdos889

#print axioms Erdos889.erdos_889.variants.v0_gt_1
