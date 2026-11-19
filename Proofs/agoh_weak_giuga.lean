import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Nat

/-- Restated from FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean -/
abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

namespace AgohGiuga

def IsWeakGiuga (n : ℕ) : Prop :=
    n.Composite ∧ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ φ n

lemma ioo_eq (n : ℕ) : Finset.Ioo 0 n = Finset.Ioc 0 (n - 1) := by
  ext i; simp; omega

lemma sum_mod (p k m : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hpk : p - 1 ∣ k) :
    ((∑ i ∈ Finset.Ioc 0 m, i ^ k : ℕ) : ZMod p) =
      ((Finset.filter (fun i => ¬ p ∣ i) (Finset.Ioc 0 m)).card : ZMod p) := by
  rw [Nat.cast_sum, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨t, rfl⟩ := hpk
  by_cases h : p ∣ i
  · rw [if_neg (not_not.2 h), Nat.cast_pow, (ZMod.natCast_eq_zero_iff i p).2 h, zero_pow hk]
  · rw [if_pos h, Nat.cast_pow, pow_mul, ZMod.pow_card_sub_one_eq_one, one_pow]
    rwa [Ne, ZMod.natCast_eq_zero_iff]

lemma key (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    p ∣ (1 + ∑ i ∈ Finset.Ioo 0 n, i ^ φ n) + (n / p - 1) := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff]
  have hk : φ n ≠ 0 := (Nat.totient_pos.2 hn).ne'
  have hpk : p - 1 ∣ φ n := by
    rw [← Nat.totient_prime hp]; exact Nat.totient_dvd_of_dvd hpn
  have hc : (Finset.filter (fun i => p ∣ i) (Finset.Ioc 0 (n - 1))).card +
      (Finset.filter (fun i => ¬ p ∣ i) (Finset.Ioc 0 (n - 1))).card = n - 1 := by
    rw [Finset.card_filter_add_card_filter_not, Nat.card_Ioc]; simp
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hc
  have hd : (n - 1 + 1) / p = (n - 1) / p + 1 :=
    Nat.succ_div_of_dvd (by rwa [Nat.sub_add_cancel hn])
  rw [Nat.sub_add_cancel hn] at hd
  have h2 : 1 + (Finset.filter (fun i => ¬ p ∣ i) (Finset.Ioc 0 (n - 1))).card + (n / p - 1) = n := by
    generalize (Finset.filter (fun i => ¬ p ∣ i) (Finset.Ioc 0 (n - 1))).card = c at hc ⊢
    generalize (n - 1) / p = q at hc hd
    generalize n / p = r at hd ⊢
    omega
  rw [ioo_eq, Nat.cast_add, Nat.cast_add, sum_mod p _ _ hk hpk]
  have h3 := congrArg (Nat.cast : ℕ → ZMod p) h2
  push_cast at h3
  rw [Nat.cast_one, h3]
  exact (ZMod.natCast_eq_zero_iff n p).2 hpn

lemma sq_free (n : ℕ) (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hxx
  have hx' : x.Prime := hx
  have hxn : x ∣ n := dvd_trans (Dvd.intro x rfl) hxx
  have hmem : x ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hx', hxn, hn⟩
  have h1 := h x hmem
  have h2 : x ∣ n / x := Nat.dvd_div_of_mul_dvd hxx
  have h3 : 1 ≤ n / x := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hxn) hx'.pos
  have h4 : x ∣ 1 := by
    have := Nat.dvd_sub h2 h1
    rwa [Nat.sub_sub_self h3] at this
  exact hx'.one_lt.ne' (Nat.dvd_one.1 h4)

lemma dvd_of_sqf (n X : ℕ) (hs : Squarefree n) (h : ∀ p ∈ n.primeFactors, p ∣ X) : n ∣ X := by
  rw [← Nat.prod_primeFactors_of_squarefree hs]
  exact Finset.prod_primes_dvd X (fun a ha => (Nat.prime_of_mem_primeFactors ha).prime) h

theorem isWeakGiuga_iff_prime_dvd {n : ℕ} (hn : n.Composite) :
    IsWeakGiuga n ↔ ∀ p ∈ n.primeFactors, p ∣ (n / p - 1) := by
  constructor
  · rintro ⟨_, hdiv⟩ p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hk := key n p hpp hpn (by omega)
    exact (Nat.dvd_add_right (dvd_trans hpn hdiv)).1 hk
  · intro h
    refine ⟨hn, dvd_of_sqf n _ (sq_free n (by omega) h) fun p hp => ?_⟩
    have hk := key n p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      (by omega)
    exact (Nat.dvd_add_left (h p hp)).1 hk

lemma T_split (n p : ℕ) (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    p ∣ (∑ q ∈ n.primeFactors, n / q) - 1 ↔ p ∣ n / p - 1 := by
  have pp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  rw [← Finset.add_sum_erase _ _ hp]
  have hR : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q := Finset.dvd_sum fun q hq => by
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqn := Nat.dvd_of_mem_primeFactors hq
    have : p ∣ q * (n / q) := by rwa [Nat.mul_div_cancel' hqn]
    rcases pp.dvd_mul.1 this with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq pp hqprime).1 h) (Ne.symm hqp)
    · exact h
  have h1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) pp.pos
  rw [show n / p + ∑ q ∈ n.primeFactors.erase p, n / q - 1
      = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q by omega]
  exact Nat.dvd_add_left hR

lemma rat_iff (n : ℕ) (hn : 1 < n) :
    (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔
      n ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hT1 : 1 ≤ ∑ q ∈ n.primeFactors, n / q := by
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, by omega⟩
    have h1 := Finset.single_le_sum (f := fun q => n / q) (fun _ _ => Nat.zero_le _) hmem
    have h2 := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    omega
  have hX : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) - 1 / n
      = (((∑ q ∈ n.primeFactors, n / q) - 1 : ℕ) : ℚ) / n := by
    rw [eq_div_iff hn0, Nat.cast_sub hT1, Nat.cast_sum, Nat.cast_one, sub_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hq)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)]
      ring
    · exact one_div_mul_cancel hn0
  rw [hX]
  constructor
  · rintro ⟨m, hm⟩
    rw [div_eq_iff hn0] at hm
    exact ⟨m, by exact_mod_cast hm.trans (mul_comm _ _)⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm, Nat.cast_mul, mul_div_cancel_left₀ _ hn0]⟩

theorem isWeakGiuga_iff_sum_primeFactors {n : ℕ} (hn : n.Composite) :
    IsWeakGiuga n ↔ ∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m := by
  have hn0 : n ≠ 0 := by omega
  rw [isWeakGiuga_iff_prime_dvd hn, rat_iff n hn.1]
  constructor
  · intro h
    exact dvd_of_sqf n _ (sq_free n hn0 h) fun p hp => (T_split n p hn0 hp).2 (h p hp)
  · intro h p hp
    exact (T_split n p hn0 hp).1 (dvd_trans (Nat.dvd_of_mem_primeFactors hp) h)

end AgohGiuga

#print axioms AgohGiuga.isWeakGiuga_iff_prime_dvd
#print axioms AgohGiuga.isWeakGiuga_iff_sum_primeFactors
