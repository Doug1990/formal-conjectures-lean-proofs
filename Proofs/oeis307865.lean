import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace OeisA307865

open Nat Finset ZMod

def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

namespace P

lemma no_neg (d : ℕ) (hd : Odd d) (hd1 : 1 < d) : (1 : ZMod d) ≠ -1 := by
  have : Fact (2 < d) := ⟨by obtain ⟨k, rfl⟩ := hd; omega⟩
  exact fun h => ZMod.neg_one_ne_one h.symm

lemma odd_of_dvd (d : ℕ) (h : d ∣ 2 * n + 1) : Odd d := by
  obtain ⟨k, hk⟩ := h
  have : Odd (d * k) := hk ▸ odd_two_mul_add_one n
  exact (Nat.odd_mul.mp this).1

lemma sq_zero_pow {R : Type*} [CommRing R] (x : R) (hx : x * x = 0) (k : ℕ) :
    (1 + x) ^ k = 1 + (k : R) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have e : (1 + (k : R) * x) * (1 + x) = 1 + ((k : R) + 1) * x + (k : R) * (x * x) := by ring
    rw [e, hx]
    push_cast
    ring

lemma key (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) (b : ℕ)
    (hb : (b : ZMod (2 * n + 1)) ^ n = -1) : False := by
  obtain ⟨h1, h2, h3⟩ := h
  have hmn : (2 * n + 1 - 1) / 2 = n := by omega
  simp only [hmn] at h3
  set m := 2 * n + 1 with hm
  have hm1 : m ≠ 1 := by omega
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  set q := m / p with hqdef
  have hmpq : m = p * q := (Nat.mul_div_cancel' hpm).symm
  have hpodd : Odd p := odd_of_dvd p hpm
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, Nat.mul_zero] at hmpq; omega
  have hq1 : q ≠ 1 := by
    intro h0; rw [h0, Nat.mul_one] at hmpq; rw [hmpq] at h2; exact h2 hp
  have hqm : q ∣ m := ⟨p, by rw [hmpq, Nat.mul_comm]⟩
  have hqodd : Odd q := odd_of_dvd q hqm
  have hn0 : n ≠ 0 := by omega
  by_cases hpq : p ∣ q
  · -- non-squarefree case: c = 1 + q
    have hx : ((q : ℕ) : ZMod m) * (q : ZMod m) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      obtain ⟨s, hs⟩ := hpq
      exact ⟨s, by rw [hmpq, hs]; ring⟩
    have hu : IsUnit (((1 + q : ℕ)) : ZMod m) := by
      refine ⟨⟨1 + (q : ZMod m), 1 - (q : ZMod m), ?_, ?_⟩, ?_⟩
      · have e : (1 + (q : ZMod m)) * (1 - q) = 1 - (q : ZMod m) * q := by ring
        rw [e, hx, sub_zero]
      · have e : (1 - (q : ZMod m)) * (1 + q) = 1 - (q : ZMod m) * q := by ring
        rw [e, hx, sub_zero]
      · push_cast; rfl
    have hc := h3 (1 + q) ((ZMod.isUnit_iff_coprime _ _).mp hu)
    push_cast at hc
    rw [sq_zero_pow _ hx] at hc
    rcases hc with hc | hc
    · have e : ((n * q : ℕ) : ZMod m) = 0 := by
        push_cast
        have := congrArg (fun t => t - 1) hc
        simpa using this
      rw [ZMod.natCast_eq_zero_iff, hmpq] at e
      have hpn : p ∣ n := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hq0) e
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right hpn 2)).mp hpm
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have := congrArg (ZMod.castHom hpm (ZMod p)) hc
      simp only [map_add, map_one, map_mul, map_natCast, map_neg] at this
      rw [(ZMod.natCast_eq_zero_iff q p).mpr hpq, mul_zero, add_zero] at this
      exact no_neg p hpodd hp.one_lt this
  · -- squarefree at p: CRT
    have hcop : p.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
    have hq1' : 1 < q := Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hq0) (Ne.symm hq1)
    obtain ⟨c, hcp, hcq⟩ := Nat.chineseRemainder hcop b 1
    have hcp' : (c : ZMod p) = b := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcp
    have hcq' : (c : ZMod q) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff c 1 q).mpr hcq
      simpa using this
    have hbp : (b : ZMod p) ^ n = -1 := by
      have := congrArg (ZMod.castHom hpm (ZMod p)) hb
      simp only [map_pow, map_natCast, map_neg, map_one] at this
      exact this
    have hup : IsUnit (c : ZMod p) := by
      rw [hcp']
      have : IsUnit ((b : ZMod p) ^ n) := by rw [hbp]; exact isUnit_one.neg
      exact (isUnit_pow_iff hn0).mp this
    have huq : IsUnit (c : ZMod q) := by rw [hcq']; exact isUnit_one
    have hcm : c.Coprime m := by
      rw [hmpq]
      exact Nat.Coprime.mul_right ((ZMod.isUnit_iff_coprime _ _).mp hup)
        ((ZMod.isUnit_iff_coprime _ _).mp huq)
    rcases h3 c hcm with hc | hc
    · have := congrArg (ZMod.castHom hpm (ZMod p)) hc
      simp only [map_pow, map_natCast, map_one] at this
      rw [hcp', hbp] at this
      exact no_neg p hpodd hp.one_lt this.symm
    · have := congrArg (ZMod.castHom hqm (ZMod q)) hc
      simp only [map_pow, map_natCast, map_neg, map_one] at this
      rw [hcq', one_pow] at this
      exact no_neg q hqodd hq1' this

end P

theorem a_eq_zero_of_pseudoprime (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  show ((Ico 1 (2 * n + 1)).filter
    (fun b : ℕ => (b : ZMod (2 * n + 1)) ^ n = (-1 : ZMod (2 * n + 1)))).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ hb
  exact P.key h b hb

#print axioms a_eq_zero_of_pseudoprime

end OeisA307865
