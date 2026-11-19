import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic

namespace OeisA91669

open Nat BigOperators

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator

namespace Q

def P (m : ℕ) : ℕ := ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)

lemma a_eq (m : ℕ) (hm : m ≠ 0) : a m = (2 ^ (m - 1) * P m) / m ! := by
  rw [a, if_neg hm]; rfl

lemma P_pos (m : ℕ) : 0 < P m := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
  omega

lemma P_odd (m : ℕ) : ¬ 2 ∣ P m := by
  intro h
  obtain ⟨k, hk, hd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
  rw [Finset.mem_Ico] at hk
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
  obtain ⟨u, hu⟩ := hd
  obtain ⟨v, hv⟩ := h2
  omega

lemma two_ne_zero' (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h'
  exact hp2 this

lemma fermat (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : q ∣ 2 ^ (q - 1) - 1 := by
  have := Fact.mk hq
  have h1 : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  push_cast
  rw [ZMod.pow_card_sub_one_eq_one (two_ne_zero' q hq2), sub_self]

lemma lte (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (j : ℕ) (hj : j ≠ 0) :
    q ^ (1 + padicValNat q j) ∣ 2 ^ ((q - 1) * j) - 1 := by
  have := Fact.mk hq
  have hodd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hyx : 1 < 2 ^ (q - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxy := fermat q hq hq2
  have hx : ¬ q ∣ 2 ^ (q - 1) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    exact hq2 this
  have key := padicValNat.pow_sub_pow (p := q) hodd hyx (by simpa using hxy) hx hj
  rw [one_pow, ← pow_mul] at key
  have h1 : 1 ≤ padicValNat q (2 ^ (q - 1) - 1) :=
    one_le_padicValNat_of_dvd (by omega) hxy
  refine (pow_dvd_pow q ?_).trans (pow_padicValNat_dvd (p := q))
  rw [key]
  omega

lemma Qprod (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (t : ℕ) :
    q ^ (t + padicValNat q t !) ∣ ∏ j ∈ Finset.Ico 1 (t + 1), (2 ^ ((q - 1) * j) - 1) := by
  have := Fact.mk hq
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ t + 1), Nat.factorial_succ,
      padicValNat.mul (by omega) (factorial_ne_zero t)]
    rw [show t + 1 + (padicValNat q (t + 1) + padicValNat q t !) =
      (t + padicValNat q t !) + (1 + padicValNat q (t + 1)) by omega, pow_add]
    exact mul_dvd_mul ih (lte q hq hq2 (t + 1) (by omega))

lemma sub_prod (q : ℕ) (hq : 2 ≤ q) (m t : ℕ) (h : (q - 1) * t ≤ m - 1) :
    ∏ j ∈ Finset.Ico 1 (t + 1), (2 ^ ((q - 1) * j) - 1) ∣ P m := by
  have e : ∏ j ∈ Finset.Ico 1 (t + 1), (2 ^ ((q - 1) * j) - 1) =
      ∏ k ∈ (Finset.Ico 1 (t + 1)).image (fun j => (q - 1) * j), (2 ^ k - 1) :=
    (Finset.prod_image (f := fun k => 2 ^ k - 1) (s := Finset.Ico 1 (t + 1))
      (g := fun j => (q - 1) * j) (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (show 0 < q - 1 by omega) hxy)).symm
  rw [e]
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  simp only [Finset.mem_image, Finset.mem_Ico] at hk ⊢
  obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hk
  have := Nat.mul_le_mul_left (q - 1) (show j ≤ t by omega)
  have := Nat.mul_le_mul_left (q - 1) (show 1 ≤ j by omega)
  omega

lemma qpart (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (m : ℕ) :
    q ^ ((m - 1) / (q - 1) + padicValNat q ((m - 1) / (q - 1))!) ∣ P m :=
  (Qprod q hq hq2 _).trans (sub_prod q hq.two_le m _ (Nat.mul_div_le (m - 1) (q - 1)))

lemma vfact (q : ℕ) [hq : Fact q.Prime] (m : ℕ) :
    padicValNat q m ! = m / q + padicValNat q (m / q)! := by
  conv_lhs => rw [← Nat.div_add_mod m q]
  rw [padicValNat_factorial_mul_add _ (Nat.mod_lt _ hq.out.pos), padicValNat_factorial_mul]
  omega

lemma vfact_mono (q : ℕ) [Fact q.Prime] (s t : ℕ) (h : s ≤ t) :
    padicValNat q s ! ≤ padicValNat q t ! :=
  (padicValNat_dvd_iff_le (factorial_ne_zero t)).mp
    ((pow_padicValNat_dvd (p := q)).trans (Nat.factorial_dvd_factorial h))

lemma two_fact (m : ℕ) (hm : 1 ≤ m) : padicValNat 2 m ! ≤ m - 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [vfact 2 m]
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m / 2 = 0 := by omega
      rw [this]
      simp
    · have := ih (m / 2) (by omega) (by omega)
      omega

lemma exact_div (m : ℕ) (hm : 1 ≤ m) : m ! ∣ 2 ^ (m - 1) * P m := by
  have hX : 2 ^ (m - 1) * P m ≠ 0 := Nat.mul_ne_zero (by positivity) (P_pos m).ne'
  rw [← Nat.factorization_prime_le_iff_dvd (factorial_ne_zero m) hX]
  intro q hq
  have := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq, ← padicValNat_dvd_iff_le hX]
  rcases hq.eq_two_or_odd' with rfl | hodd
  · exact (pow_dvd_pow 2 (two_fact m hm)).trans (Dvd.intro _ rfl)
  · have hq2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      omega
    refine (pow_dvd_pow q ?_).trans ((qpart q hq hq2 m).trans (Dvd.intro_left _ rfl))
    rw [vfact q m]
    have hst : m / q ≤ (m - 1) / (q - 1) := by
      rcases Nat.lt_or_ge m q with h | h
      · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
      · rw [Nat.le_div_iff_mul_le (by have := hq.two_le; omega), Nat.mul_sub_one]
        have := Nat.div_mul_le_self m q
        have := Nat.div_pos h hq.pos
        omega
    exact Nat.add_le_add hst (vfact_mono q _ _ hst)

lemma vfact_two_pow (k : ℕ) : padicValNat 2 (2 ^ k)! = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm, padicValNat_factorial_mul, ih]
    have := Nat.one_le_two_pow (n := k)
    omega

end Q

open Q in
theorem prime_and_primitive_root_of_dvd (n : ℕ) (hn : n > 2) : n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdvd
  rw [show m + 1 - 2 = m - 1 by omega] at hdvd
  have hm : 1 ≤ m := by omega
  have hA : a m * m ! = 2 ^ (m - 1) * P m := by
    rw [a_eq m (by omega)]
    exact Nat.div_mul_cancel (exact_div m hm)
  have hkey : (m + 1)! ∣ 2 ^ (m - 1) * P m + 2 ^ (m - 1) * m ! := by
    rw [Nat.factorial_succ, ← hA, ← Nat.add_mul]
    exact Nat.mul_dvd_mul_right hdvd _
  -- no odd prime q with q ∣ n, q ≠ n
  have hA_case : ∀ q, q.Prime → q ≠ 2 → q ∣ m + 1 → q = m + 1 := by
    intro q hq hq2 hqn
    by_contra hne
    have := Fact.mk hq
    obtain ⟨r, hr⟩ := hqn
    have hr2 : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h | h
      · interval_cases r <;> simp_all
      · exact h
    set e := padicValNat q m ! with he
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have h1 : m / q < r := by
      rw [Nat.div_lt_iff_lt_mul hq.pos]
      have := Nat.mul_comm q r
      omega
    have h2 : r ≤ (m - 1) / (q - 1) := by
      rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_sub_one]
      have := Nat.mul_comm q r
      have : q * 2 ≤ q * r := Nat.mul_le_mul_left q hr2
      omega
    have hX : q ^ (e + 1) ∣ 2 ^ (m - 1) * P m := by
      refine (pow_dvd_pow q ?_).trans ((qpart q hq hq2 m).trans (Dvd.intro_left _ rfl))
      rw [he, vfact q m]
      have := vfact_mono q (m / q) ((m - 1) / (q - 1)) (by omega)
      omega
    have hF : q ^ (e + 1) ∣ (m + 1)! := by
      rw [Nat.factorial_succ, pow_succ, mul_comm, hr]
      exact mul_dvd_mul (dvd_mul_right q r) (pow_padicValNat_dvd (p := q))
    have h3 : q ^ (e + 1) ∣ 2 ^ (m - 1) * m ! :=
      (Nat.dvd_add_right hX).mp (hF.trans hkey)
    have hcop : Nat.Coprime (q ^ (e + 1)) (2 ^ (m - 1)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    exact pow_succ_padicValNat_not_dvd (factorial_ne_zero m)
      (Nat.Coprime.dvd_of_dvd_mul_left hcop h3)
  -- n is not a power of two
  have hB_case : ∀ k, m + 1 ≠ 2 ^ k := by
    intro k hk
    have hv : padicValNat 2 (m + 1)! = m := by rw [hk, vfact_two_pow]; omega
    have h1 : 2 ^ m ∣ 2 ^ (m - 1) * (P m + m !) := by
      rw [Nat.mul_add]
      exact (hv ▸ pow_padicValNat_dvd (p := 2)).trans hkey
    rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega] at h1
    have h2 : 2 ∣ P m + m ! := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    have h3 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
    exact P_odd m ((Nat.dvd_add_left h3).mp h2)
  have hprime : (m + 1).Prime := by
    obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (show m + 1 ≠ 0 by omega)
    by_cases ho1 : o = 1
    · exact absurd (by rw [hko, ho1, mul_one]) (hB_case k)
    · have hmf := Nat.minFac_prime ho1
      have hq2 : o.minFac ≠ 2 := by
        intro h2
        have := Nat.minFac_dvd o
        rw [h2] at this
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr this)
      have := hA_case o.minFac hmf hq2 (hko ▸ Dvd.dvd.mul_left (Nat.minFac_dvd o) _)
      rw [← this]
      exact hmf
  refine ⟨hprime, ?_⟩
  have := Fact.mk hprime
  have hp2 : m + 1 ≠ 2 := by omega
  have h2 := two_ne_zero' (m + 1) hp2
  rw [Nat.totient_prime hprime, Nat.add_sub_cancel]
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) ?_ ?_
  · have := ZMod.pow_card_sub_one_eq_one h2
    simpa using this
  · intro l hl0 hlm hl
    have hPl : (m + 1) ∣ P m := by
      have hd : (m + 1) ∣ 2 ^ l - 1 := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        rw [hl, sub_self]
      exact hd.trans (Finset.dvd_prod_of_mem _ (by rw [Finset.mem_Ico]; omega))
    have hPz : (P m : ZMod (m + 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hPl
    have hW : (m ! : ZMod (m + 1)) = -1 := by
      have := ZMod.wilsons_lemma (p := m + 1)
      simpa using this
    have hAz : ((a m * m ! : ℕ) : ZMod (m + 1)) = ((2 ^ (m - 1) * P m : ℕ) : ZMod (m + 1)) := by
      rw [hA]
    push_cast at hAz
    rw [hW, hPz, mul_zero, mul_neg_one, neg_eq_zero] at hAz
    have hd : ((a m + 2 ^ (m - 1) : ℕ) : ZMod (m + 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hd
    rw [hAz, zero_add] at hd
    exact h2 (pow_eq_zero_iff (by omega) |>.mp hd)

end OeisA91669

#print axioms OeisA91669.prime_and_primitive_root_of_dvd
