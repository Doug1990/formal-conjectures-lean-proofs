import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Tactic.Ring

open scoped Nat

/-- Restated from FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean -/
abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

/-- Restated from FormalConjecturesForMathlib/NumberTheory/Carmichael.lean -/
def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

namespace AgohGiuga

def IsStrongGiuga (n : ℕ) : Prop :=
    n.Composite ∧ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1)

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

lemma sum_zmod (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k ≠ 0) :
    ∑ x : ZMod p, x ^ k = if p - 1 ∣ k then -1 else 0 := by
  classical
  have h := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at h
  rw [← h]
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have : Finset.univ.map emb =Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton]
    exact isUnit_iff_ne_zero
  rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
    zero_pow hk, add_zero, ← this, Finset.sum_map]
  rfl

lemma periodic_mul {M : Type*} (q : ℕ) (g : ℕ → M) (hg : ∀ k, g (k + q) = g k) (j x : ℕ) :
    g (j * q + x) = g x := by
  induction j with
  | zero => simp
  | succ j ihj =>
    rw [Nat.succ_mul, show j * q + q + x = (j * q + x) + q by omega, hg, ihj]

lemma sum_periodic {M : Type*} [AddCommMonoid M] (q : ℕ) (g : ℕ → M)
    (hg : ∀ k, g (k + q) = g k) (m : ℕ) :
    ∑ k ∈ Finset.range (m * q), g k = m • ∑ k ∈ Finset.range q, g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => periodic_mul q g hg m x)

lemma sum_range_eq_univ (p : ℕ) [NeZero p] {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ k ∈ Finset.range p, f (k : ZMod p) = ∑ j : ZMod p, f j := by
  refine Finset.sum_nbij' (fun k : ℕ => (k : ZMod p)) (fun j => j.val) ?_ ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro j _; simpa using ZMod.val_lt j
  · intro x hx
    simp only [Finset.mem_range] at hx
    exact ZMod.val_cast_of_lt hx
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro x _; rfl

lemma strong_mod (n p : ℕ) [hp : Fact p.Prime] (hpn : p ∣ n) (hn : 2 ≤ n) :
    ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) =
      1 + ((n / p : ℕ) : ZMod p) * (if p - 1 ∣ n - 1 then -1 else 0) := by
  have hk : n - 1 ≠ 0 := by omega
  have e1 : Finset.Ioo 0 n = (Finset.range n).erase 0 := by ext i; simp; omega
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sum, e1,
    Finset.sum_erase _ (by simp [zero_pow hk])]
  simp only [Nat.cast_pow]
  obtain ⟨c, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left c hp.out.pos, show Finset.range (p * c) = Finset.range (c * p) by
    rw [Nat.mul_comm], sum_periodic p _ ?_ c, sum_range_eq_univ p (fun x => x ^ (p * c - 1)),
    sum_zmod p _ hk, nsmul_eq_mul]
  intro k
  simp

lemma fermat (p b e : ℕ) (pp : p.Prime) (hpb : ¬ p ∣ b) (he : p - 1 ∣ e) (hb : 1 ≤ b) :
    p ∣ b ^ e - 1 := by
  have := Fact.mk pp
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow,
    Nat.cast_one, sub_eq_zero]
  obtain ⟨t, rfl⟩ := he
  rw [pow_mul, ZMod.pow_card_sub_one_eq_one, one_pow]
  rwa [Ne, ZMod.natCast_eq_zero_iff]

lemma strong_cond (a : ℕ) (ha : IsStrongGiuga a) :
    ∀ p ∈ a.primeFactors, p - 1 ∣ a - 1 ∧ p ∣ a / p - 1 := by
  obtain ⟨hc, hdiv⟩ := ha
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have hpa := Nat.dvd_of_mem_primeFactors hp
  have := Fact.mk pp
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 (dvd_trans hpa hdiv)
  rw [strong_mod a p hpa (by omega)] at h0
  by_cases hd : p - 1 ∣ a - 1
  · refine ⟨hd, ?_⟩
    rw [if_pos hd, mul_neg_one, ← sub_eq_add_neg, sub_eq_zero] at h0
    have h1 : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) pp.pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_one, sub_eq_zero]
    exact h0.symm
  · rw [if_neg hd, mul_zero, add_zero] at h0
    exact absurd h0 one_ne_zero

lemma carm_of_cond (a : ℕ) (hc : a.Composite) (h : ∀ p ∈ a.primeFactors, p - 1 ∣ a - 1)
    (hs : Squarefree a) : IsCarmichael a := by
  intro b hb hcop
  refine ⟨?_, hc.2, hc.1⟩
  show a ∣ b ^ (a - 1) - 1
  refine dvd_of_sqf a _ hs fun p hp => ?_
  have pp := Nat.prime_of_mem_primeFactors hp
  have hpa := Nat.dvd_of_mem_primeFactors hp
  exact fermat p b (a - 1) pp ((Nat.Prime.coprime_iff_not_dvd pp).1
    (Nat.Coprime.coprime_dvd_left hpa hcop)) (h p hp) hb

theorem agoh_giuga.variants.isStrongGiuga_implies_isCarmichael
    (a : ℕ) (ha : IsStrongGiuga a) : IsCarmichael a := by
  have hcond := strong_cond a ha
  exact carm_of_cond a ha.1 (fun p hp => (hcond p hp).1)
    (sq_free a (by have := ha.1.1; omega) fun p hp => (hcond p hp).2)

/-! ### Giuga's characterisation: strong Giuga ↔ Carmichael ∧ weak Giuga -/

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

lemma sum_iff {n : ℕ} (hn : n.Composite) :
    (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔
      ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := by
  have hn0 : n ≠ 0 := by omega
  rw [rat_iff n hn.1]
  constructor
  · intro h p hp
    exact (T_split n p hn0 hp).1 (dvd_trans (Nat.dvd_of_mem_primeFactors hp) h)
  · intro h
    exact dvd_of_sqf n _ (sq_free n hn0 h) fun p hp => (T_split n p hn0 hp).2 (h p hp)

/-- One direction of Korselt's criterion (for squarefree `a`). -/
lemma carm_dvd (a p : ℕ) (hc : a.Composite) (hs : Squarefree a) (hcar : IsCarmichael a)
    (hp : p ∈ a.primeFactors) : p - 1 ∣ a - 1 := by
  have pp := Nat.prime_of_mem_primeFactors hp
  have hpa := Nat.dvd_of_mem_primeFactors hp
  have := Fact.mk pp
  obtain ⟨k, hk⟩ := hpa
  have hpk : ¬ p ∣ k := by
    rintro ⟨j, rfl⟩
    have := (Nat.squarefree_iff_prime_squarefree.1 hs) p pp
    exact this ⟨j, by rw [hk]; ring⟩
  have hcop : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd pp).2 hpk
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · rw [hk, mul_one] at hc; exact absurd pp hc.2
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop ((g : ZMod p).val) 1
  have hbk : Nat.gcd b k = 1 := by
    rw [Nat.ModEq.gcd_eq hb2, Nat.gcd_one_left]
  have hb0 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.gcd_zero_left] at hbk; omega
    · exact h
  have hbg : (b : ZMod p) = (g : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hb1, ZMod.natCast_zmod_val]
  have hpb : ¬ p ∣ b := by
    rw [← ZMod.natCast_eq_zero_iff, hbg]; exact g.ne_zero
  have hcopab : a.Coprime b := by
    rw [hk]
    exact Nat.coprime_mul_iff_left.2
      ⟨(Nat.Prime.coprime_iff_not_dvd pp).2 hpb, Nat.Coprime.symm hbk⟩
  have hdiv : p ∣ b ^ (a - 1) - 1 :=
    dvd_trans ⟨k, hk⟩ (hcar b hb0 hcopab).1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb0), Nat.cast_pow,
    Nat.cast_one, sub_eq_zero, hbg] at hdiv
  have hg1 : g ^ (a - 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdiv, Units.val_one])
  have := orderOf_dvd_of_pow_eq_one hg1
  rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units p] at this

theorem isStrongGiuga_iff {a : ℕ} (ha : a.Composite) :
    IsStrongGiuga a ↔ IsCarmichael a ∧ ∃ n : ℕ, ∑ p ∈ a.primeFactors, (1 / p : ℚ) - 1 / a = n := by
  rw [sum_iff ha]
  constructor
  · intro h
    exact ⟨agoh_giuga.variants.isStrongGiuga_implies_isCarmichael a h,
      fun p hp => (strong_cond a h p hp).2⟩
  · rintro ⟨hcar, h⟩
    have hs := sq_free a (by omega) h
    refine ⟨ha, dvd_of_sqf a _ hs fun p hp => ?_⟩
    have pp := Nat.prime_of_mem_primeFactors hp
    have hpa := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk pp
    rw [← ZMod.natCast_eq_zero_iff, strong_mod a p hpa (by omega),
      if_pos (carm_dvd a p ha hs hcar hp), mul_neg_one, ← sub_eq_add_neg, sub_eq_zero]
    have h1 : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) pp.pos
    have h2 := (ZMod.natCast_eq_zero_iff _ p).2 (h p hp)
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at h2
    exact h2.symm

end AgohGiuga

#print axioms AgohGiuga.agoh_giuga.variants.isStrongGiuga_implies_isCarmichael
#print axioms AgohGiuga.isStrongGiuga_iff
