import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace OeisA211417

def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

namespace T7

lemma div_eq (m q c d : ℕ) (hc : 0 < c) (h : c * d = 30) :
    d * m / q = 30 * m / q / c := by
  rw [Nat.div_div_eq_div_mul, ← h, mul_comm q c, mul_assoc,
    Nat.mul_div_mul_left _ _ hc]

lemma key (m q : ℕ) :
    15 * m / q + 10 * m / q + 6 * m / q ≤ 30 * m / q + m / q := by
  have h2 := div_eq m q 2 15 (by omega) (by omega)
  have h3 := div_eq m q 3 10 (by omega) (by omega)
  have h5 := div_eq m q 5 6 (by omega) (by omega)
  have h30 := div_eq m q 30 1 (by omega) (by omega)
  rw [one_mul] at h30
  rw [h2, h3, h5, h30]
  generalize 30 * m / q = J
  omega

/-- a layer q ∣ 2m+1 with q ∉ {3,5,7} contributes at least 1 -/
lemma key7 (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 2 * m + 1) (h3 : q ≠ 3) (h5 : q ≠ 5)
    (h7 : q ≠ 7) :
    15 * m / q + 10 * m / q + 6 * m / q + 1 ≤ 30 * m / q + m / q := by
  obtain ⟨k, hk⟩ := hd
  rcases Nat.lt_or_ge q 15 with hlt | hge
  · interval_cases q <;> omega
  · have e2 := div_eq m q 2 15 (by omega) (by omega)
    have e3 := div_eq m q 3 10 (by omega) (by omega)
    have e5 := div_eq m q 5 6 (by omega) (by omega)
    have e30 := div_eq m q 30 1 (by omega) (by omega)
    rw [one_mul] at e30
    rw [e2, e3, e5, e30]
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
    · have : q * (2 * t) = 2 * (q * t) := by ring
      omega
    · have hr : q * (2 * t + 1) = 2 * (q * t) + q := by ring
      have hs : q * (30 * t + 14) = 30 * (q * t) + 14 * q := by ring
      have e : 30 * m = q * (30 * t + 14) + (q - 15) := by omega
      have hJ : 30 * m / q = 30 * t + 14 := by
        rw [e, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
      rw [hJ]
      omega

/-- the top layers (q ≤ 30m < 6q) contribute 1 -/
lemma top (m q : ℕ) (hq0 : 0 < q) (h1 : q ≤ 30 * m) (h6 : 30 * m < 6 * q) :
    15 * m / q + 10 * m / q + 6 * m / q + 1 ≤ 30 * m / q + m / q := by
  have e2 := div_eq m q 2 15 (by omega) (by omega)
  have e3 := div_eq m q 3 10 (by omega) (by omega)
  have e5 := div_eq m q 5 6 (by omega) (by omega)
  have e30 := div_eq m q 30 1 (by omega) (by omega)
  rw [one_mul] at e30
  rw [e2, e3, e5, e30]
  have hJ1 : 0 < 30 * m / q := Nat.div_pos h1 hq0
  have hJ2 : 30 * m / q < 6 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  generalize 30 * m / q = J at hJ1 hJ2 ⊢
  omega

lemma sum_bound' (b v c : ℕ) (L R : ℕ → ℕ) (h0 : ∀ i, L i ≤ R i)
    (hv : v ≤ c + ((Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i)).card) :
    v + ∑ i ∈ Finset.Ico 1 b, L i ≤ c + ∑ i ∈ Finset.Ico 1 b, R i := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 b) (fun i => L i + 1 ≤ R i) L,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 b) (fun i => L i + 1 ≤ R i) R]
  have hA : ∑ i ∈ (Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i), (L i + 1) ≤
      ∑ i ∈ (Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i), R i :=
    Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
  have hc : ∑ i ∈ (Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i), (fun _ => (1 : ℕ)) i =
      ((Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i)).card := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), mul_one]
  rw [Finset.sum_add_distrib, hc] at hA
  have hB : ∑ i ∈ (Finset.Ico 1 b).filter (fun i => ¬ (L i + 1 ≤ R i)), L i ≤
      ∑ i ∈ (Finset.Ico 1 b).filter (fun i => ¬ (L i + 1 ≤ R i)), R i :=
    Finset.sum_le_sum (fun i _ => h0 i)
  omega

lemma ne_of_prime_pow (p i r : ℕ) (hp : p.Prime) (hr : r.Prime) (hi : 1 ≤ i) (hpr : p ≠ r) :
    p ^ i ≠ r := by
  intro h
  have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
  rw [h] at hd
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd)

theorem main (n : ℕ) (hn : 1 ≤ n) :
    (2 * n + 1) * (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      7 * (Nat.factorial (30 * n) * Nat.factorial n) := by
  have hx : 2 * n + 1 ≠ 0 := by omega
  have f15 := Nat.factorial_ne_zero (15 * n)
  have f10 := Nat.factorial_ne_zero (10 * n)
  have f6 := Nat.factorial_ne_zero (6 * n)
  have f30 := Nat.factorial_ne_zero (30 * n)
  have f1 := Nat.factorial_ne_zero n
  have h7 : (7 : ℕ) ≠ 0 := by omega
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6))
    (Nat.mul_ne_zero h7 (Nat.mul_ne_zero f30 f1))]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6),
    padicValNat.mul (Nat.mul_ne_zero f15 f10) f6, padicValNat.mul f15 f10,
    padicValNat.mul h7 (Nat.mul_ne_zero f30 f1), padicValNat.mul f30 f1]
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * n) < Nat.log p (30 * n) + 1 := fun c hc =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right n hc))
  have hb1 : Nat.log p n < Nat.log p (30 * n) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial (hb 15 (by omega)), padicValNat_factorial (hb 10 (by omega)),
    padicValNat_factorial (hb 6 (by omega)), padicValNat_factorial (hb 30 (by omega)),
    padicValNat_factorial hb1]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hc7 : p = 7 → padicValNat p 7 = 1 := fun h => by subst h; exact padicValNat_self
  generalize padicValNat p 7 = c at hc7 ⊢
  have hdv : p ^ padicValNat p (2 * n + 1) ∣ 2 * n + 1 := pow_padicValNat_dvd
  have hpv : p ^ padicValNat p (2 * n + 1) ≤ 2 * n + 1 := Nat.le_of_dvd (by omega) hdv
  have hL1 : p ^ Nat.log p (30 * n) ≤ 30 * n := Nat.pow_log_le_self p (by omega)
  have hL2 : 30 * n < p ^ (Nat.log p (30 * n) + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
  generalize padicValNat p (2 * n + 1) = v at hdv hpv ⊢
  generalize Nat.log p (30 * n) = L at hL1 hL2 ⊢
  have hlt : ∀ i, p ^ i ≤ 30 * n → i < L + 1 := fun i h => by
    by_contra hc
    have := Nat.pow_le_pow_right hp.pos (show L + 1 ≤ i by omega)
    omega
  have hvL : v ≤ L := by have := hlt v (by omega); omega
  refine sum_bound' (L + 1) v c (fun i => 15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i)
    (fun i => 30 * n / p ^ i + n / p ^ i) (fun i => key n (p ^ i)) ?_
  have good : ∀ i, 1 ≤ i → i ≤ v → p ^ i ≠ 3 → p ^ i ≠ 5 → p ^ i ≠ 7 →
      i ∈ (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i) := by
    intro i hi1 hiv h3 h5 h7
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hi1, by omega⟩, ?_⟩
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact key7 n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) h3 h5 h7
  have topg : ∀ i, 1 ≤ i → i ≤ L → 30 * n < 6 * p ^ i →
      i ∈ (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i) := by
    intro i hi1 hiL h6
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hi1, by omega⟩, ?_⟩
    have hle : p ^ i ≤ 30 * n := (Nat.pow_le_pow_right hp.pos hiL).trans hL1
    exact top n (p ^ i) (pow_pos hp.pos i) hle h6
  have hcard : (Finset.Ico 1 (v + 1)).card = v := by rw [Nat.card_Ico]; omega
  -- p = 3 or p = 5: replace the bad layer i = 1 by the top layer L
  have small : ∀ r, r = 3 ∨ r = 5 → p = r →
      v ≤ ((Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i)).card := by
    intro r hr hpr
    subst hpr
    have hv1 : v + 1 ≤ L := by
      have e : p ^ (v + 1) = p ^ v * p := pow_succ _ _
      have : p ^ v * p ≤ 30 * n := by
        rcases hr with rfl | rfl <;> omega
      have := hlt (v + 1) (by omega)
      omega
    have e1 : p ^ (L + 1) = p ^ L * p := pow_succ _ _
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn
          (fun i => if i = 1 then L else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi ⊢
      split_ifs with h1
      · refine topg _ (by omega) le_rfl ?_
        rcases hr with rfl | rfl <;> omega
      · have h4 : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
        have e2 : p ^ 2 = p * p := sq p
        refine good i hi.1 (by omega) ?_ ?_ ?_ <;> rcases hr with rfl | rfl <;> omega
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
      simp only at hij
      split_ifs at hij <;> omega
  by_cases hp3 : p = 3
  · have := small 3 (Or.inl rfl) hp3; omega
  by_cases hp5 : p = 5
  · have := small 5 (Or.inr rfl) hp5; omega
  by_cases hp7 : p = 7
  · have hc : c = 1 := hc7 hp7
    subst hp7
    have hcard2 : (Finset.Ico 2 (v + 1)).card + 1 ≥ v := by rw [Nat.card_Ico]; omega
    have : (Finset.Ico 2 (v + 1)).card ≤ _ := Finset.card_le_card (s := Finset.Ico 2 (v + 1))
      (t := (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / 7 ^ i + 10 * n / 7 ^ i +
        6 * n / 7 ^ i + 1 ≤ 30 * n / 7 ^ i + n / 7 ^ i)) (by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h4 : 7 ^ 2 ≤ 7 ^ i := Nat.pow_le_pow_right (by omega) hi.1
      exact good i (by omega) (by omega) (by omega) (by omega) (by omega))
    omega
  have : v ≤ ((Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i)).card := by
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact good i hi.1 (by omega) (ne_of_prime_pow p i 3 hp Nat.prime_three hi.1 hp3)
      (ne_of_prime_pow p i 5 hp Nat.prime_five hi.1 hp5)
      (ne_of_prime_pow p i 7 hp (by decide) hi.1 hp7)
  omega

theorem integral (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      Nat.factorial (30 * n) * Nat.factorial n := by
  have f15 := Nat.factorial_ne_zero (15 * n)
  have f10 := Nat.factorial_ne_zero (10 * n)
  have f6 := Nat.factorial_ne_zero (6 * n)
  have f30 := Nat.factorial_ne_zero (30 * n)
  have f1 := Nat.factorial_ne_zero n
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6) (Nat.mul_ne_zero f30 f1)]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul (Nat.mul_ne_zero f15 f10) f6, padicValNat.mul f15 f10,
    padicValNat.mul f30 f1]
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * n) < Nat.log p (30 * n) + 1 := fun c hc =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right n hc))
  have hb1 : Nat.log p n < Nat.log p (30 * n) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial (hb 15 (by omega)), padicValNat_factorial (hb 10 (by omega)),
    padicValNat_factorial (hb 6 (by omega)), padicValNat_factorial (hb 30 (by omega)),
    padicValNat_factorial hb1]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => key n (p ^ i))

end T7

theorem seven_mul_a_dvd_two_mul_add_one (n : ℕ) :
    (2 * (n : ℤ) + 1) ∣ 7 * (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := T7.main n hn
    have hD := T7.integral n hn
    have h2 : (2 * n + 1) ∣ 7 * a n := by
      unfold a
      rw [← Nat.mul_div_assoc _ hD]
      rw [mul_comm] at h
      exact Nat.dvd_div_of_mul_dvd h
    have h3 : ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 1 := by norm_cast
    rw [← h3]
    exact_mod_cast Int.natCast_dvd_natCast.mpr h2

end OeisA211417

#print axioms OeisA211417.seven_mul_a_dvd_two_mul_add_one
