import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace OeisA211417

def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

namespace T5

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

/-- a layer q ∣ 5m+1 with q ∉ {2,3,4} contributes at least 1 -/
lemma key5 (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 5 * m + 1) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (h4 : q ≠ 4) :
    15 * m / q + 10 * m / q + 6 * m / q + 1 ≤ 30 * m / q + m / q := by
  obtain ⟨k, hk⟩ := hd
  rcases Nat.lt_or_ge q 6 with hlt | hge
  · interval_cases q <;> omega
  · have e2 := div_eq m q 2 15 (by omega) (by omega)
    have e3 := div_eq m q 3 10 (by omega) (by omega)
    have e5 := div_eq m q 5 6 (by omega) (by omega)
    have e30 := div_eq m q 30 1 (by omega) (by omega)
    rw [one_mul] at e30
    rw [e2, e3, e5, e30]
    rcases k with _ | k'
    · simp at hk
    · have hr : q * (k' + 1) = q * k' + q := by ring
      have hs : q * (6 * k' + 5) = 6 * (q * k') + 5 * q := by ring
      have e : 30 * m = q * (6 * k' + 5) + (q - 6) := by omega
      have hJ : 30 * m / q = 6 * k' + 5 := by
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

lemma sum_bound' (b v : ℕ) (L R : ℕ → ℕ) (h0 : ∀ i, L i ≤ R i)
    (hv : v ≤ ((Finset.Ico 1 b).filter (fun i => L i + 1 ≤ R i)).card) :
    v + ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i := by
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

theorem main (n : ℕ) (hn : 1 ≤ n) :
    (5 * n + 1) * (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      Nat.factorial (30 * n) * Nat.factorial n := by
  have hx : 5 * n + 1 ≠ 0 := by omega
  have f15 := Nat.factorial_ne_zero (15 * n)
  have f10 := Nat.factorial_ne_zero (10 * n)
  have f6 := Nat.factorial_ne_zero (6 * n)
  have f30 := Nat.factorial_ne_zero (30 * n)
  have f1 := Nat.factorial_ne_zero n
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6))
    (Nat.mul_ne_zero f30 f1)]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul hx (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6),
    padicValNat.mul (Nat.mul_ne_zero f15 f10) f6, padicValNat.mul f15 f10,
    padicValNat.mul f30 f1]
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * n) < Nat.log p (30 * n) + 1 := fun c hc =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right n hc))
  have hb1 : Nat.log p n < Nat.log p (30 * n) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial (hb 15 (by omega)), padicValNat_factorial (hb 10 (by omega)),
    padicValNat_factorial (hb 6 (by omega)), padicValNat_factorial (hb 30 (by omega)),
    padicValNat_factorial hb1]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hdv : p ^ padicValNat p (5 * n + 1) ∣ 5 * n + 1 := pow_padicValNat_dvd
  have hpv : p ^ padicValNat p (5 * n + 1) ≤ 5 * n + 1 := Nat.le_of_dvd (by omega) hdv
  have hL1 : p ^ Nat.log p (30 * n) ≤ 30 * n := Nat.pow_log_le_self p (by omega)
  have hL2 : 30 * n < p ^ (Nat.log p (30 * n) + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
  generalize padicValNat p (5 * n + 1) = v at hdv hpv ⊢
  generalize Nat.log p (30 * n) = L at hL1 hL2 ⊢
  have hlt : ∀ i, p ^ i ≤ 30 * n → i < L + 1 := fun i h => by
    by_contra hc
    have := Nat.pow_le_pow_right hp.pos (show L + 1 ≤ i by omega)
    omega
  have hvL : v ≤ L := by have := hlt v (by omega); omega
  refine sum_bound' (L + 1) v (fun i => 15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i)
    (fun i => 30 * n / p ^ i + n / p ^ i) (fun i => key n (p ^ i)) ?_
  have good : ∀ i, 1 ≤ i → i ≤ v → p ^ i ≠ 2 → p ^ i ≠ 3 → p ^ i ≠ 4 →
      i ∈ (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i) := by
    intro i hi1 hiv h2 h3 h4
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hi1, by omega⟩, ?_⟩
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact key5 n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) h2 h3 h4
  have topg : ∀ i, 1 ≤ i → i ≤ L → 30 * n < 6 * p ^ i →
      i ∈ (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
        6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i) := by
    intro i hi1 hiL h6
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hi1, by omega⟩, ?_⟩
    have hle : p ^ i ≤ 30 * n := (Nat.pow_le_pow_right hp.pos hiL).trans hL1
    exact top n (p ^ i) (pow_pos hp.pos i) hle h6
  have hcard : (Finset.Ico 1 (v + 1)).card = v := by rw [Nat.card_Ico]; omega
  by_cases hp2 : p = 2
  · subst hp2
    have hv2 : v + 2 ≤ L := by
      have e : 2 ^ (v + 2) = 2 ^ v * 2 * 2 := by rw [pow_succ, pow_succ]
      have := hlt (v + 2) (by omega)
      omega
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have e1 : 2 ^ (L' + 1 + 1) = 2 ^ L' * 2 * 2 := by rw [pow_succ, pow_succ]
    have e2 : 2 ^ (L' + 1) = 2 ^ L' * 2 := pow_succ _ _
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn
          (fun i => if i = 1 then L' + 1 else if i = 2 then L' else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi ⊢
      split_ifs with h1 h3
      · exact topg _ (by omega) le_rfl (by omega)
      · exact topg _ (by omega) (by omega) (by omega)
      · have h4 : 8 ≤ 2 ^ i :=
          calc 8 = 2 ^ 3 := rfl
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        exact good i hi.1 (by omega) (by omega) (by omega) (by omega)
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
      simp only at hij
      split_ifs at hij <;> omega
  by_cases hp3 : p = 3
  · subst hp3
    have hv1 : v + 1 ≤ L := by
      have e : 3 ^ (v + 1) = 3 ^ v * 3 := pow_succ _ _
      have := hlt (v + 1) (by omega)
      omega
    have e1 : 3 ^ (L + 1) = 3 ^ L * 3 := pow_succ _ _
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn
          (fun i => if i = 1 then L else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi ⊢
      split_ifs with h1
      · exact topg _ (by omega) le_rfl (by omega)
      · have h4 : 9 ≤ 3 ^ i :=
          calc 9 = 3 ^ 2 := rfl
            _ ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        exact good i hi.1 (by omega) (by omega) (by omega) (by omega)
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
      simp only at hij
      split_ifs at hij <;> omega
  calc v = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  have h2 : p ^ i ≠ 2 := by
    intro h
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [h] at hd
    have := Nat.le_of_dvd (by omega) hd
    have := hp.two_le
    omega
  have h3 : p ^ i ≠ 3 := by
    intro h
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [h] at hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
  have h4 : p ^ i ≠ 4 := by
    intro h
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [h] at hd
    have h' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
    have := Nat.le_of_dvd (by omega) h'
    have := hp.two_le
    omega
  exact good i hi.1 (by omega) h2 h3 h4

end T5

theorem a_dvd_five_mul_add_one (n : ℕ) :
    (5 * (n : ℤ) + 1) ∣ (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := T5.main n hn
    have h2 : (5 * n + 1) ∣ a n := by
      unfold a
      rw [mul_comm] at h
      exact Nat.dvd_div_of_mul_dvd h
    have h3 : ((5 * n + 1 : ℕ) : ℤ) = 5 * (n : ℤ) + 1 := by norm_cast
    rw [← h3]
    exact Int.natCast_dvd_natCast.mpr h2

end OeisA211417

#print axioms OeisA211417.a_dvd_five_mul_add_one
