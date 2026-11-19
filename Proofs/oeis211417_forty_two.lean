import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace OeisA211417

def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

namespace T42

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

lemma keyA (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 2 * m + 1) (h3 : q ≠ 3) (h5 : q ≠ 5)
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

lemma keyB (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 3 * m + 1) (h2 : q ≠ 2) (h5 : q ≠ 5)
    (h8 : q ≠ 8) :
    15 * m / q + 10 * m / q + 6 * m / q + 1 ≤ 30 * m / q + m / q := by
  obtain ⟨k, hk⟩ := hd
  rcases Nat.lt_or_ge q 10 with hlt | hge
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
      have hs : q * (10 * k' + 9) = 10 * (q * k') + 9 * q := by ring
      have e : 30 * m = q * (10 * k' + 9) + (q - 10) := by omega
      have hJ : 30 * m / q = 10 * k' + 9 := by
        rw [e, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
      rw [hJ]
      omega

lemma keyC (m q : ℕ) (hq : 2 ≤ q) (hd : q ∣ 5 * m + 1) (h2 : q ≠ 2) (h3 : q ≠ 3)
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

/-- the good layers -/
def G (n p L : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (L + 1)).filter (fun i => 15 * n / p ^ i + 10 * n / p ^ i +
    6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i)

lemma memG (n p L i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ L)
    (h : 15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i + 1 ≤ 30 * n / p ^ i + n / p ^ i) :
    i ∈ G n p L := by
  unfold G
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨h1, by omega⟩, h⟩

lemma topG (n p L : ℕ) (hp : p.Prime) (hL1 : p ^ L ≤ 30 * n) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ L) (h6 : 30 * n < 6 * p ^ i) : i ∈ G n p L :=
  memG n p L i h1 h2
    (top n (p ^ i) (pow_pos hp.pos i) ((Nat.pow_le_pow_right hp.pos h2).trans hL1) h6)

lemma hlt_of (n p L : ℕ) (hp : p.Prime) (hL2 : 30 * n < p ^ (L + 1)) :
    ∀ i, p ^ i ≤ 30 * n → i ≤ L := fun i h => by
  by_contra hc
  have := Nat.pow_le_pow_right hp.pos (show L + 1 ≤ i by omega)
  omega

theorem frame (n X c : ℕ) (hn : 1 ≤ n) (hX : X ≠ 0) (hc : c ≠ 0)
    (H : ∀ p, p.Prime → ∀ L, p ^ L ≤ 30 * n → 30 * n < p ^ (L + 1) →
      padicValNat p X ≤ padicValNat p c + (G n p L).card) :
    X * (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      c * (Nat.factorial (30 * n) * Nat.factorial n) := by
  have f15 := Nat.factorial_ne_zero (15 * n)
  have f10 := Nat.factorial_ne_zero (10 * n)
  have f6 := Nat.factorial_ne_zero (6 * n)
  have f30 := Nat.factorial_ne_zero (30 * n)
  have f1 := Nat.factorial_ne_zero n
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.mul_ne_zero hX (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6))
    (Nat.mul_ne_zero hc (Nat.mul_ne_zero f30 f1))]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul hX (Nat.mul_ne_zero (Nat.mul_ne_zero f15 f10) f6),
    padicValNat.mul (Nat.mul_ne_zero f15 f10) f6, padicValNat.mul f15 f10,
    padicValNat.mul hc (Nat.mul_ne_zero f30 f1), padicValNat.mul f30 f1]
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * n) < Nat.log p (30 * n) + 1 := fun c hc =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right n hc))
  have hb1 : Nat.log p n < Nat.log p (30 * n) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial (hb 15 (by omega)), padicValNat_factorial (hb 10 (by omega)),
    padicValNat_factorial (hb 6 (by omega)), padicValNat_factorial (hb 30 (by omega)),
    padicValNat_factorial hb1]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hL1 : p ^ Nat.log p (30 * n) ≤ 30 * n := Nat.pow_log_le_self p (by omega)
  have hL2 : 30 * n < p ^ (Nat.log p (30 * n) + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
  refine sum_bound' _ _ _ (fun i => 15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i)
    (fun i => 30 * n / p ^ i + n / p ^ i) (fun i => key n (p ^ i)) ?_
  exact H p hp _ hL1 hL2

lemma cardA (n p L v : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hL1 : p ^ L ≤ 30 * n)
    (hL2 : 30 * n < p ^ (L + 1)) (hdv : p ^ v ∣ 2 * n + 1) :
    v ≤ (if p = 7 then 1 else 0) + (G n p L).card := by
  have hpv : p ^ v ≤ 2 * n + 1 := Nat.le_of_dvd (by omega) hdv
  have hlt := hlt_of n p L hp hL2
  have hvL : v ≤ L := hlt v (by omega)
  have good : ∀ i, 1 ≤ i → i ≤ v → p ^ i ≠ 3 → p ^ i ≠ 5 → p ^ i ≠ 7 → i ∈ G n p L := by
    intro i hi1 hiv h3 h5 h7
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact memG n p L i hi1 (by omega)
      (keyA n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) h3 h5 h7)
  have topg := topG n p L hp hL1
  have hcard : (Finset.Ico 1 (v + 1)).card = v := by rw [Nat.card_Ico]; omega
  by_cases hp7 : p = 7
  · rw [if_pos hp7]
    subst hp7
    have hcard2 : (Finset.Ico 2 (v + 1)).card + 1 ≥ v := by rw [Nat.card_Ico]; omega
    have : (Finset.Ico 2 (v + 1)).card ≤ (G n 7 L).card := Finset.card_le_card (by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h4 : 7 ^ 2 ≤ 7 ^ i := Nat.pow_le_pow_right (by omega) hi.1
      exact good i (by omega) (by omega) (by omega) (by omega) (by omega))
    omega
  rw [if_neg hp7, zero_add]
  have small : ∀ r, r = 3 ∨ r = 5 → p = r → v ≤ (G n p L).card := by
    intro r hr hpr
    subst hpr
    have hv1 : v + 1 ≤ L := by
      have e : p ^ (v + 1) = p ^ v * p := pow_succ _ _
      have : p ^ v * p ≤ 30 * n := by
        rcases hr with rfl | rfl <;> omega
      exact hlt (v + 1) (by omega)
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
  · exact small 3 (Or.inl rfl) hp3
  by_cases hp5 : p = 5
  · exact small 5 (Or.inr rfl) hp5
  calc v = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact good i hi.1 (by omega) (ne_of_prime_pow p i 3 hp Nat.prime_three hi.1 hp3)
    (ne_of_prime_pow p i 5 hp Nat.prime_five hi.1 hp5)
    (ne_of_prime_pow p i 7 hp (by decide) hi.1 hp7)

lemma cardB (n p L v : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hL1 : p ^ L ≤ 30 * n)
    (hL2 : 30 * n < p ^ (L + 1)) (hdv : p ^ v ∣ 3 * n + 1) :
    v ≤ (G n p L).card := by
  have hpv : p ^ v ≤ 3 * n + 1 := Nat.le_of_dvd (by omega) hdv
  have hlt := hlt_of n p L hp hL2
  have hvL : v ≤ L := hlt v (by omega)
  have good : ∀ i, 1 ≤ i → i ≤ v → p ^ i ≠ 2 → p ^ i ≠ 5 → p ^ i ≠ 8 → i ∈ G n p L := by
    intro i hi1 hiv h2 h5 h8
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact memG n p L i hi1 (by omega)
      (keyB n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) h2 h5 h8)
  have topg := topG n p L hp hL1
  have hcard : (Finset.Ico 1 (v + 1)).card = v := by rw [Nat.card_Ico]; omega
  by_cases hp2 : p = 2
  · subst hp2
    have hv2 : v + 2 ≤ L := by
      have e : 2 ^ (v + 2) = 2 ^ v * 2 * 2 := by rw [pow_succ, pow_succ]
      exact hlt (v + 2) (by omega)
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have e1 : 2 ^ (L' + 1 + 1) = 2 ^ L' * 2 * 2 := by rw [pow_succ, pow_succ]
    have e2 : 2 ^ (L' + 1) = 2 ^ L' * 2 := pow_succ _ _
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn
          (fun i => if i = 1 then L' + 1 else if i = 3 then L' else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi ⊢
      split_ifs with h1 h3
      · exact topg _ (by omega) le_rfl (by omega)
      · exact topg _ (by omega) (by omega) (by omega)
      · have h4 : 2 ^ i = 4 ∨ 16 ≤ 2 ^ i := by
          rcases (show i = 2 ∨ 4 ≤ i by omega) with rfl | h
          · left; rfl
          · right
            calc 16 = 2 ^ 4 := rfl
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) h
        exact good i hi.1 (by omega) (by omega) (by omega) (by omega)
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
      simp only at hij
      split_ifs at hij <;> omega
  by_cases hp5 : p = 5
  · subst hp5
    have hv1 : v + 1 ≤ L := by
      have e : 5 ^ (v + 1) = 5 ^ v * 5 := pow_succ _ _
      exact hlt (v + 1) (by omega)
    have e1 : 5 ^ (L + 1) = 5 ^ L * 5 := pow_succ _ _
    calc v = _ := hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn
          (fun i => if i = 1 then L else i) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi ⊢
      split_ifs with h1
      · exact topg _ (by omega) le_rfl (by omega)
      · have h4 : 25 ≤ 5 ^ i :=
          calc 25 = 5 ^ 2 := rfl
            _ ≤ 5 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        exact good i hi.1 (by omega) (by omega) (by omega) (by omega)
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
      simp only at hij
      split_ifs at hij <;> omega
  calc v = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  have h8 : p ^ i ≠ 8 := by
    intro h
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [h] at hd
    have h' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  exact good i hi.1 (by omega) (ne_of_prime_pow p i 2 hp Nat.prime_two hi.1 hp2)
    (ne_of_prime_pow p i 5 hp Nat.prime_five hi.1 hp5) h8

lemma cardC (n p L v : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hL1 : p ^ L ≤ 30 * n)
    (hL2 : 30 * n < p ^ (L + 1)) (hdv : p ^ v ∣ 5 * n + 1) :
    v ≤ (G n p L).card := by
  have hpv : p ^ v ≤ 5 * n + 1 := Nat.le_of_dvd (by omega) hdv
  have hlt := hlt_of n p L hp hL2
  have hvL : v ≤ L := hlt v (by omega)
  have good : ∀ i, 1 ≤ i → i ≤ v → p ^ i ≠ 2 → p ^ i ≠ 3 → p ^ i ≠ 4 → i ∈ G n p L := by
    intro i hi1 hiv h2 h3 h4
    have hq : 2 ≤ p ^ i := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact memG n p L i hi1 (by omega)
      (keyC n (p ^ i) hq ((pow_dvd_pow p hiv).trans hdv) h2 h3 h4)
  have topg := topG n p L hp hL1
  have hcard : (Finset.Ico 1 (v + 1)).card = v := by rw [Nat.card_Ico]; omega
  by_cases hp2 : p = 2
  · subst hp2
    have hv2 : v + 2 ≤ L := by
      have e : 2 ^ (v + 2) = 2 ^ v * 2 * 2 := by rw [pow_succ, pow_succ]
      exact hlt (v + 2) (by omega)
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
      exact hlt (v + 1) (by omega)
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
  have h4 : p ^ i ≠ 4 := by
    intro h
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [h] at hd
    have h' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  exact good i hi.1 (by omega) (ne_of_prime_pow p i 2 hp Nat.prime_two hi.1 hp2)
    (ne_of_prime_pow p i 3 hp Nat.prime_three hi.1 hp3) h4

lemma dv1 (p v X : ℕ) (hv : 1 ≤ v) (h : p ^ v ∣ X) : p ∣ X :=
  (dvd_pow_self p (by omega)).trans h

lemma dv2 (p v X : ℕ) (hv : 2 ≤ v) (h : p ^ v ∣ X) : p ^ 2 ∣ X :=
  (pow_dvd_pow p hv).trans h

/-- if d divides x and y with a·x = b·y + r, then d divides r -/
lemma dvd_comb (d x y a b r : ℕ) (hx : d ∣ x) (hy : d ∣ y) (e : a * x = b * y + r) : d ∣ r := by
  have h := dvd_mul_of_dvd_right hx a
  rw [e] at h
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hy b)).mp h

theorem main (n : ℕ) (hn : 1 ≤ n) :
    ((2 * n + 1) * (3 * n + 1) * (5 * n + 1)) *
      (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
      42 * (Nat.factorial (30 * n) * Nat.factorial n) := by
  refine frame n _ 42 hn (by positivity) (by omega) ?_
  intro p hp L hL1 hL2
  have := Fact.mk hp
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.mul (by omega) (by omega)]
  have hdA : p ^ padicValNat p (2 * n + 1) ∣ 2 * n + 1 := pow_padicValNat_dvd
  have hdB : p ^ padicValNat p (3 * n + 1) ∣ 3 * n + 1 := pow_padicValNat_dvd
  have hdC : p ^ padicValNat p (5 * n + 1) ∣ 5 * n + 1 := pow_padicValNat_dvd
  have hA := cardA n p L _ hp hn hL1 hL2 hdA
  have hB := cardB n p L _ hp hn hL1 hL2 hdB
  have hC := cardC n p L _ hp hn hL1 hL2 hdC
  have h42 : p ∣ 42 → 1 ≤ padicValNat p 42 := one_le_padicValNat_of_dvd (by omega)
  generalize padicValNat p 42 = c at h42 ⊢
  generalize padicValNat p (2 * n + 1) = vA at hdA hA ⊢
  generalize padicValNat p (3 * n + 1) = vB at hdB hB ⊢
  generalize padicValNat p (5 * n + 1) = vC at hdC hC ⊢
  generalize (G n p L).card = K at hA hB hC ⊢
  have hAB : vA = 0 ∨ vB = 0 := by
    by_contra h
    have h1 := dvd_comb p _ _ 3 2 1 (dv1 p vA _ (by omega) hdA) (dv1 p vB _ (by omega) hdB)
      (by ring)
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hAC : vA = 0 ∨ vC = 0 ∨ p = 3 := by
    by_contra h
    have h1 := dvd_comb p _ _ 5 2 3 (dv1 p vA _ (by omega) hdA) (dv1 p vC _ (by omega) hdC)
      (by ring)
    exact h (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)))
  have hBC : vB = 0 ∨ vC = 0 ∨ p = 2 := by
    by_contra h
    have h1 := dvd_comb p _ _ 5 3 2 (dv1 p vB _ (by omega) hdB) (dv1 p vC _ (by omega) hdC)
      (by ring)
    exact h (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)))
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_neg (by omega)] at hA
    have hc := h42 (by decide)
    have hvA : vA = 0 := by
      by_contra h
      have := dv1 2 vA _ (by omega) hdA
      omega
    have hm : vB ≤ 1 ∨ vC ≤ 1 := by
      by_contra h
      have h1 := dvd_comb (2 ^ 2) _ _ 5 3 2 (dv2 2 vB _ (by omega) hdB)
        (dv2 2 vC _ (by omega) hdC) (by ring)
      have := Nat.le_of_dvd (by omega) h1
      norm_num at this
    omega
  by_cases hp3 : p = 3
  · subst hp3
    rw [if_neg (by omega)] at hA
    have hc := h42 (by decide)
    have hvB : vB = 0 := by
      by_contra h
      have := dv1 3 vB _ (by omega) hdB
      omega
    have hm : vA ≤ 1 ∨ vC ≤ 1 := by
      by_contra h
      have h1 := dvd_comb (3 ^ 2) _ _ 5 2 3 (dv2 3 vA _ (by omega) hdA)
        (dv2 3 vC _ (by omega) hdC) (by ring)
      have := Nat.le_of_dvd (by omega) h1
      norm_num at this
    omega
  by_cases hp7 : p = 7
  · rw [if_pos hp7] at hA
    have hc := h42 (by rw [hp7]; decide)
    omega
  · rw [if_neg hp7] at hA
    omega

end T42

theorem forty_two_mul_a_dvd_product (n : ℕ) :
    ((2 * (n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (5 * (n : ℤ) + 1)) ∣
      42 * (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := T42.main n hn
    have hD : (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) ∣
        Nat.factorial (30 * n) * Nat.factorial n := by
      have := T42.frame n 1 1 hn (by omega) (by omega) (fun p _ L _ _ => by simp)
      simpa using this
    have h2 : ((2 * n + 1) * (3 * n + 1) * (5 * n + 1)) ∣ 42 * a n := by
      unfold a
      rw [← Nat.mul_div_assoc _ hD]
      rw [mul_comm] at h
      exact Nat.dvd_div_of_mul_dvd h
    have h3 : (((2 * n + 1) * (3 * n + 1) * (5 * n + 1) : ℕ) : ℤ) =
        (2 * (n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (5 * (n : ℤ) + 1) := by push_cast; ring
    rw [← h3]
    exact_mod_cast Int.natCast_dvd_natCast.mpr h2

end OeisA211417

#print axioms OeisA211417.forty_two_mul_a_dvd_product
