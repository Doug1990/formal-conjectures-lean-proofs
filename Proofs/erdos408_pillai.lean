import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

open Filter

namespace Erdos408

noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}

namespace P

/-- Completely additive weight with `D 2 = 1` and `D p = D (p - 1)` for odd primes. -/
def D (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors.attach,
    n.factorization p * (if p.1 = 2 then 1 else D (p.1 - 1))
decreasing_by
  all_goals
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hle := Nat.le_of_mem_primeFactors p.2
    have := hp.two_le
    omega

def w (p : ℕ) : ℕ := if p = 2 then 1 else D (p - 1)

lemma D_eq (n : ℕ) : D n = n.factorization.sum (fun p k => k * w p) := by
  rw [D, Finsupp.sum, Nat.support_factorization]
  exact Finset.sum_attach n.primeFactors (fun p => n.factorization p * w p)

lemma D_one : D 1 = 0 := by
  rw [D_eq]; simp

lemma D_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : D (a * b) = D a + D b := by
  rw [D_eq, D_eq, D_eq, Nat.factorization_mul ha hb, Finsupp.sum_add_index']
  · intro i; simp
  · intro i b1 b2; exact add_mul _ _ _

lemma D_prime {p : ℕ} (hp : p.Prime) : D p = w p := by
  rw [D_eq, hp.factorization, Finsupp.sum_single_index] <;> simp

lemma D_pow {p : ℕ} (hp : p ≠ 0) : ∀ k, D (p ^ k) = k * D p
  | 0 => by simp [D_one]
  | k + 1 => by
    rw [pow_succ, D_mul (pow_ne_zero _ hp) hp, D_pow hp k]; ring

lemma D_prod (s : Finset ℕ) (g : ℕ → ℕ) (h : ∀ i ∈ s, g i ≠ 0) :
    D (∏ i ∈ s, g i) = ∑ i ∈ s, D (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [D_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      D_mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

lemma key (n : ℕ) (hn : n ≠ 0) :
    D n ≤ D (Nat.totient n) + (if 2 ∣ n then 1 else 0) := by
  have h1 : D (Nat.totient n) =
      ∑ p ∈ n.primeFactors, D (p ^ (n.factorization p - 1) * (p - 1)) := by
    rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization]
    apply D_prod
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    exact Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have h2 : D n = ∑ p ∈ n.primeFactors, n.factorization p * w p := by
    rw [D_eq, Finsupp.sum, Nat.support_factorization]
  have h3 : (if 2 ∣ n then 1 else 0) =
      ∑ p ∈ n.primeFactors, (if p = 2 then 1 else 0) := by
    rw [Finset.sum_ite_eq']
    simp [Nat.mem_primeFactors, hn, Nat.prime_two]
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : 1 ≤ n.factorization p :=
    hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  have h2p := hpp.two_le
  rw [D_mul (pow_ne_zero _ hpp.ne_zero) (by omega), D_pow hpp.ne_zero, D_prime hpp]
  unfold w
  generalize n.factorization p = k at hk ⊢
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  split_ifs with h
  · simp only [mul_one, Nat.add_sub_cancel]; omega
  · simp only [Nat.add_sub_cancel, add_mul, one_mul]; omega

lemma bound (n : ℕ) (hn : 1 ≤ n) : n ≤ 3 ^ D n ∧ (2 ∣ n → 3 * n ≤ 2 * 3 ^ D n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp [D_one]
    set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have h2p := hp.two_le
    obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; omega
      · exact h0
    have hmn : m < n := by
      rw [hm]; nlinarith
    have hDn : D n = D p + D m := by rw [hm]; exact D_mul (by omega) (by omega)
    obtain ⟨ihm, -⟩ := ih m hmn hm1
    by_cases hp2 : p = 2
    · have hDp : D p = 1 := by rw [D_prime hp, w, if_pos hp2]
      rw [hDn, hDp, pow_add]
      rw [hp2] at hm
      constructor
      · omega
      · intro; omega
    · have hDp : D p = D (p - 1) := by rw [D_prime hp, w, if_neg hp2]
      have hodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h' | h'
        · exact absurd h' hp2
        · exact h'
      have hp1 : p - 1 < n := by
        have := Nat.minFac_le (by omega : 0 < n); omega
      obtain ⟨-, ihp⟩ := ih (p - 1) hp1 (by omega)
      have hq := ihp (by omega)
      have hpX : p ≤ 3 ^ D (p - 1) := by omega
      rw [hDn, hDp, pow_add]
      constructor
      · rw [hm]; exact Nat.mul_le_mul hpX ihm
      · intro h2
        exfalso
        have := Nat.minFac_le_of_dvd (le_refl 2) h2
        omega

lemma iter_D : ∀ k n, n ≠ 0 → Nat.totient^[k] n = 1 →
    D n ≤ k ∧ (¬ 2 ∣ n → 2 ≤ n → D n + 1 ≤ k)
  | 0, n, _, h => by
    simp only [Function.iterate_zero, id_eq] at h
    subst h
    simp [D_one]
  | k + 1, n, hn, h => by
    rw [Function.iterate_succ_apply] at h
    have hφ : Nat.totient n ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
    obtain ⟨ih, -⟩ := iter_D k _ hφ h
    have hk := key n hn
    constructor
    · split_ifs at hk <;> omega
    · intro h2 _
      rw [if_neg h2] at hk
      omega

lemma half : ∀ m, Nat.totient (2 * m) ≤ m
  | m => by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp
    by_cases h : 2 ∣ m
    · obtain ⟨j, rfl⟩ := h
      rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two ⟨j, rfl⟩]
      have := half j
      omega
    · rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h),
        Nat.totient_two, one_mul]
      exact Nat.totient_le m

lemma E (n : ℕ) (hn : 1 ≤ n) : ∃ k, 1 ≤ k ∧ Nat.totient^[k] n = 1 ∧
    2 ^ (k - 1) ≤ n ∧ (2 ∣ n → 2 ^ k ≤ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
      · exact ⟨1, le_rfl, by simp, by simp, by omega⟩
      · exact ⟨1, le_rfl, by simp [Nat.totient_two], by simp, fun _ => by simp⟩
    have hmn : Nat.totient n < n := Nat.totient_lt n (by omega)
    have hm0 : 0 < Nat.totient n := Nat.totient_pos.2 (by omega)
    have hme : 2 ∣ Nat.totient n := even_iff_two_dvd.1 (Nat.totient_even (by omega))
    obtain ⟨k, hk1, hit, -, hpow⟩ := ih _ hmn hm0
    have hpow := hpow hme
    refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply]; exact hit
    · rw [Nat.add_sub_cancel]; omega
    · rintro ⟨j, rfl⟩
      have := half j
      rw [pow_succ]
      omega

end P

open P in
theorem erdos_408.variants.pillai (n : ℕ) (hn : 2 ≤ n) :
    ⌊(Real.log n - Real.log 2) / Real.log 3⌋₊ + 1 ≤ f n ∧
      f n ≤ ⌊Real.log n / Real.log 2⌋₊ + 1 := by
  obtain ⟨k, hk1, hit, hpow, -⟩ := E n (by omega)
  have hmem : f n ∈ {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1} := Nat.sInf_mem ⟨k, hk1, hit⟩
  have hle : f n ≤ k := Nat.sInf_le ⟨hk1, hit⟩
  obtain ⟨hf1, hfit⟩ := hmem
  have hlow : n ≤ 2 * 3 ^ (f n - 1) := by
    obtain ⟨hD, hD'⟩ := iter_D (f n) n (by omega) hfit
    obtain ⟨hb, hb'⟩ := bound n (by omega)
    obtain ⟨j, hj⟩ : ∃ j, f n = j + 1 := ⟨f n - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    rw [hj] at hD hD'
    by_cases h2 : 2 ∣ n
    · have h3 := hb' h2
      have h4 : 3 ^ D n ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) hD
      rw [pow_succ] at h4
      omega
    · have h3 := hD' h2 hn
      have h4 : 3 ^ D n ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · have : ⌊(Real.log n - Real.log 2) / Real.log 3⌋₊ ≤ f n - 1 := by
      apply Nat.floor_le_of_le
      rw [div_le_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
      have h5 : Real.log n ≤ Real.log (2 * 3 ^ (f n - 1)) :=
        Real.log_le_log hn0 (by exact_mod_cast hlow)
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num))] at h5
      linarith
    omega
  · have : k - 1 ≤ ⌊Real.log n / Real.log 2⌋₊ := by
      apply Nat.le_floor
      rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
      exact Real.log_le_log (pow_pos (by norm_num) _) (by exact_mod_cast hpow)
    omega

end Erdos408

#print axioms Erdos408.erdos_408.variants.pillai
