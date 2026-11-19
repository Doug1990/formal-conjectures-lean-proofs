import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Statement restated from FormalConjectures/ErdosProblems/205.lean (Erdos205). -/

open Asymptotics Filter

open scoped ArithmeticFunction.Omega

namespace Erdos205

namespace MP

/-- Chebyshev-type lower bound via the central binomial coefficient. -/
lemma cheb (m : ℕ) (hm : 1 ≤ m) :
    4 ^ m ≤ (2 * m + 1) * (2 * m) ^ Nat.count Nat.Prime (2 * m + 1) := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  rw [← Nat.centralBinom_eq_two_mul_choose, ← Nat.prod_pow_factorization_centralBinom,
    Nat.count_eq_card_filter_range, ← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p _
  split_ifs with h
  · rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.pow_factorization_choose_le (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero]

noncomputable def q (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 1)

lemma q_prime (i : ℕ) : (q i).Prime := Nat.prime_nth_prime _

lemma q_strict : StrictMono q := fun a b h =>
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)

lemma q_gt_two (i : ℕ) : 2 < q i := by
  have := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_pos i)
  rwa [Nat.nth_prime_zero_eq_two] at this

lemma two_pow_ge (j : ℕ) (hj : 3 ≤ j) : 2 * j + 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

lemma count_big (j : ℕ) (hj : 3 ≤ j) :
    2 ^ j < Nat.count Nat.Prime (2 * (2 ^ j) ^ 2 + 1) := by
  by_contra hc
  have hc' := not_lt.1 hc
  have f1 : (2 ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hr1 : 1 ≤ (2 ^ j) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h := cheb ((2 ^ j) ^ 2) hr1
  have hA : 2 * (j + 1) ≤ 2 ^ j := by have := two_pow_ge j hj; omega
  have h8 : 8 ≤ 2 ^ j := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h2 : (2 * (2 ^ j) ^ 2 + 1) * (2 * (2 ^ j) ^ 2) ^ Nat.count Nat.Prime (2 * (2 ^ j) ^ 2 + 1)
      ≤ (4 * (2 ^ j) ^ 2) ^ (2 ^ j + 1) := by
    rw [pow_succ' (4 * (2 ^ j) ^ 2) (2 ^ j)]
    apply Nat.mul_le_mul (by omega)
    calc (2 * (2 ^ j) ^ 2) ^ Nat.count Nat.Prime (2 * (2 ^ j) ^ 2 + 1)
        ≤ (2 * (2 ^ j) ^ 2) ^ (2 ^ j) := Nat.pow_le_pow_right (by positivity) hc'
      _ ≤ (4 * (2 ^ j) ^ 2) ^ (2 ^ j) := Nat.pow_le_pow_left (by omega) _
  have key : (j + 1) * (2 ^ j + 1) < 2 ^ j * 2 ^ j := by
    have e1 : 2 * ((j + 1) * (2 ^ j + 1)) ≤ 2 ^ j * (2 ^ j + 1) := by
      calc 2 * ((j + 1) * (2 ^ j + 1)) = (2 * (j + 1)) * (2 ^ j + 1) := by ring
        _ ≤ 2 ^ j * (2 ^ j + 1) := Nat.mul_le_mul_right _ hA
    have e2 : 2 ^ j * (2 ^ j + 1) = 2 ^ j * 2 ^ j + 2 ^ j := by ring
    have e3 : 2 ^ j < 2 ^ j * 2 ^ j := by nlinarith
    omega
  have h3 : (4 * (2 ^ j) ^ 2) ^ (2 ^ j + 1) < 4 ^ ((2 ^ j) ^ 2) := by
    have e4 : (4 * (2 ^ j) ^ 2) ^ (2 ^ j + 1) = 4 ^ ((j + 1) * (2 ^ j + 1)) := by
      rw [f1, ← pow_succ', ← pow_mul]
    have e5 : (2 ^ j) ^ 2 = 2 ^ j * 2 ^ j := by ring
    rw [e4, e5]
    exact Nat.pow_lt_pow_right (by norm_num) key
  omega

lemma big {p r m : ℕ} (hp : p.Prime) (h : p ^ r ∣ m) (hm : m ≠ 0) : r ≤ Ω m := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := by rintro rfl; simp at hm
  have hqr : p ^ r ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [ArithmeticFunction.cardFactors_mul hqr hb,
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  omega

noncomputable def s (r i : ℕ) : ℕ := if i < r then q i ^ r else 2 ^ (r + 1)

lemma core (r Q : ℕ) (_hr : 1 ≤ r) (hq : ∀ i < r, q i ≤ Q) :
    ∃ n : ℕ, 2 ^ r < n ∧ n < 2 * ((Q ^ r) ^ r * 2 ^ (r + 1)) ∧
    ∀ k, 2 ^ k ≤ n → r ≤ Ω (n - 2 ^ k) := by
  classical
  have hs0 : ∀ i ∈ Finset.range (r + 1), s r i ≠ 0 := by
    intro i _
    unfold s
    split_ifs
    · exact pow_ne_zero _ (q_prime i).ne_zero
    · exact pow_ne_zero _ two_ne_zero
  have hco : Set.Pairwise (↑(Finset.range (r + 1)) : Set ℕ) (Function.onFun Nat.Coprime (s r)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    show Nat.Coprime (s r i) (s r j)
    unfold s
    split_ifs with h1 h2 h2
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (q_prime i) (q_prime j)).2
        (q_strict.injective.ne hij))
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (q_prime i) Nat.prime_two).2
        (by have := q_gt_two i; omega))
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (q_prime j)).2
        (by have := q_gt_two j; omega))
    · omega
  have hsr : s r r = 2 ^ (r + 1) := by unfold s; simp
  have hPle : ∏ i ∈ Finset.range (r + 1), s r i ≤ (Q ^ r) ^ r * 2 ^ (r + 1) := by
    rw [Finset.prod_range_succ, hsr]
    apply Nat.mul_le_mul_right
    calc ∏ i ∈ Finset.range r, s r i
        ≤ (Q ^ r) ^ (Finset.range r).card := by
          apply Finset.prod_le_pow_card
          intro i hi
          have hi' := Finset.mem_range.1 hi
          have : s r i = q i ^ r := by unfold s; simp [hi']
          rw [this]
          exact Nat.pow_le_pow_left (hq i hi') r
      _ = (Q ^ r) ^ r := by rw [Finset.card_range]
  have hPge : 2 ^ (r + 1) ≤ ∏ i ∈ Finset.range (r + 1), s r i := by
    rw [Finset.prod_range_succ, hsr]
    apply Nat.le_mul_of_pos_left
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 (fun i hi => hs0 i (by
      simp only [Finset.mem_range] at hi ⊢; omega)))
  have hdvdP : ∀ i ≤ r, s r i ∣ ∏ i ∈ Finset.range (r + 1), s r i := fun i hi =>
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
  obtain ⟨c, hclt, hcong⟩ : ∃ c, c < ∏ i ∈ Finset.range (r + 1), s r i ∧
      ∀ i ∈ Finset.range (r + 1), c ≡ 2 ^ i [MOD s r i] :=
    ⟨Nat.chineseRemainderOfFinset (fun i => 2 ^ i) (s r) (Finset.range (r + 1)) hs0 hco,
      Nat.chineseRemainderOfFinset_lt_prod _ _ hs0 hco,
      (Nat.chineseRemainderOfFinset (fun i => 2 ^ i) (s r) (Finset.range (r + 1)) hs0 hco).2⟩
  generalize ∏ i ∈ Finset.range (r + 1), s r i = P at hPle hPge hdvdP hclt
  have hmod : ∀ i ≤ r, c + P ≡ 2 ^ i [MOD s r i] := by
    intro i hi
    have h1 := hcong i (Finset.mem_range.2 (by omega))
    have := Nat.ModEq.add h1 ((Nat.modEq_zero_iff_dvd).2 (hdvdP i hi))
    simpa using this
  have hrr : 2 ^ r < 2 ^ (r + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨d, hd⟩ : ∃ d, c + P = 2 ^ r * (2 * d + 1) := by
    have h := hmod r le_rfl
    rw [hsr] at h
    have hle : 2 ^ r ≤ c + P := by omega
    obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hle).1 h.symm
    refine ⟨d, ?_⟩
    have e := Nat.sub_add_cancel hle
    rw [hd] at e
    rw [← e, pow_succ]
    ring
  refine ⟨c + P, by omega, by omega, ?_⟩
  intro k hk
  have hne : c + P - 2 ^ k ≠ 0 := by
    intro h0
    have heq : c + P = 2 ^ k := le_antisymm (Nat.sub_eq_zero_iff_le.1 h0) hk
    rcases Nat.lt_or_ge r k with hkr | hkr
    · have e1 : 2 ^ k = 2 ^ r * 2 ^ (k - r - 1) * 2 := by
        rw [mul_assoc, ← pow_succ, ← pow_add]; congr 1; omega
      rw [hd, e1, mul_assoc] at heq
      have := Nat.eq_of_mul_eq_mul_left (by positivity) heq
      omega
    · have : 2 ^ k ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hkr
      omega
  rcases Nat.lt_or_ge k r with hkr | hkr
  · have h := hmod k hkr.le
    have hsk : s r k = q k ^ r := by unfold s; simp [hkr]
    rw [hsk] at h
    have hdv := (Nat.modEq_iff_dvd' hk).1 h.symm
    exact big (q_prime k) hdv hne
  · have h1 : 2 ^ r ∣ c + P := ⟨2 * d + 1, hd⟩
    have h2 : 2 ^ r ∣ 2 ^ k := pow_dvd_pow 2 hkr
    exact big Nat.prime_two (Nat.dvd_sub h1 h2) hne

lemma main (j : ℕ) (hj : 3 ≤ j) : ∃ n : ℕ, 2 ^ (2 ^ j) < n ∧
    n < 2 ^ ((2 * j + 1) * 2 ^ j * 2 ^ j + 2 ^ j + 2) ∧
    ∀ k, 2 ^ k ≤ n → 2 ^ j ≤ Ω (n - 2 ^ k) := by
  have hcount := count_big j hj
  have hq : ∀ i < 2 ^ j, q i ≤ 2 ^ (2 * j + 1) := by
    intro i hi
    have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := 2 * (2 ^ j) ^ 2 + 1)
      (k := i + 1) (by omega)
    have e : 2 * (2 ^ j) ^ 2 = 2 ^ (2 * j + 1) := by ring
    unfold q
    omega
  obtain ⟨n, h1, h2, h3⟩ := core (2 ^ j) (2 ^ (2 * j + 1)) (Nat.one_le_two_pow) hq
  refine ⟨n, h1, ?_, h3⟩
  have e : 2 * (((2 ^ (2 * j + 1)) ^ 2 ^ j) ^ 2 ^ j * 2 ^ (2 ^ j + 1)) =
      2 ^ ((2 * j + 1) * 2 ^ j * 2 ^ j + 2 ^ j + 2) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    ring
  omega

lemma ratio (j n : ℕ) (hj : 3 ≤ j) (h1 : 2 ^ (2 ^ j) < n)
    (h2 : n < 2 ^ ((2 * j + 1) * 2 ^ j * 2 ^ j + 2 ^ j + 2)) :
    (1 / 4 : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (2 : ℝ) ^ j := by
  set E := (2 * j + 1) * 2 ^ j * 2 ^ j + 2 ^ j + 2 with hE
  have h8 : 8 ≤ 2 ^ j := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hEle : E ≤ (2 * j + 2) * (2 ^ j * 2 ^ j) := by
    have : 2 ^ j + 2 ≤ 2 ^ j * 2 ^ j := by nlinarith
    have e : (2 * j + 2) * (2 ^ j * 2 ^ j) = (2 * j + 1) * 2 ^ j * 2 ^ j + 2 ^ j * 2 ^ j := by ring
    omega
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hR : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hnpos : (0 : ℝ) < n := by exact_mod_cast ((Nat.zero_le _).trans_lt h1 : 0 < n)
  have hlow : (2 : ℝ) ^ j * Real.log 2 < Real.log n := by
    have : ((2 : ℝ) ^ (2 ^ j)) < n := by exact_mod_cast h1
    have h := Real.log_lt_log (by positivity) this
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hup : Real.log n ≤ (2 * j + 2) * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) := by
    have : (n : ℝ) < (2 : ℝ) ^ E := by exact_mod_cast h2
    have h := Real.log_lt_log hnpos this
    rw [Real.log_pow] at h
    have hEr : (E : ℝ) ≤ (2 * j + 2) * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) := by
      have := (Nat.cast_le (α := ℝ)).2 hEle
      push_cast at this
      exact this
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    have : (E : ℝ) * Real.log 2 ≤ E := mul_le_of_le_one_right hE0 (by linarith)
    linarith
  have hLL : (j : ℝ) / 4 ≤ Real.log (Real.log n) := by
    have hpos : 0 < (2 : ℝ) ^ j / 2 := by positivity
    have hm1 : (2 : ℝ) ^ j * 0.6931471803 ≤ (2 : ℝ) ^ j * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le hR.le
    have hle : (2 : ℝ) ^ j / 2 ≤ Real.log n := by linarith
    have h := Real.log_le_log hpos hle
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    have hm : ((j : ℝ) - 1) * (1 / 2) ≤ ((j : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have expand : ((j : ℝ) - 1) * Real.log 2 = j * Real.log 2 - Real.log 2 := by ring
    linarith
  have hLLpos : 0 < Real.log (Real.log n) := by linarith
  have hX : Real.log n / Real.log (Real.log n) ≤ 16 * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) := by
    rw [div_le_iff₀ hLLpos]
    have h1' : 16 * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) * ((j : ℝ) / 4) ≤
        16 * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) * Real.log (Real.log n) :=
      mul_le_mul_of_nonneg_left hLL (by positivity)
    have h2' : (2 * (j : ℝ) + 2) * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) ≤
        4 * j * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hs := Real.sqrt_le_sqrt hX
  rw [show 16 * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) = (4 * (2 : ℝ) ^ j) ^ 2 by ring,
    Real.sqrt_sq (by positivity)] at hs
  linarith

end MP

theorem erdos_205.variants.many_prime_factors : ∃ c > (0 : ℝ),
    {n : ℕ | ∀ k : ℕ, 2 ^ k < n →
      c * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (Ω (n - 2 ^ k) : ℝ)}.Infinite := by
  refine ⟨1 / 4, by norm_num, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨n, hn1, hn2, hn3⟩ := MP.main (B + 3) (by omega)
  have hmem : n ∈ {n : ℕ | ∀ k : ℕ, 2 ^ k < n →
      (1 / 4 : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (Ω (n - 2 ^ k) : ℝ)} := by
    intro k hk
    have h := MP.ratio (B + 3) n (by omega) hn1 hn2
    have h' : ((2 : ℝ) ^ (B + 3)) ≤ (Ω (n - 2 ^ k) : ℝ) := by exact_mod_cast hn3 k hk.le
    linarith
  have := hB hmem
  have h1 : B + 3 < 2 ^ (B + 3) := Nat.lt_two_pow_self
  have h2 : 2 ^ (B + 3) < 2 ^ 2 ^ (B + 3) := Nat.lt_two_pow_self
  omega

end Erdos205

#print axioms Erdos205.erdos_205.variants.many_prime_factors
