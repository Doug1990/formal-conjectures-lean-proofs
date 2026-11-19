import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Statements restated from FormalConjectures/ErdosProblems/205.lean (Erdos205). -/

open Asymptotics Filter

open scoped ArithmeticFunction.Omega

namespace Erdos205

def IsRepresentable (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k m : ℕ, n = 2 ^ k + m ∧ (Ω m : ℝ) < f m

namespace RP

lemma pr_ex (k : ℕ) : ∃ p, Nat.Prime p ∧ 2 ^ (k + 1) < p ∧ p ≤ 2 * 2 ^ (k + 1) :=
  Nat.exists_prime_lt_and_le_two_mul (2 ^ (k + 1)) (pow_ne_zero _ two_ne_zero)

noncomputable def pr (k : ℕ) : ℕ := Classical.choose (pr_ex k)

lemma pr_spec (k : ℕ) : Nat.Prime (pr k) ∧ 2 ^ (k + 1) < pr k ∧ pr k ≤ 2 * 2 ^ (k + 1) :=
  Classical.choose_spec (pr_ex k)

lemma pr_lt {k j : ℕ} (h : k < j) : pr k < pr j := by
  have h1 := (pr_spec k).2.2
  have h2 := (pr_spec j).2.1
  have : 2 * 2 ^ (k + 1) ≤ 2 ^ (j + 1) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma pr_inj {i j : ℕ} (h : i ≠ j) : pr i ≠ pr j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact (pr_lt h).ne
  · exact (pr_lt h).ne'

lemma pr_gt_two (k : ℕ) : 2 < pr k := by
  have h := (pr_spec k).2.1
  have : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma pr_le {k r : ℕ} (h : k < r) : pr k ≤ 2 ^ (r + 1) := by
  have h1 := (pr_spec k).2.2
  have : 2 * 2 ^ (k + 1) ≤ 2 ^ (r + 1) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

noncomputable def s (r i : ℕ) : ℕ := if i < r then pr i ^ r else 2 ^ (r + 1)

lemma s_le (r i : ℕ) (hr : 1 ≤ r) : s r i ≤ 2 ^ ((r + 1) * r) := by
  unfold s
  split_ifs with h
  · calc pr i ^ r ≤ (2 ^ (r + 1)) ^ r := Nat.pow_le_pow_left (pr_le h) r
      _ = 2 ^ ((r + 1) * r) := (pow_mul _ _ _).symm
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hr)

lemma big {q r m : ℕ} (hq : q.Prime) (h : q ^ r ∣ m) (hm : m ≠ 0) : 2 ^ r ≤ m ∧ r ≤ Ω m := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := by rintro rfl; simp at hm
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq.ne_zero
  refine ⟨?_, ?_⟩
  · calc 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq.two_le r
      _ ≤ q ^ r * b := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb)
  · rw [ArithmeticFunction.cardFactors_mul hqr hb,
      ArithmeticFunction.cardFactors_apply_prime_pow hq]
    omega

lemma core (r : ℕ) (hr : 1 ≤ r) : ∃ n : ℕ, 2 ^ r < n ∧ n < 2 ^ ((r + 1) * r * (r + 1) + 1) ∧
    ∀ k, 2 ^ k ≤ n → n - 2 ^ k ≠ 0 ∧ 2 ^ r ≤ n - 2 ^ k ∧ r ≤ Ω (n - 2 ^ k) := by
  classical
  have hs0 : ∀ i ∈ Finset.range (r + 1), s r i ≠ 0 := by
    intro i _
    unfold s
    split_ifs
    · exact pow_ne_zero _ (pr_spec i).1.ne_zero
    · exact pow_ne_zero _ two_ne_zero
  have hco : Set.Pairwise (↑(Finset.range (r + 1)) : Set ℕ) (Function.onFun Nat.Coprime (s r)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    show Nat.Coprime (s r i) (s r j)
    unfold s
    split_ifs with h1 h2 h2
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (pr_spec i).1 (pr_spec j).1).2 (pr_inj hij))
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (pr_spec i).1 Nat.prime_two).2
        (by have := pr_gt_two i; omega))
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (pr_spec j).1).2
        (by have := pr_gt_two j; omega))
    · omega
  have hPle : ∏ i ∈ Finset.range (r + 1), s r i ≤ 2 ^ ((r + 1) * r * (r + 1)) := by
    calc ∏ i ∈ Finset.range (r + 1), s r i
        ≤ (2 ^ ((r + 1) * r)) ^ (Finset.range (r + 1)).card :=
          Finset.prod_le_pow_card _ _ _ (fun i _ => s_le r i hr)
      _ = 2 ^ ((r + 1) * r * (r + 1)) := by rw [Finset.card_range, ← pow_mul]
  have hsr : s r r = 2 ^ (r + 1) := by unfold s; simp
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
  refine ⟨c + P, by omega, ?_, ?_⟩
  · have h2E : 2 ^ ((r + 1) * r * (r + 1) + 1) = 2 * 2 ^ ((r + 1) * r * (r + 1)) := by
      rw [pow_succ]; ring
    rw [h2E]; omega
  · intro k hk
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
    refine ⟨hne, ?_⟩
    rcases Nat.lt_or_ge k r with hkr | hkr
    · have h := hmod k hkr.le
      have hsk : s r k = pr k ^ r := by unfold s; simp [hkr]
      rw [hsk] at h
      have hdv := (Nat.modEq_iff_dvd' hk).1 h.symm
      exact big (pr_spec k).1 hdv hne
    · have h1 : 2 ^ r ∣ c + P := ⟨2 * d + 1, hd⟩
      have h2 : 2 ^ r ∣ 2 ^ k := pow_dvd_pow 2 hkr
      exact big Nat.prime_two (Nat.dvd_sub h1 h2) hne

lemma nat_bound (r : ℕ) (hr : 48 ≤ r) : 24 * ((r + 1) * r * (r + 1) + 1) ≤ r ^ 4 := by
  have h1 : 48 * r ^ 3 ≤ r ^ 4 := by
    calc 48 * r ^ 3 ≤ r * r ^ 3 := Nat.mul_le_mul_right _ hr
      _ = r ^ 4 := by ring
  have h2 : 48 * r ^ 2 ≤ r ^ 3 := by
    calc 48 * r ^ 2 ≤ r * r ^ 2 := Nat.mul_le_mul_right _ hr
      _ = r ^ 3 := by ring
  have h3 : 48 * r ≤ r ^ 2 := by
    calc 48 * r ≤ r * r := Nat.mul_le_mul_right _ hr
      _ = r ^ 2 := by ring
  have e : 24 * ((r + 1) * r * (r + 1) + 1) = 24 * r ^ 3 + 48 * r ^ 2 + 24 * r + 24 := by ring
  omega

lemma loglog_lt (r m : ℕ) (hr : 48 ≤ r) (hm2 : 2 ≤ m)
    (hmB : m < 2 ^ ((r + 1) * r * (r + 1) + 1)) : Real.log (Real.log m) < r := by
  have hNB := nat_bound r hr
  generalize (r + 1) * r * (r + 1) + 1 = E at hmB hNB
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogpos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have h1 : Real.log m < E := by
    have hlt : (m : ℝ) < 2 ^ E := by exact_mod_cast hmB
    have := Real.log_lt_log hm hlt
    rw [Real.log_pow] at this
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith
    have hE0 : (0 : ℝ) ≤ E := by positivity
    have := mul_le_mul_of_nonneg_left hl2.le hE0
    linarith
  have h3 : (r : ℝ) ^ 4 / 24 ≤ Real.exp r := by
    have := Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rwa [hf] at this
  have h4 : (E : ℝ) ≤ (r : ℝ) ^ 4 / 24 := by
    have : ((24 * E : ℕ) : ℝ) ≤ ((r ^ 4 : ℕ) : ℝ) := by exact_mod_cast hNB
    push_cast at this
    linarith
  exact (Real.log_lt_iff_lt_exp hlogpos).2 (by linarith)

lemma gen (f : ℕ → ℝ) (m0 : ℕ) (hf : ∀ m ≥ m0, f m ≤ Real.log (Real.log m)) :
    ¬ ∀ᶠ n : ℕ in atTop, IsRepresentable f n := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  obtain ⟨n, hn1, hn2, hn3⟩ := core (48 + N + m0) (by omega)
  have hrN : 48 + N + m0 < 2 ^ (48 + N + m0) := Nat.lt_two_pow_self
  obtain ⟨k, m, hnm, hlt⟩ := hN n (by omega)
  have hk : 2 ^ k ≤ n := by rw [hnm]; exact Nat.le_add_right _ _
  have hmn : m ≤ n := by rw [hnm]; exact Nat.le_add_left _ _
  have hmeq : n - 2 ^ k = m := by rw [hnm, Nat.add_sub_cancel_left]
  obtain ⟨_, h2r, hΩ⟩ := hn3 k hk
  rw [hmeq] at h2r hΩ
  have hll := loglog_lt (48 + N + m0) m (by omega) (by omega) (lt_of_le_of_lt hmn hn2)
  have h1 := hf m (by omega)
  have h2 : ((48 + N + m0 : ℕ) : ℝ) ≤ (Ω m : ℝ) := by exact_mod_cast hΩ
  linarith

end RP

theorem erdos_205.parts.i :
    ¬ ∀ᶠ n : ℕ in atTop, IsRepresentable (fun m => Real.log (Real.log m)) n :=
  RP.gen _ 0 (fun _ _ => le_rfl)

theorem erdos_205.parts.ii :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      IsRepresentable (fun m => ε * Real.log (Real.log m)) n := by
  intro h
  exact RP.gen (fun m => 1 * Real.log (Real.log m)) 0 (fun _ _ => by simp) (h 1 one_pos)

theorem erdos_205.parts.iii :
    ¬ ∃ f : ℕ → ℝ, f =o[atTop] (fun m : ℕ => Real.log (Real.log m)) ∧
      ∀ᶠ n : ℕ in atTop, IsRepresentable f n := by
  rintro ⟨f, hf, hev⟩
  obtain ⟨m1, hm1⟩ := Filter.eventually_atTop.1 (hf.bound (by norm_num : (0 : ℝ) < 1))
  refine RP.gen f (m1 + 3) (fun m hm => ?_) hev
  have h := hm1 m (by omega)
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
  have hlog1 : 1 ≤ Real.log m := by
    have := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three] : Real.exp 1 ≤ m)
    rwa [Real.log_exp] at this
  have hll : 0 ≤ Real.log (Real.log m) := Real.log_nonneg hlog1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hll, one_mul] at h
  exact (le_abs_self _).trans h

end Erdos205

#print axioms Erdos205.erdos_205.parts.i
#print axioms Erdos205.erdos_205.parts.ii
#print axioms Erdos205.erdos_205.parts.iii
