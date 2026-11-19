import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Statement restated from FormalConjectures/ErdosProblems/888.lean (Erdos888). -/

open Filter Asymptotics

namespace Erdos888

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop := ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

namespace PR

/-- Chebyshev-type lower bound via the central binomial coefficient (copied from erdos205_many). -/
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

lemma dvd_of_sq {q x : ℕ} (hq : q.Prime) (h : IsSquare (q * x)) : q ∣ x := by
  obtain ⟨r, hr⟩ := h
  have h1 : q ∣ r * r := hr ▸ dvd_mul_right q x
  have h2 : q ∣ r := ((Nat.Prime.dvd_mul hq).1 h1).elim id id
  obtain ⟨s, rfl⟩ := h2
  have h3 : q * x = q * (q * s * s) := by rw [hr]; ring
  have h4 := Nat.eq_of_mul_eq_mul_left hq.pos h3
  exact ⟨s * s, by rw [h4]; ring⟩

lemma prime_dvd3 {q x y z : ℕ} (hq : q.Prime) (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h : q ∣ x * y * z) : q = x ∨ q = y ∨ q = z := by
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hx).1 h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hy).1 h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq hz).1 h))

lemma cond (n : ℕ) : RequiredCondition ((Finset.range (n + 1)).filter Nat.Prime) n := by
  constructor
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have := hx.2.pos
    simp only [Finset.mem_Ioc]
    omega
  · intro a ha b hb c hc d hd hab hbc hcd hsq
    simp only [Finset.mem_filter] at ha hb hc hd
    have h1 : IsSquare (a * (b * c * d)) := by
      rwa [show a * (b * c * d) = a * b * c * d by ring]
    have h2 : IsSquare (d * (a * b * c)) := by
      rwa [show d * (a * b * c) = a * b * c * d by ring]
    have e1 := prime_dvd3 ha.2 hb.2 hc.2 hd.2 (dvd_of_sq ha.2 h1)
    have e2 := prime_dvd3 hd.2 ha.2 hb.2 hc.2 (dvd_of_sq hd.2 h2)
    have hab' : a = b := by omega
    have hcd' : d = c := by omega
    rw [hab', hcd']

lemma pi_lower (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ≤ 6 * (Nat.count Nat.Prime (n + 1) : ℝ) := by
  obtain ⟨m, hm⟩ : ∃ m, m = (n - 1) / 2 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m + 1 ≤ n := by omega
  have h2m' : 2 * m ≤ n := by omega
  have h4m : n ≤ 4 * m := by omega
  have hc := cheb m hm1
  obtain ⟨k, hkdef⟩ : ∃ k, k = Nat.count Nat.Prime (2 * m + 1) := ⟨_, rfl⟩
  rw [← hkdef] at hc
  have hk : k ≤ Nat.count Nat.Prime (n + 1) := hkdef ▸ Nat.count_monotone _ (by omega)
  have h3 : Nat.count Nat.Prime 3 = 1 := by
    simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  have hk1 : 1 ≤ k := by
    have := Nat.count_monotone Nat.Prime (show 3 ≤ 2 * m + 1 by omega)
    omega
  have hcR : (4 : ℝ) ^ m ≤ (2 * m + 1) * (2 * m) ^ k := by exact_mod_cast hc
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have hlog := Real.log_le_log hpos hcR
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hn1 : Real.log (2 * m + 1) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast h2m)
  have hn2 : Real.log (2 * m) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast h2m')
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4] at hlog
  have hl2 := Real.log_two_gt_d9
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkn : (k : ℝ) ≤ (Nat.count Nat.Prime (n + 1) : ℝ) := by exact_mod_cast hk
  have hmn : (n : ℝ) ≤ 4 * m := by exact_mod_cast h4m
  have e1 : (k : ℝ) * Real.log (2 * m) ≤ k * Real.log n :=
    mul_le_mul_of_nonneg_left hn2 (by positivity)
  have e2 : Real.log n ≤ k * Real.log n := le_mul_of_one_le_left hlogn.le hkR
  have e3 : (k : ℝ) * Real.log n ≤ (Nat.count Nat.Prime (n + 1) : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right hkn hlogn.le
  have e5 : (m : ℝ) * (2 * 0.6931471803) ≤ m * (2 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [div_le_iff₀ hlogn]
  linarith

end PR

open scoped Classical in
theorem erdos_888.variants.primes :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ ↦ (n : ℝ) / Real.log n)
      (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have h1 := PR.pi_lower n hn
  have h2 : Nat.count Nat.Prime (n + 1) ≤ Nat.findGreatest (p n) n := by
    apply Nat.le_findGreatest
    · rw [Nat.count_eq_card_filter_range]
      calc _ ≤ (Finset.Ioc 0 n).card := Finset.card_le_card (PR.cond n).1
        _ = n := by simp
    · exact ⟨_, PR.cond n, (Nat.count_eq_card_filter_range _ _).symm⟩
  have hpos : 0 ≤ (n : ℝ) / Real.log n :=
    div_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by positivity)]
  calc _ ≤ 6 * (Nat.count Nat.Prime (n + 1) : ℝ) := h1
    _ ≤ 6 * (Nat.findGreatest (p n) n : ℝ) := by gcongr

end Erdos888

#print axioms Erdos888.erdos_888.variants.primes
