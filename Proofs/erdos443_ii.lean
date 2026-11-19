import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

namespace Erdos443

def A (m : ℕ) : Finset ℕ := (Finset.Icc 1 (m / 2)).image fun k => k * (m - k)

namespace T

lemma loc (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 1 ≤ K ∧ ∃ P0 : ℕ, ∀ p a : ℕ, 2 ≤ p →
    ((a:ℝ) + 1) ≤ (if p < P0 then K else 1) * ((p:ℝ)^a)^ε := by
  refine ⟨max 1 (1 / (ε * Real.log 2)), le_max_left _ _, ⌈(2:ℝ)^(1/ε)⌉₊, fun p a hp => ?_⟩
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < ε * Real.log 2 := mul_pos hε hl
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  split_ifs with h
  · have h1 : (2:ℝ)^((a:ℝ)*ε) ≤ ((p:ℝ)^a)^ε := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      exact Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by norm_num) hp' a) hε.le
    have h2 : 1 + ε * Real.log 2 * a ≤ (2:ℝ)^((a:ℝ)*ε) := by
      have e : Real.log 2 * (a * ε) = ε * Real.log 2 * a := by ring
      rw [Real.rpow_def_of_pos (by norm_num), e]
      linarith [Real.add_one_le_exp (ε * Real.log 2 * a)]
    have hK1 : (1:ℝ) ≤ max 1 (1 / (ε * Real.log 2)) := le_max_left _ _
    have hK2 : 1 / (ε * Real.log 2) ≤ max 1 (1 / (ε * Real.log 2)) := le_max_right _ _
    have hKc : 1 ≤ max 1 (1 / (ε * Real.log 2)) * (ε * Real.log 2) :=
      (div_le_iff₀ hc).mp hK2
    have h3 : (a:ℝ) + 1 ≤ max 1 (1 / (ε * Real.log 2)) * (1 + ε * Real.log 2 * a) := by
      have := mul_le_mul_of_nonneg_left hKc ha
      nlinarith
    calc (a:ℝ) + 1 ≤ max 1 (1 / (ε * Real.log 2)) * (1 + ε * Real.log 2 * a) := h3
      _ ≤ max 1 (1 / (ε * Real.log 2)) * ((p:ℝ)^a)^ε :=
        mul_le_mul_of_nonneg_left (h2.trans h1) (by linarith)
  · have h' : (⌈(2:ℝ)^(1/ε)⌉₊ : ℝ) ≤ p := by exact_mod_cast (not_lt.mp h)
    have hP : (2:ℝ) ≤ (p:ℝ)^ε :=
      calc (2:ℝ) = ((2:ℝ)^(1/ε))^ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p:ℝ)^ε := Real.rpow_le_rpow (by positivity) (le_trans (Nat.le_ceil _) h') hε.le
    have e1 : ((p:ℝ)^a)^ε = (p:ℝ)^((a:ℝ)*ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have e2 : ((p:ℝ)^ε)^a = (p:ℝ)^(ε*(a:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [one_mul, e1, mul_comm, ← e2]
    have h2a : a + 1 ≤ 2^a := Nat.lt_two_pow_self
    calc (a:ℝ) + 1 ≤ (2:ℝ)^a := by exact_mod_cast h2a
      _ ≤ ((p:ℝ)^ε)^a := pow_le_pow_left₀ (by norm_num) hP a

lemma tau_bound (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, N ≠ 0 → (N.divisors.card : ℝ) ≤ C * (N:ℝ)^ε := by
  obtain ⟨K, hK, P0, hloc⟩ := loc ε hε
  refine ⟨K^P0, by positivity, fun N hN => ?_⟩
  have hNprod : (N:ℝ) = ∏ p ∈ N.primeFactors, ((p:ℝ)^(N.factorization p)) := by
    have := Nat.prod_factorization_pow_eq_self hN
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact_mod_cast this.symm
  have hG : ∀ p : ℕ, 0 ≤ (if p < P0 then K else 1) := by
    intro p; split_ifs <;> linarith
  rw [Nat.card_divisors hN, hNprod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  push_cast
  calc ∏ p ∈ N.primeFactors, ((N.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ N.primeFactors, ((if p < P0 then K else 1) * ((p:ℝ)^(N.factorization p))^ε) :=
        Finset.prod_le_prod (fun _ _ => by positivity)
          (fun p hp => hloc p _ (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = (∏ p ∈ N.primeFactors, (if p < P0 then K else 1)) *
          ∏ p ∈ N.primeFactors, ((p:ℝ)^(N.factorization p))^ε := Finset.prod_mul_distrib
    _ ≤ K^P0 * ∏ p ∈ N.primeFactors, ((p:ℝ)^(N.factorization p))^ε := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hK
        calc (N.primeFactors.filter (· < P0)).card ≤ (Finset.range P0).card :=
              Finset.card_le_card (fun p hp => by
                rw [Finset.mem_filter] at hp; rw [Finset.mem_range]; exact hp.2)
          _ = P0 := Finset.card_range P0

lemma sq_form (m x : ℕ) (hx : x ∈ A m) : ∃ u, u^2 + 4*x = m^2 := by
  simp only [A, Finset.mem_image, Finset.mem_Icc] at hx
  obtain ⟨k, ⟨h1, h2⟩, rfl⟩ := hx
  have h2' : 2*k ≤ m := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h2'
  refine ⟨r, ?_⟩
  rw [show 2*k + r - k = k + r by omega]; ring

lemma sqrt_eq (m x u : ℕ) (h : u^2 + 4*x = m^2) : Nat.sqrt (m^2 - 4*x) = u := by
  rw [show m^2 - 4*x = u^2 by omega]; exact Nat.sqrt_eq' u

lemma injcore (m n u v u' v' x x' : ℤ) (h1 : u^2 + 4*x = m^2) (h2 : v^2 + 4*x = n^2)
    (h1' : u'^2 + 4*x' = m^2) (h2' : v'^2 + 4*x' = n^2) (hmn : m^2 ≠ n^2)
    (hd : u + v = u' + v') : x = x' := by
  have e1 : (u+v)*(u-v) = m^2-n^2 := by linear_combination h1 - h2
  have e2 : (u'+v')*(u'-v') = m^2-n^2 := by linear_combination h1' - h2'
  have hne : u + v ≠ 0 := by
    intro h; rw [h, zero_mul] at e1; exact hmn (by linarith)
  have e3 : u - v = u' - v' := by
    rw [hd] at e1 hne; exact mul_left_cancel₀ hne (e1.trans e2.symm)
  have hu : u = u' := by linarith
  subst hu; linarith

lemma card_le (m n : ℕ) (hm : n < m) : (A n ∩ A m).card ≤ (m^2 - n^2).divisors.card := by
  have hN : n^2 < m^2 := Nat.pow_lt_pow_left hm (by norm_num)
  have key : ∀ x ∈ A n ∩ A m, ∃ u v : ℕ, u^2 + 4*x = m^2 ∧ v^2 + 4*x = n^2 := by
    intro x hx; rw [Finset.mem_inter] at hx
    obtain ⟨v, hv⟩ := sq_form n x hx.1
    obtain ⟨u, hu⟩ := sq_form m x hx.2
    exact ⟨u, v, hu, hv⟩
  have hmn : (m:ℤ)^2 ≠ (n:ℤ)^2 := by
    have : (n:ℤ)^2 < (m:ℤ)^2 := by exact_mod_cast hN
    exact ne_of_gt this
  refine Finset.card_le_card_of_injOn (fun x => Nat.sqrt (m^2 - 4*x) + Nat.sqrt (n^2 - 4*x))
    ?_ ?_
  · intro x hx
    obtain ⟨u, v, hu, hv⟩ := key x hx
    simp only [sqrt_eq m x u hu, sqrt_eq n x v hv]
    rw [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, Nat.sub_ne_zero_of_lt hN⟩
    have hu' : (u:ℤ)^2 + 4*x = m^2 := by exact_mod_cast hu
    have hv' : (v:ℤ)^2 + 4*x = n^2 := by exact_mod_cast hv
    have : ((u+v : ℕ) : ℤ) ∣ ((m^2 - n^2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hN.le]
      exact ⟨(u:ℤ) - v, by linear_combination hv' - hu'⟩
    exact Int.natCast_dvd_natCast.mp this
  · intro x hx y hy hxy
    obtain ⟨u, v, hu, hv⟩ := key x hx
    obtain ⟨u', v', hu', hv'⟩ := key y hy
    have hd : u + v = u' + v' := by
      have := hxy
      simp only [sqrt_eq m x u hu, sqrt_eq n x v hv, sqrt_eq m y u' hu',
        sqrt_eq n y v' hv'] at this
      exact this
    have := injcore (m:ℤ) n u v u' v' x y (by exact_mod_cast hu) (by exact_mod_cast hv)
      (by exact_mod_cast hu') (by exact_mod_cast hv') hmn (by exact_mod_cast hd)
    exact_mod_cast this

end T

theorem erdos_443.parts.ii :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
      ((A n ∩ A m).card : ℝ) < ((m : ℝ) * n) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hτ⟩ := T.tau_bound (ε/2) (by linarith)
  refine ⟨⌈C^(1/ε)⌉₊, fun m n hn hm => ?_⟩
  have hN : n^2 < m^2 := Nat.pow_lt_pow_left hm (by norm_num)
  have hcard := T.card_le m n hm
  have hnC : C < (n:ℝ)^ε := by
    have h1 : C^(1/ε) < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 := Real.rpow_lt_rpow (by positivity) h1 hε
    rwa [← Real.rpow_mul hC.le, one_div_mul_cancel hε.ne', Real.rpow_one] at h2
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNle : (((m^2 - n^2 : ℕ) : ℝ))^(ε/2) ≤ (m:ℝ)^ε := by
    calc (((m^2 - n^2 : ℕ) : ℝ))^(ε/2) ≤ ((m:ℝ)^2)^(ε/2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          push_cast [Nat.cast_sub hN.le]
          nlinarith [sq_nonneg (n:ℝ)]
      _ = (m:ℝ)^ε := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
          congr 1; push_cast; ring
  have hmε : 0 < (m:ℝ)^ε := Real.rpow_pos_of_pos hm0 _
  calc ((A n ∩ A m).card : ℝ) ≤ ((m^2 - n^2).divisors.card : ℝ) := by exact_mod_cast hcard
    _ ≤ C * (((m^2 - n^2 : ℕ) : ℝ))^(ε/2) := hτ _ (Nat.sub_ne_zero_of_lt hN)
    _ ≤ C * (m:ℝ)^ε := mul_le_mul_of_nonneg_left hNle hC.le
    _ < (n:ℝ)^ε * (m:ℝ)^ε := mul_lt_mul_of_pos_right hnC hmε
    _ = ((m:ℝ) * n)^ε := by
        rw [Real.mul_rpow hm0.le (Nat.cast_nonneg n)]; ring

end Erdos443

#print axioms Erdos443.erdos_443.parts.ii
