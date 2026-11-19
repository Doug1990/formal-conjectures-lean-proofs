import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

namespace OeisA129365

namespace C1

open Finset

/-- `exp Λ(d)` as a natural number. -/
noncomputable def f (d : ℕ) : ℕ := if IsPrimePow d then d.minFac else 1

lemma f_pos (d : ℕ) : 0 < f d := by
  unfold f
  split_ifs
  · exact Nat.minFac_pos d
  · exact Nat.one_pos

lemma log_f (d : ℕ) : Real.log (f d : ℝ) = ArithmeticFunction.vonMangoldt d := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  unfold f
  split_ifs
  · rfl
  · simp

lemma prod_divisors (i : ℕ) (hi : 0 < i) : ∏ d ∈ i.divisors, f d = i := by
  have hpos : (0 : ℝ) < ((∏ d ∈ i.divisors, f d : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun d _ => f_pos d)
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have key : Real.log ((∏ d ∈ i.divisors, f d : ℕ) : ℝ) = Real.log (i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun d _ => by exact_mod_cast (f_pos d).ne')]
    simp only [log_f]
    exact ArithmeticFunction.vonMangoldt_sum
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hi') key

/-- indicator -/
def ind (d x : ℕ) : ℕ := if d ∣ x then 1 else 0

lemma prod_Icc (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∏ d ∈ Icc 1 n, f d ^ ind d i = i := by
  have h1 : ∏ d ∈ Icc 1 n, f d ^ ind d i = ∏ d ∈ Icc 1 n, (if d ∣ i then f d else 1) := by
    apply Finset.prod_congr rfl
    intro d _
    unfold ind
    split_ifs <;> simp
  rw [h1, ← Finset.prod_filter]
  have h2 : (Icc 1 n).filter (fun d => d ∣ i) = i.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hin⟩, h⟩
  rw [h2, prod_divisors i (by omega)]

lemma prod_swap {ι : Type*} (s : Finset ι) (T : Finset ℕ) (g : ι → ℕ → ℕ) :
    ∏ x ∈ s, ∏ d ∈ T, f d ^ g x d = ∏ d ∈ T, f d ^ (∑ x ∈ s, g x d) := by
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro d _
  exact Finset.prod_pow_eq_pow_sum s (fun x => g x d) (f d)

lemma cnt (m d : ℕ) : ∑ i ∈ Icc 1 m, ind d i = m / d := by
  unfold ind
  rw [Finset.sum_boole, Nat.cast_id,
    show Icc 1 m = Ioc 0 m from Finset.Icc_add_one_left_eq_Ioc 0 m]
  exact Nat.Ioc_filter_dvd_card_eq_div m d

lemma ind_gcd (d j k : ℕ) : ind d (Nat.gcd j k) = ind d j * ind d k := by
  unfold ind
  by_cases hj : d ∣ j <;> by_cases hk : d ∣ k <;> simp [Nat.dvd_gcd_iff, hj, hk]

lemma num_eq (n : ℕ) :
    ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k) =
      ∏ d ∈ Icc 1 n, f d ^ ((n / d) * (n / d)) := by
  have h1 : ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k) =
      ∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, ∏ d ∈ Icc 1 n, f d ^ ind d (Nat.gcd j k) := by
    apply Finset.prod_congr rfl
    intro j hj
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hj hk
    rw [prod_Icc n _ (Nat.gcd_pos_of_pos_left _ (by omega))
      ((Nat.gcd_le_left _ (by omega)).trans hj.2)]
  rw [h1]
  simp only [prod_swap]
  apply Finset.prod_congr rfl
  intro d _
  congr 1
  simp only [ind_gcd]
  rw [← Finset.sum_mul_sum, cnt]

lemma fact_eq (n m : ℕ) (hm : m ≤ n) :
    m.factorial = ∏ d ∈ Icc 1 n, f d ^ (m / d) := by
  rw [← Finset.prod_Ico_id_eq_factorial, Finset.Ico_add_one_right_eq_Icc]
  have h1 : ∏ x ∈ Icc 1 m, x = ∏ i ∈ Icc 1 m, ∏ d ∈ Icc 1 n, f d ^ ind d i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [prod_Icc n i hi.1 (hi.2.trans hm)]
  rw [h1, prod_swap]
  apply Finset.prod_congr rfl
  intro d _
  rw [cnt]

lemma den_eq (n : ℕ) :
    ((Icc 1 n).prod fun k => (n / k).factorial ^ k) =
      ∏ d ∈ Icc 1 n, f d ^ (∑ k ∈ Icc 1 n, k * (n / k / d)) := by
  have h1 : ((Icc 1 n).prod fun k => (n / k).factorial ^ k) =
      ∏ k ∈ Icc 1 n, ∏ d ∈ Icc 1 n, f d ^ (k * (n / k / d)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [fact_eq n (n / k) (Nat.div_le_self n k), ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro d _
    rw [← pow_mul, mul_comm]
  rw [h1, prod_swap]

lemma sum_le (n M : ℕ) (hM : M ≤ n) : ∑ k ∈ Icc 1 n, k * (M / k) ≤ M * M := by
  have hsub : Icc 1 M ⊆ Icc 1 n := Finset.Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub]
  · calc ∑ k ∈ Icc 1 M, k * (M / k) ≤ ∑ k ∈ Icc 1 M, M := by
          apply Finset.sum_le_sum
          intro k _
          calc k * (M / k) = M / k * k := mul_comm _ _
            _ ≤ M := Nat.div_mul_le_self M k
      _ = M * M := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
          simp
  · intro k hk hk'
    rw [Finset.mem_Icc] at hk hk'
    have : M / k = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, mul_zero]

end C1

theorem conjecture1 (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
  rw [C1.num_eq, C1.den_eq]
  apply Finset.prod_dvd_prod_of_dvd
  intro d _
  apply pow_dvd_pow
  have h : ∀ k, n / k / d = n / d / k := by
    intro k
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  simp only [h]
  exact C1.sum_le n (n / d) (Nat.div_le_self n d)

end OeisA129365

#print axioms OeisA129365.conjecture1
