import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Int

namespace OeisA129365

def a (n : ℕ) : ℚ :=
  let num : ℚ := (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k
  let den : ℚ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k
  num / den

def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (n % k)

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

lemma sum_restrict (n M : ℕ) (hM : M ≤ n) :
    ∑ k ∈ Icc 1 n, k * (M / k) = ∑ k ∈ Icc 1 M, k * (M / k) := by
  have hsub : Icc 1 M ⊆ Icc 1 n := Finset.Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub]
  intro k hk hk'
  rw [Finset.mem_Icc] at hk hk'
  have : M / k = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, mul_zero]

end C1

namespace C2

open Finset C1

noncomputable def A (n : ℕ) : ℕ := ∏ d ∈ Icc 1 n, f d ^ b (n / d)

lemma A_ne_zero (n : ℕ) : A n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun d _ => pow_ne_zero _ (f_pos d).ne')

lemma b_add (n M : ℕ) (hM : M ≤ n) : b M + ∑ k ∈ Icc 1 n, k * (M / k) = M * M := by
  rw [sum_restrict n M hM, b, ← Finset.sum_add_distrib]
  have : ∀ k ∈ Icc 1 M, M % k + k * (M / k) = M := fun k _ => Nat.mod_add_div M k
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  simp

lemma a_eq (n : ℕ) : a n = (A n : ℚ) := by
  have key : (∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k) =
      (∏ k ∈ Icc 1 n, (n / k).factorial ^ k) * A n := by
    rw [num_eq, den_eq, A, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d _
    rw [← pow_add]
    congr 1
    have h : ∀ k, n / k / d = n / d / k := by
      intro k
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [h]
    have := b_add n (n / d) (Nat.div_le_self n d)
    omega
  have hden : (∏ k ∈ Icc 1 n, (n / k).factorial ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hq : a n = ((∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k : ℕ) : ℚ) /
      ((∏ k ∈ Icc 1 n, (n / k).factorial ^ k : ℕ) : ℚ) := by
    unfold a
    simp only [Nat.cast_prod, Nat.cast_pow]
  rw [hq, key, Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast hden)]

lemma fac_f (p d : ℕ) (_hp : p.Prime) :
    (f d).factorization p = if IsPrimePow d ∧ d.minFac = p then 1 else 0 := by
  unfold f
  by_cases h : IsPrimePow d
  · rw [if_pos h, (Nat.minFac_prime h.ne_one).factorization, Finsupp.single_apply]
    simp [h]
  · rw [if_neg h]
    simp [h]

lemma val_A (n p : ℕ) (hp : p.Prime) :
    (A n).factorization p =
      ∑ d ∈ Icc 1 n, b (n / d) * (if IsPrimePow d ∧ d.minFac = p then 1 else 0) := by
  unfold A
  rw [Nat.factorization_prod (fun d _ => pow_ne_zero _ (f_pos d).ne'),
    Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, fac_f p d hp]

lemma lt_pow (p k : ℕ) (hp : 2 ≤ p) : k < p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have : p ^ k * 2 ≤ p ^ k * p := Nat.mul_le_mul_left _ hp
    omega

lemma reindex (n p : ℕ) (hp : p.Prime) (g : ℕ → ℕ) (hg : ∀ d, n < d → g d = 0) :
    ∑ d ∈ Icc 1 n, g d * (if IsPrimePow d ∧ d.minFac = p then 1 else 0) =
      ∑ r ∈ Icc 1 n, g (p ^ r) := by
  have h1 : ∀ r ∈ Icc 1 n, g (p ^ r) = ∑ d ∈ Icc 1 n, (if d = p ^ r then g d else 0) := by
    intro r _
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [Finset.mem_Icc] at h
      have : 0 < p ^ r := pow_pos hp.pos r
      exact hg _ (by omega)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  by_cases hP : IsPrimePow d ∧ d.minFac = p
  · rw [if_pos hP, mul_one]
    obtain ⟨q, k, hq, hk, hqk⟩ := (isPrimePow_nat_iff d).mp hP.1
    have hqp : q = p := by
      rw [← hP.2, ← hqk, Nat.pow_minFac hk.ne', hq.minFac_eq]
    subst hqp
    subst hqk
    have hinj := Nat.pow_right_injective hq.two_le
    have : ∀ r, (q ^ k = q ^ r) ↔ (k = r) := fun r => hinj.eq_iff
    simp only [this]
    rw [Finset.sum_ite_eq, if_pos]
    have := lt_pow q k hq.two_le
    rw [Finset.mem_Icc]
    omega
  · rw [if_neg hP, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [if_neg]
    rintro rfl
    exact hP ⟨hp.isPrimePow.pow (by omega), by rw [Nat.pow_minFac (by omega), hp.minFac_eq]⟩

lemma b_zero : b 0 = 0 := by simp [b]

lemma fact_A (n p : ℕ) (hp : p.Prime) :
    (A n).factorization p = ∑ r ∈ Icc 1 n, b (n / p ^ r) := by
  rw [val_A n p hp]
  exact reindex n p hp (fun d => b (n / d)) (fun d hd => by
    rw [Nat.div_eq_of_lt hd, b_zero])

lemma val (n p : ℕ) (hp : p.Prime) :
    padicValRat p (a n) = ((∑ r ∈ Icc 1 n, b (n / p ^ r) : ℕ) : ℤ) := by
  rw [a_eq, padicValRat.of_nat, ← Nat.factorization_def _ hp, fact_A n p hp]

lemma ext (n N p : ℕ) (hp : p.Prime) (hN : n ≤ N) :
    ∑ r ∈ Icc 1 n, b (n / p ^ r) = ∑ r ∈ Icc 1 N, b (n / p ^ r) := by
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
  intro r hr hr'
  rw [Finset.mem_Icc] at hr hr'
  have := lt_pow p r hp.two_le
  rw [Nat.div_eq_of_lt (by omega), b_zero]

lemma b_pos (m : ℕ) : 1 ≤ b m ↔ 3 ≤ m := by
  constructor
  · intro h
    by_contra h'
    have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl | rfl <;> revert h <;> decide
  · intro h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hmem : j + 2 ∈ Icc 1 (j + 3) := by rw [Finset.mem_Icc]; omega
    have h1 : (j + 3) % (j + 2) = 1 := by
      rw [show j + 3 = 1 + (j + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    calc 1 = (j + 3) % (j + 2) := h1.symm
      _ ≤ b (j + 3) := Finset.single_le_sum (f := fun k => (j + 3) % k)
          (fun _ _ => Nat.zero_le _) hmem

lemma dvd_A (n p : ℕ) (hn : 0 < n) (hp : p.Prime) : p ∣ A n ↔ p ≤ n / 3 := by
  rw [hp.dvd_iff_one_le_factorization (A_ne_zero n), fact_A n p hp,
    Nat.le_div_iff_mul_le (by norm_num)]
  constructor
  · intro h
    by_contra hc
    have : ∑ r ∈ Icc 1 n, b (n / p ^ r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_Icc] at hr
      by_contra hne
      have h3 := (b_pos _).mp (Nat.one_le_iff_ne_zero.mpr hne)
      have hle : n / p ^ r ≤ n / p :=
        Nat.div_le_div_left (Nat.le_self_pow (by omega) p) hp.pos
      have h4 : 3 ≤ n / p := h3.trans hle
      rw [Nat.le_div_iff_mul_le hp.pos] at h4
      apply hc
      rw [mul_comm]; exact h4
    omega
  · intro h
    have hmem : 1 ∈ Icc 1 n := by rw [Finset.mem_Icc]; omega
    have h3 : 3 ≤ n / p ^ 1 := by
      rw [pow_one, Nat.le_div_iff_mul_le hp.pos, mul_comm]; exact h
    calc 1 ≤ b (n / p ^ 1) := (b_pos _).mpr h3
      _ ≤ ∑ r ∈ Icc 1 n, b (n / p ^ r) :=
          Finset.single_le_sum (f := fun r => b (n / p ^ r)) (fun _ _ => Nat.zero_le _) hmem

lemma shift (N : ℕ) (g : ℕ → ℕ) : ∑ r ∈ Icc 1 N, g r = ∑ i ∈ range N, g (i + 1) := by
  rw [show Icc 1 N = Ioc 0 N from Finset.Icc_add_one_left_eq_Ioc 0 N]
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ]

lemma div_succ (x p r : ℕ) : x / p ^ (r + 1) = x / p / p ^ r := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

end C2

open C2 in
theorem conjecture2 (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (∃ m : ℕ, a n = m ∧ p ∣ m) ↔ p ≤ n / 3 := by
  constructor
  · rintro ⟨m, hm, hpm⟩
    rw [a_eq] at hm
    have : A n = m := by exact_mod_cast hm
    rw [← this] at hpm
    exact (dvd_A n p hn hp).mp hpm
  · intro h
    exact ⟨A n, a_eq n, (dvd_A n p hn hp).mpr h⟩

open C2 in
theorem conjecture3 (n p k : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) :
    padicValRat p (a (n * p)) = padicValRat p (a (n * p + k)) := by
  rw [val _ p hp, val _ p hp, ext (n * p) (n * p + k) p hp (Nat.le_add_right _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_Icc] at hr
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h1 : (n * p + k) / p = n := by
    rw [add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hk, zero_add]
  have h2 : n * p / p = n := Nat.mul_div_cancel n hp.pos
  rw [div_succ, div_succ, h1, h2]

open C2 in
theorem conjecture4 (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ) := by
  rw [tsum_eq_sum (s := Finset.range (n * p)), val _ p hp, shift, Nat.cast_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [div_succ, Nat.mul_div_cancel n hp.pos]
  · intro i hi
    rw [Finset.mem_range] at hi
    have h1 := lt_pow p i hp.two_le
    have h2 : n ≤ n * p := Nat.le_mul_of_pos_right n hp.pos
    rw [Nat.div_eq_of_lt (by omega), b_zero, Nat.cast_zero]

end OeisA129365

#print axioms OeisA129365.conjecture2
#print axioms OeisA129365.conjecture3
#print axioms OeisA129365.conjecture4
