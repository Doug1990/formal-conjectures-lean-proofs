import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset

namespace Erdos882

def IsSubsetSumAntichain (A : Finset ℕ) : Prop :=
  ∀ S₁ ⊆ A, ∀ S₂ ⊆ A, S₁.Nonempty → S₂.Nonempty → S₁ ≠ S₂ →
    ¬ (∑ a ∈ S₁, a) ∣ (∑ a ∈ S₂, a)

noncomputable def maxAntichainCard (n : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = k}

def A (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => 2 ^ m - 2 ^ i)

namespace SD

/-- binary digit sum -/
def nu (n : ℕ) : ℕ := n.bitIndices.length

lemma nu_zero : nu 0 = 0 := by simp [nu]

lemma nu_rec (n : ℕ) : nu n = n % 2 + nu (n / 2) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k % 2 = 0 := by omega
    rw [h1, h2]
    simp [nu]
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    rw [h1, h2]
    simp [nu]
    omega

lemma nu_two_mul (n : ℕ) : nu (2 * n) = nu n := by
  rw [nu_rec]
  have h1 : 2 * n / 2 = n := by omega
  have h2 : 2 * n % 2 = 0 := by omega
  rw [h1, h2]; simp

lemma nu_one : nu 1 = 1 := by simp [nu]

lemma nu_add_le : ∀ n a b : ℕ, a + b = n → nu (a + b) ≤ nu a + nu b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb; simp [nu_zero]
    have ra := nu_rec a
    have rb := nu_rec b
    rw [nu_rec (a + b)]
    rcases Nat.lt_or_ge (a % 2 + b % 2) 2 with hc | hc
    · have e1 : (a + b) % 2 = a % 2 + b % 2 := by omega
      have e2 : (a + b) / 2 = a / 2 + b / 2 := by omega
      have := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      rw [e1, e2]; omega
    · have e1 : (a + b) % 2 = 0 := by omega
      have e2 : (a + b) / 2 = (a / 2 + b / 2) + 1 := by omega
      have h3 := ih (a / 2 + b / 2 + 1) (by omega) (a / 2 + b / 2) 1 rfl
      have h4 := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      rw [e1, e2, nu_one] at *
      omega

lemma nu_add (a b : ℕ) : nu (a + b) ≤ nu a + nu b := nu_add_le _ a b rfl

lemma nu_mul_le : ∀ q s : ℕ, nu (q * s) ≤ nu q * nu s := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro s
    rcases Nat.lt_or_ge q 1 with hq | hq
    · have : q = 0 := by omega
      subst this; simp [nu_zero]
    have e : q * s = 2 * ((q / 2) * s) + (q % 2) * s := by
      conv_lhs => rw [← Nat.div_add_mod q 2]
      ring
    have h1 := ih (q / 2) (by omega) s
    have hr := nu_rec q
    rw [e]
    refine (nu_add _ _).trans ?_
    rw [nu_two_mul]
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · rw [h] at hr ⊢; simp [nu_zero]
      rw [hr]; simpa using h1
    · rw [h] at hr ⊢
      rw [hr]; simp only [one_mul]
      nlinarith

lemma nu_lt : ∀ q : ℕ, 2 ≤ q → nu q < q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    rw [nu_rec]
    rcases Nat.lt_or_ge (q / 2) 2 with h | h
    · have : q / 2 = 1 := by omega
      rw [this, nu_one]; omega
    · have := ih (q / 2) (by omega) h
      omega

lemma nu_card (S : Finset ℕ) : nu (∑ i ∈ S, 2 ^ i) = S.card := by
  conv_rhs => rw [← Finset.toFinset_bitIndices_sum_two_pow S]
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  rfl

end SD

namespace LB

open SD

/-- `n - nu n` is monotone. -/
lemma mono (t q : ℕ) (h : t ≤ q) : t + nu q ≤ q + nu t := by
  induction q, h using Nat.le_induction with
  | base => omega
  | succ q hq ih =>
    have := nu_add q 1
    rw [nu_one] at this
    omega

/-- Binary concatenation. -/
lemma append : ∀ m s t : ℕ, s < 2 ^ m → nu (s + 2 ^ m * t) = nu s + nu t := by
  intro m
  induction m with
  | zero =>
    intro s t hs
    have : s = 0 := by simp at hs; omega
    subst this
    simp [nu_zero]
  | succ m ih =>
    intro s t hs
    have hp : 2 ^ (m + 1) * t = 2 * (2 ^ m * t) := by ring
    have hs' : s < 2 * 2 ^ m := by rw [pow_succ] at hs; omega
    rw [hp, nu_rec (s + 2 * (2 ^ m * t)), nu_rec s]
    have e1 : (s + 2 * (2 ^ m * t)) % 2 = s % 2 := by omega
    have e2 : (s + 2 * (2 ^ m * t)) / 2 = s / 2 + 2 ^ m * t := by omega
    rw [e1, e2, ih (s / 2) t (by omega)]
    omega

lemma uniq (a b r s P : ℕ) (hr : r < P) (hs : s < P) (h : a * P + r = b * P + s) :
    a = b ∧ r = s := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have : (a + 1) * P ≤ b * P := Nat.mul_le_mul_right _ hab
    nlinarith
  · subst hab; exact ⟨rfl, by omega⟩
  · have : (b + 1) * P ≤ a * P := Nat.mul_le_mul_right _ hab
    nlinarith

lemma core (m k1 k2 s1 s2 x1 x2 q : ℕ) (hs1 : s1 < 2 ^ m) (hs2 : s2 < 2 ^ m)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hn1 : nu s1 = k1) (hn2 : nu s2 = k2)
    (hone : k1 = 1 → 2 * s1 ≤ 2 ^ m)
    (hx1 : x1 + s1 = k1 * 2 ^ m) (hx2 : x2 + s2 = k2 * 2 ^ m) (hq : x2 = x1 * q) :
    k1 = k2 ∧ s1 = s2 := by
  set P := 2 ^ m with hP
  have hPpos : 0 < P := Nat.two_pow_pos m
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · have : P ≤ k2 * P := Nat.le_mul_of_pos_left _ hk2
      simp at hq; omega
    · rw [mul_one] at hq
      subst hq
      have := uniq k1 k2 s2 s1 P hs2 hs1 (by linarith)
      exact ⟨this.1, this.2.symm⟩
  · exfalso
    set t := q * s1 / P with ht
    set r := q * s1 % P with hr
    have hdm : r + P * t = q * s1 := Nat.mod_add_div _ _
    have hrP : r < P := Nat.mod_lt _ hPpos
    have hmul : (x1 + s1) * q = k1 * P * q := by rw [hx1]
    have e : (k2 + t) * P + r = (q * k1) * P + s2 := by
      rw [hq] at hx2
      nlinarith
    obtain ⟨ha, hrs⟩ := uniq _ _ _ _ _ hrP hs2 e
    have hnu : nu (q * s1) = k2 + nu t := by
      rw [← hdm, append m r t hrP, hrs, hn2]
    have hle := nu_mul_le q s1
    rw [hnu, hn1] at hle
    have htq : t < q := by
      have h1 : q * s1 < q * P := Nat.mul_lt_mul_of_pos_left hs1 (by omega)
      have h2 : t * P < q * P := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right h2
    have hlt := nu_lt q hq2
    rcases Nat.lt_or_ge k1 2 with hk | hk
    · have hk1' : k1 = 1 := by omega
      have h2s := hone hk1'
      subst hk1'
      have h2t : 2 * t ≤ q := by
        have h1 : 2 * t * P ≤ q * P := by nlinarith
        exact Nat.le_of_mul_le_mul_right h1 hPpos
      have hm := mono (2 * t) q h2t
      rw [nu_two_mul] at hm
      simp only [mul_one] at ha hle
      omega
    · have hm := mono t q htq.le
      set d := q - nu q with hd
      have hd1 : 1 ≤ d := by omega
      have hdk : d * k1 + nu q * k1 = q * k1 := by
        rw [← add_mul]; congr 1; omega
      have h2 : d * 2 ≤ d * k1 := Nat.mul_le_mul_left _ hk
      omega

end LB

theorem erdos_882.variants.lower_bound (m : ℕ) : IsSubsetSumAntichain (A m) := by
  classical
  set f : ℕ → ℕ := fun i => 2 ^ m - 2 ^ i with hf
  have finj : Set.InjOn f (Finset.range m : Set ℕ) := by
    intro i hi j hj h
    have hi' : 2 ^ i < 2 ^ m :=
      Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hi))
    have hj' : 2 ^ j < 2 ^ m :=
      Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hj))
    have h' : 2 ^ m - 2 ^ i = 2 ^ m - 2 ^ j := h
    exact Nat.pow_right_injective le_rfl (show 2 ^ i = 2 ^ j by omega)
  have dec : ∀ S ⊆ (Finset.range m).image f, ∃ I ⊆ Finset.range m, S = I.image f := by
    intro S hS
    refine ⟨(Finset.range m).filter (fun i => f i ∈ S), Finset.filter_subset _ _, ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hS hx)
      exact ⟨i, ⟨hi, hx⟩, rfl⟩
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
  have sumI : ∀ I ⊆ Finset.range m,
      ∑ a ∈ I.image f, a + ∑ i ∈ I, 2 ^ i = I.card * 2 ^ m := by
    intro I hI
    rw [Finset.sum_image (fun i hi j hj h => finj (Finset.mem_coe.mpr (hI hi))
      (Finset.mem_coe.mpr (hI hj)) h)]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => 2 ^ m)]
    · simp
    · intro i hi
      have : 2 ^ i ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp (hI hi)).le
      simp only [hf]
      omega
  have small : ∀ I ⊆ Finset.range m, ∑ i ∈ I, 2 ^ i < 2 ^ m := by
    intro I hI
    exact Nat.geomSum_lt le_rfl (fun k hk => Finset.mem_range.mp (hI hk))
  intro S₁ h₁ S₂ h₂ ne₁ ne₂ hne hdvd
  obtain ⟨I₁, hI₁, rfl⟩ := dec S₁ h₁
  obtain ⟨I₂, hI₂, rfl⟩ := dec S₂ h₂
  obtain ⟨q, hq⟩ := hdvd
  have hInj : Function.Injective (fun s : Finset ℕ => ∑ i ∈ s, 2 ^ i) :=
    Finset.geomSum_injective le_rfl
  have nI₁ : I₁.Nonempty := by simpa using ne₁
  have nI₂ : I₂.Nonempty := by simpa using ne₂
  have hone : I₁.card = 1 → 2 * ∑ i ∈ I₁, 2 ^ i ≤ 2 ^ m := by
    intro h
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    have hi : i < m := Finset.mem_range.mp (hI₁ (Finset.mem_singleton_self i))
    rw [Finset.sum_singleton, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hi
  have := LB.core m I₁.card I₂.card (∑ i ∈ I₁, 2 ^ i) (∑ i ∈ I₂, 2 ^ i) _ _ q
    (small I₁ hI₁) (small I₂ hI₂) (Finset.card_pos.mpr nI₁) (Finset.card_pos.mpr nI₂)
    (SD.nu_card I₁) (SD.nu_card I₂) hone (sumI I₁ hI₁) (sumI I₂ hI₂) hq
  exact hne (by rw [hInj this.2])

lemma A_subset (m : ℕ) : A m ⊆ Finset.Icc 1 (2 ^ m - 1) := by
  intro a ha
  simp only [A, Finset.mem_image, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have h1 : 2 ^ i < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hi
  have h2 : 0 < 2 ^ i := Nat.two_pow_pos i
  rw [Finset.mem_Icc]
  omega

lemma A_card (m : ℕ) : (A m).card = m := by
  rw [A, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hi' : 2 ^ i < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hi))
  have hj' : 2 ^ j < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hj))
  have h : 2 ^ m - 2 ^ i = 2 ^ m - 2 ^ j := hij
  have h' : 2 ^ i = 2 ^ j := by omega
  exact Nat.pow_right_injective le_rfl h'

theorem erdos_882.variants.lower_bound_explicit (n : ℕ) (hn : 0 < n) :
    Real.logb 2 n - 1 < (maxAntichainCard n : ℝ) := by
  set m := Nat.log 2 n with hm
  have hle : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hlt : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hcard : m ≤ maxAntichainCard n := by
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro k ⟨B, hB, -, rfl⟩
      simpa using Finset.card_le_card hB
    · refine ⟨A m, ?_, erdos_882.variants.lower_bound m, A_card m⟩
      intro a ha
      have := Finset.mem_Icc.mp (A_subset m ha)
      rw [Finset.mem_Icc]
      omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.logb 2 n < (m : ℝ) + 1 := by
    calc Real.logb 2 n < Real.logb 2 ((2 : ℝ) ^ (m + 1)) :=
          Real.logb_lt_logb (by norm_num) hnpos (by exact_mod_cast hlt)
      _ = (m : ℝ) + 1 := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          push_cast; ring
  have h2 : (m : ℝ) ≤ (maxAntichainCard n : ℝ) := by exact_mod_cast hcard
  linarith

end Erdos882

#print axioms Erdos882.erdos_882.variants.lower_bound
#print axioms Erdos882.erdos_882.variants.lower_bound_explicit
