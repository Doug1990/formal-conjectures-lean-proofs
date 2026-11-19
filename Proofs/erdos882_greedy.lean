import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.BitIndices
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

/-- The arithmetic core. -/
lemma core (m N k1 k2 s1 s2 q : ℕ) (hN : N = m * 2 ^ m)
    (hs1 : s1 < 2 ^ m) (hs2 : s2 < 2 ^ m) (hk1 : 1 ≤ k1) (hk2 : k2 ≤ m)
    (hne : (k1, s1) ≠ (k2, s2)) (hq : (k1 * N + s1) * q = k2 * N + s2)
    (hpos : 0 < s2) (hnu : ∀ q, 2 ≤ q → q * s1 = s2 → q * k1 ≠ k2) : False := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hP : 2 ^ m ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hm
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · simp at hq; omega
    · rw [mul_one] at hq
      rcases Nat.lt_trichotomy k1 k2 with h | h | h
      · have : (k1 + 1) * N ≤ k2 * N := Nat.mul_le_mul_right _ h
        nlinarith
      · subst h
        apply hne; congr 1; omega
      · have : (k2 + 1) * N ≤ k1 * N := Nat.mul_le_mul_right _ h
        nlinarith
  · have hexp : (k1 * N + s1) * q = (q * k1) * N + q * s1 := by ring
    rw [hexp] at hq
    rcases Nat.lt_trichotomy (q * k1) k2 with h | h | h
    · have h1 : (q * k1 + 1) * N ≤ k2 * N := Nat.mul_le_mul_right _ h
      have h2 : (q * k1) * N < (m + 1) * N := by
        have : k2 * N ≤ m * N := Nat.mul_le_mul_right _ hk2
        nlinarith
      have h3 : q * k1 < m + 1 := Nat.lt_of_mul_lt_mul_right h2
      have h4 : q ≤ m := by nlinarith
      have h5 : q * s1 < q * 2 ^ m := Nat.mul_lt_mul_of_pos_left hs1 (by omega)
      have h6 : q * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ h4
      nlinarith
    · rw [h] at hq
      have : q * s1 = s2 := by omega
      exact hnu q hq2 this h
    · have : (k2 + 1) * N ≤ (q * k1) * N := Nat.mul_le_mul_right _ h
      nlinarith

end SD

theorem erdos_882.variants.sandor (m : ℕ) (hm : 1 ≤ m) :
    IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m)) := by
  classical
  set N := m * 2 ^ m with hN
  set f : ℕ → ℕ := fun i => 2 ^ i + N with hf
  have finj : Function.Injective f := by
    intro i j h
    have h' : 2 ^ i + N = 2 ^ j + N := h
    exact Nat.pow_right_injective le_rfl (show 2 ^ i = 2 ^ j by omega)
  -- decomposition of a subset
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
  have sumI : ∀ I : Finset ℕ, ∑ a ∈ I.image f, a = I.card * N + ∑ i ∈ I, 2 ^ i := by
    intro I
    rw [Finset.sum_image (fun i _ j _ h => finj h)]
    simp only [hf]
    rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)]
    ring
  have small : ∀ I ⊆ Finset.range m, ∑ i ∈ I, 2 ^ i < 2 ^ m := by
    intro I hI
    exact Nat.geomSum_lt le_rfl (fun k hk => Finset.mem_range.mp (hI hk))
  intro S₁ h₁ S₂ h₂ ne₁ ne₂ hne hdvd
  obtain ⟨I₁, hI₁, rfl⟩ := dec S₁ h₁
  obtain ⟨I₂, hI₂, rfl⟩ := dec S₂ h₂
  rw [sumI, sumI] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hInj : Function.Injective (fun s : Finset ℕ => ∑ i ∈ s, 2 ^ i) :=
    Finset.geomSum_injective le_rfl
  have nI₁ : I₁.Nonempty := by simpa using ne₁
  have nI₂ : I₂.Nonempty := by simpa using ne₂
  refine SD.core m N I₁.card I₂.card (∑ i ∈ I₁, 2 ^ i) (∑ i ∈ I₂, 2 ^ i) q hN
    (small I₁ hI₁) (small I₂ hI₂) (Finset.card_pos.mpr nI₁)
    ((Finset.card_le_card hI₂).trans (by simp)) ?_ hq.symm ?_ ?_
  · intro h
    apply hne
    have : I₁ = I₂ := hInj (Prod.ext_iff.mp h).2
    rw [this]
  · obtain ⟨x, hx⟩ := nI₂
    exact lt_of_lt_of_le (Nat.two_pow_pos x)
      (Finset.single_le_sum (f := fun i => 2 ^ i) (fun _ _ => Nat.zero_le _) hx)
  · intro q hq2 hs hk
    have e1 := SD.nu_card I₁
    have e2 := SD.nu_card I₂
    rw [← hs] at e2
    have hle := SD.nu_mul_le q (∑ i ∈ I₁, 2 ^ i)
    have hlt := SD.nu_lt q hq2
    have hc : 0 < I₁.card := Finset.card_pos.mpr nI₁
    rw [e2, e1] at hle
    rw [← hk] at hle
    have : SD.nu q * I₁.card < q * I₁.card := Nat.mul_lt_mul_of_pos_right hlt hc
    omega

namespace GR

lemma lt2 : ∀ k : ℕ, k < 2 ^ k
  | 0 => by norm_num
  | k + 1 => by
    have := lt2 k
    rw [pow_succ]; omega

lemma key : ∀ k : ℕ, 3 ≤ k → (k + 2) * 2 ^ (k + 1) ≤ 3 ^ (k + 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ 3]
    have h1 : (k + 1 + 2) * 2 ≤ 3 * (k + 2) := by omega
    have h2 : (k + 1 + 2) * 2 * 2 ^ (k + 1) ≤ 3 * (k + 2) * 2 ^ (k + 1) :=
      Nat.mul_le_mul_right _ h1
    have h3 : 3 * ((k + 2) * 2 ^ (k + 1)) ≤ 3 * 3 ^ (k + 1) := Nat.mul_le_mul_left _ ih
    calc (k + 1 + 2) * (2 ^ (k + 1) * 2) = (k + 1 + 2) * 2 * 2 ^ (k + 1) := by ring
      _ ≤ 3 * (k + 2) * 2 ^ (k + 1) := h2
      _ = 3 * ((k + 2) * 2 ^ (k + 1)) := by ring
      _ ≤ 3 * 3 ^ (k + 1) := h3
      _ = 3 ^ (k + 1) * 3 := by ring

/-- Sándor's set lies in `[1, n]` and has `m` elements, so `m ≤ maxAntichainCard n`. -/
lemma card_le (m n : ℕ) (hm : 1 ≤ m) (h : (m + 1) * 2 ^ m ≤ n) :
    m ≤ maxAntichainCard n := by
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  · refine ⟨(Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m), ?_,
      erdos_882.variants.sandor m hm, ?_⟩
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hi' : i < m := Finset.mem_range.mp hi
      have h1 : 2 ^ i ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hi'.le
      have h2 : 0 < 2 ^ i := Nat.two_pow_pos i
      have h3 : (m + 1) * 2 ^ m = m * 2 ^ m + 2 ^ m := by ring
      rw [Finset.mem_Icc]
      omega
    · rw [Finset.card_image_of_injective, Finset.card_range]
      intro i j hij
      have h' : 2 ^ i + m * 2 ^ m = 2 ^ j + m * 2 ^ m := hij
      exact Nat.pow_right_injective le_rfl (show 2 ^ i = 2 ^ j by omega)

end GR

theorem erdos_882.variants.greedy :
    ∀ᶠ n : ℕ in Filter.atTop, (Real.logb 3 n - 1 : ℝ) ≤ (maxAntichainCard n : ℝ) := by
  classical
  rw [Filter.eventually_atTop]
  refine ⟨32, fun n hn => ?_⟩
  have hex : ∃ m, n < (m + 2) * 2 ^ (m + 1) := by
    refine ⟨n, ?_⟩
    have h1 := GR.lt2 (n + 1)
    have h2 : 2 ^ (n + 1) ≤ (n + 2) * 2 ^ (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨m, hm1, hmin⟩ : ∃ m, n < (m + 2) * 2 ^ (m + 1) ∧
      ∀ j < m, ¬ n < (j + 2) * 2 ^ (j + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with h | h | h <;> subst h <;> norm_num at hm1 <;> omega
  have hlow : (m + 1) * 2 ^ m ≤ n := by
    have := hmin (m - 1) (by omega)
    have e : m - 1 + 2 = m + 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e, e2] at this
    omega
  have hn3 : n ≤ 3 ^ (m + 1) := le_trans hm1.le (GR.key m hm3)
  have hcard : m ≤ maxAntichainCard n := GR.card_le m n (by omega) hlow
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h1 : Real.logb 3 n ≤ (m : ℝ) + 1 := by
    calc Real.logb 3 n ≤ Real.logb 3 ((3 : ℝ) ^ (m + 1)) :=
          Real.logb_le_logb_of_le (by norm_num) hnpos (by exact_mod_cast hn3)
      _ = (m : ℝ) + 1 := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          push_cast; ring
  have h2 : (m : ℝ) ≤ (maxAntichainCard n : ℝ) := by exact_mod_cast hcard
  linarith

end Erdos882

#print axioms Erdos882.erdos_882.variants.greedy
