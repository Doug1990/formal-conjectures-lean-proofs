import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos287

def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- If a prime `r ≥ 13` divides some term, and all terms are `< 4r`, then the reciprocal sum
of distinct positive integers is not `1`. -/
lemma key {k r : ℕ} (s : Fin k → ℕ) (hinj : Function.Injective s) (hpos : ∀ i, 0 < s i)
    (hr : r.Prime) (h13 : 13 ≤ r) (hlt : ∀ i, s i < 4 * r) (hex : ∃ i, r ∣ s i) :
    ∑ i, 1 / (s i : ℝ) ≠ 1 := by
  classical
  intro hsum
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ i ∈ Finset.univ.filter (fun i => ¬ r ∣ s i), s i := ⟨_, rfl⟩
  have hj : ∀ i, r ∣ s i → s i = r * (s i / r) ∧
      (s i / r = 1 ∨ s i / r = 2 ∨ s i / r = 3) := by
    intro i hi
    have h1 := Nat.mul_div_cancel' hi
    have h2 := hpos i
    have h3 := hlt i
    refine ⟨h1.symm, ?_⟩
    have h4 : s i / r < 4 := by
      rw [Nat.div_lt_iff_lt_mul hr.pos]; omega
    have h5 : 0 < s i / r := Nat.div_pos (Nat.le_of_dvd h2 hi) hr.pos
    omega
  have hdvd : ∀ i, s i ∣ r * (6 * P) := by
    intro i
    by_cases hi : r ∣ s i
    · obtain ⟨he, hj3⟩ := hj i hi
      rw [he]
      apply Nat.mul_dvd_mul_left
      have : s i / r ∣ 6 := by rcases hj3 with h | h | h <;> rw [h] <;> decide
      exact Dvd.dvd.mul_right this P
    · have : s i ∣ P := by
        rw [hP]; exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left this 6) r
  have hnat : ∑ i, r * (6 * P) / s i = r * (6 * P) := by
    have : (∑ i, ((r * (6 * P) / s i : ℕ) : ℝ)) = ((r * (6 * P) : ℕ) : ℝ) := by
      have e : ∀ i, ((r * (6 * P) / s i : ℕ) : ℝ)
          = ((r * (6 * P) : ℕ) : ℝ) * (1 / (s i : ℝ)) := by
        intro i
        rw [Nat.cast_div (hdvd i) (by exact_mod_cast (hpos i).ne')]
        ring
      simp_rw [e, ← Finset.mul_sum, hsum, mul_one]
    exact_mod_cast this
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => r ∣ s i)
    (fun i => r * (6 * P) / s i)
  have hC : r ∣ ∑ i ∈ Finset.univ.filter (fun i => ¬ r ∣ s i), r * (6 * P) / s i := by
    apply Finset.dvd_sum
    intro i hi
    have : s i ∣ 6 * P := by
      rw [hP]; exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hi) 6
    rw [Nat.mul_div_assoc _ this]
    exact dvd_mul_right r _
  have hR : r ∣ ∑ i ∈ Finset.univ.filter (fun i => r ∣ s i), r * (6 * P) / s i := by
    have h1 : r ∣ ∑ i, r * (6 * P) / s i := by rw [hnat]; exact dvd_mul_right r _
    rw [← hsplit] at h1
    exact (Nat.dvd_add_left hC).1 h1
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => r ∣ s i),
      r * (6 * P) / s i = P * (6 / (s i / r)) := by
    intro i hi
    obtain ⟨he, hj3⟩ := hj i (Finset.mem_filter.1 hi).2
    generalize s i / r = j at he hj3 ⊢
    rw [he, Nat.mul_div_mul_left _ _ hr.pos]
    rcases hj3 with rfl | rfl | rfl <;> omega
  have hcop : Nat.Coprime r P := by
    rw [hP]
    apply Nat.Coprime.prod_right
    intro i hi
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (Finset.mem_filter.1 hi).2
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hR
  have hm : r ∣ ∑ i ∈ Finset.univ.filter (fun i => r ∣ s i), 6 / (s i / r) :=
    hcop.dvd_of_dvd_mul_left hR
  have hpos_m : 0 < ∑ i ∈ Finset.univ.filter (fun i => r ∣ s i), 6 / (s i / r) := by
    obtain ⟨i0, hi0⟩ := hex
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · refine ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0⟩, ?_⟩
      rcases (hj i0 hi0).2 with h | h | h <;> rw [h] <;> decide
  have hle : ∑ i ∈ Finset.univ.filter (fun i => r ∣ s i), 6 / (s i / r) ≤ 11 := by
    have himg : ∑ j ∈ (Finset.univ.filter (fun i => r ∣ s i)).image (fun i => s i / r), 6 / j
        = ∑ i ∈ Finset.univ.filter (fun i => r ∣ s i), 6 / (s i / r) := by
      apply Finset.sum_image
      intro i hi i' hi' heq
      have heq' : s i / r = s i' / r := heq
      apply hinj
      rw [(hj i (Finset.mem_filter.1 hi).2).1, (hj i' (Finset.mem_filter.1 hi').2).1, heq']
    rw [← himg]
    calc ∑ j ∈ (Finset.univ.filter (fun i => r ∣ s i)).image (fun i => s i / r), 6 / j
        ≤ ∑ j ∈ ({1, 2, 3} : Finset ℕ), 6 / j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj'
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj'
            rcases (hj i (Finset.mem_filter.1 hi).2).2 with h | h | h <;> simp [h]
          · intros; exact Nat.zero_le _
      _ = 11 := by rfl
  have := Nat.le_of_dvd hpos_m hm
  omega

/-- `∑_{i < m+2} 1/(m+2+i) ≤ 5/6`. -/
lemma tail_le (m : ℕ) :
    ∑ i ∈ Finset.range (m + 2), (1 : ℝ) / ((m + 2 + i : ℕ) : ℝ) ≤ 5 / 6 := by
  induction m with
  | zero => norm_num [Finset.sum_range_succ]
  | succ m ih =>
    have hA : ∑ i ∈ Finset.range (m + 2), (1 : ℝ) / ((m + 2 + i : ℕ) : ℝ)
        = (∑ i ∈ Finset.range m, (1 : ℝ) / ((m + 3 + i : ℕ) : ℝ))
          + 1 / ((2 * m + 3 : ℕ) : ℝ) + 1 / ((m + 2 : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have h1 : ∀ i ∈ Finset.range m, (1 : ℝ) / ((m + 2 + (i + 1) : ℕ) : ℝ)
          = 1 / ((m + 3 + i : ℕ) : ℝ) := fun i _ => by
        rw [show m + 2 + (i + 1) = m + 3 + i by omega]
      rw [Finset.sum_congr rfl h1, show m + 2 + (m + 1) = 2 * m + 3 by omega, Nat.add_zero]
    have hB : ∑ i ∈ Finset.range (m + 3), (1 : ℝ) / ((m + 3 + i : ℕ) : ℝ)
        = (∑ i ∈ Finset.range m, (1 : ℝ) / ((m + 3 + i : ℕ) : ℝ))
          + 1 / ((2 * m + 3 : ℕ) : ℝ) + 1 / ((2 * m + 4 : ℕ) : ℝ)
          + 1 / ((2 * m + 5 : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        show m + 3 + m = 2 * m + 3 by omega, show m + 3 + (m + 1) = 2 * m + 4 by omega,
        show m + 3 + (m + 2) = 2 * m + 5 by omega]
    show ∑ i ∈ Finset.range (m + 3), (1 : ℝ) / ((m + 3 + i : ℕ) : ℝ) ≤ 5 / 6
    rw [hB]; rw [hA] at ih
    have h2 : (1 : ℝ) / ((2 * m + 4 : ℕ) : ℝ) + 1 / ((2 * m + 5 : ℕ) : ℝ)
        ≤ 1 / ((m + 2 : ℕ) : ℝ) := by
      push_cast
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h3 : (1 : ℝ) / (2 * m + 5) ≤ 1 / (2 * m + 4) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : (1 : ℝ) / (2 * m + 4) = 1 / (m + 2) / 2 := by
        rw [div_div, show ((m : ℝ) + 2) * 2 = 2 * m + 4 by ring]
      linarith
    linarith

/-- Distinct integers in `[a, 2a+1]`, `a ≥ 7`, have reciprocal sum `< 1`. -/
lemma sum_lt_one {k a : ℕ} (s : Fin k → ℕ) (hinj : Function.Injective s) (ha : 7 ≤ a)
    (hlo : ∀ i, a ≤ s i) (hhi : ∀ i, s i ≤ 2 * a + 1) : ∑ i, 1 / (s i : ℝ) < 1 := by
  classical
  have h1 : ∑ i, 1 / (s i : ℝ) = ∑ x ∈ Finset.univ.image s, 1 / (x : ℝ) := by
    rw [Finset.sum_image (fun i _ j _ h => hinj h)]
  have h2 : Finset.univ.image s ⊆ (Finset.range (a + 2)).image (fun j => a + j) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    have := hlo i
    have := hhi i
    exact Finset.mem_image.2 ⟨s i - a, Finset.mem_range.2 (by omega), by omega⟩
  have h3 : ∑ x ∈ Finset.univ.image s, 1 / (x : ℝ)
      ≤ ∑ x ∈ (Finset.range (a + 2)).image (fun j => a + j), 1 / (x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg h2 (fun x _ _ => by positivity)
  have h4 : ∑ x ∈ (Finset.range (a + 2)).image (fun j => a + j), 1 / (x : ℝ)
      = ∑ j ∈ Finset.range (a + 2), 1 / ((a + j : ℕ) : ℝ) :=
    Finset.sum_image (fun i _ j _ h => by simpa using h)
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  have h5 : ∑ j ∈ Finset.range (m + 1 + 2), (1 : ℝ) / ((m + 1 + j : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (m + 2), (1 : ℝ) / ((m + 2 + j : ℕ) : ℝ)
        + 1 / ((m + 1 : ℕ) : ℝ) := by
    show ∑ j ∈ Finset.range (m + 2 + 1), (1 : ℝ) / ((m + 1 + j : ℕ) : ℝ) = _
    rw [Finset.sum_range_succ']
    have h6 : ∀ j ∈ Finset.range (m + 2), (1 : ℝ) / ((m + 1 + (j + 1) : ℕ) : ℝ)
        = 1 / ((m + 2 + j : ℕ) : ℝ) := fun j _ => by
      rw [show m + 1 + (j + 1) = m + 2 + j by omega]
    rw [Finset.sum_congr rfl h6, Nat.add_zero]
  have h7 := tail_le m
  have h8 : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)
  rw [h1]
  linarith

theorem erdos_287.variants.prime_conjecture_implies : (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N ∧ Nat.Prime ((p + 1) / 2)) →
    ∃ (k₀ : ℕ), ∀ᵉ (k : ℕ) (hk₀ : k₀ ≤ k) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
      3 ≤ max_gap k s := by
  classical
  rintro ⟨N₀, hN₀⟩
  refine ⟨2 * N₀ + 100, ?_⟩
  intro k hk₀ hk s hs h1 hsum
  by_contra hgap
  rw [not_le] at hgap
  have hg : ∀ i (hi : i + 1 < k), s ⟨i + 1, hi⟩ ≤ s ⟨i, by omega⟩ + 2 := by
    intro i hi
    have h3 := lt_of_le_of_lt (Finset.le_sup (f := fun i : Fin (k - 1) =>
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
      (Finset.mem_univ (⟨i, by omega⟩ : Fin (k - 1)))) hgap
    try dsimp only at h3
    omega
  have hinj : Function.Injective s := hs.injective
  obtain ⟨a, ha⟩ : ∃ a, s ⟨0, by omega⟩ = a := ⟨_, rfl⟩
  have hlow : ∀ i (hi : i < k), a + i ≤ s ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      have : s ⟨0, hi⟩ = a := ha
      omega
    | succ i ih =>
      intro hi
      have := ih (by omega)
      have h2 : s ⟨i, by omega⟩ < s ⟨i + 1, hi⟩ := hs (Fin.mk_lt_mk.2 (by omega))
      omega
  obtain ⟨b, hb⟩ : ∃ b, s ⟨k - 1, by omega⟩ = b := ⟨_, rfl⟩
  have hup : ∀ i, s i ≤ b := fun i => hb ▸ hs.monotone
    (Fin.le_iff_val_le_val.2 (by have := i.isLt; show i.val ≤ k - 1; omega))
  have hdown : ∀ i, a ≤ s i := fun i => ha ▸ hs.monotone
    (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
  have hbk : a + (k - 1) ≤ b := by
    have h' := hlow (k - 1) (by omega)
    have h'' : s ⟨k - 1, by omega⟩ = b := hb
    omega
  have ha2 : 2 ≤ a := by
    have : s ⟨0, by omega⟩ = a := ha
    omega
  have hb2 : 2 * a + 2 ≤ b := by
    by_contra hcon
    have h7 : 7 ≤ a := by omega
    have := sum_lt_one s hinj h7 hdown (fun i => by have := hup i; omega)
    linarith
  obtain ⟨p, hp, hNp, hp2N, hq⟩ := hN₀ (b / 2) (by omega)
  have hp50 : 50 ≤ p := by omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  by_cases hin : ∃ i, s i = p
  · obtain ⟨i, hi⟩ := hin
    exact key s hinj (fun j => by have := hdown j; omega) hp (by omega)
      (fun j => by have := hup j; omega) ⟨i, by simp [hi]⟩ hsum
  · push Not at hin
    have hex : ∃ j, ∃ hj : j < k, p ≤ s ⟨j, hj⟩ :=
      ⟨k - 1, by omega, by have : s ⟨k - 1, by omega⟩ = b := hb; omega⟩
    obtain ⟨j, hjk, hjp, hmin⟩ : ∃ j, ∃ hj : j < k, p ≤ s ⟨j, hj⟩ ∧
        ∀ j' (hj' : j' < j), s ⟨j', by omega⟩ < p := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j' hj' => ?_⟩
      have := Nat.find_min hex hj'
      push Not at this
      exact this _
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        have : s ⟨0, hjk⟩ = a := ha
        omega
      · exact ⟨j - 1, by omega⟩
    have hlt := hmin j' (by omega)
    have hgj := hg j' hjk
    have hne := hin ⟨j' + 1, hjk⟩
    have hval : s ⟨j' + 1, hjk⟩ = p + 1 := by omega
    exact key s hinj (fun i => by have := hdown i; omega) hq (by omega)
      (fun i => by have := hup i; omega)
      ⟨⟨j' + 1, hjk⟩, by rw [hval]; exact Dvd.intro_left 2 (by omega)⟩ hsum

end Erdos287

#print axioms Erdos287.erdos_287.variants.prime_conjecture_implies
