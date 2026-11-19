import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

namespace Erdos878

/-- The function $f(n)=\sum_{p\mid n}p^{\lfloor\log_p n\rfloor}$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- The function $H(x)=\sum_{1\le n<x}f(n)/n$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

namespace LF

lemma tele_eq (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ x ∈ Ico a b, (1 : ℝ) / ((x : ℝ) * (x + 1)) = 1 / a - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    push_cast
    field_simp
    ring

lemma tele (a b : ℕ) (ha : 1 ≤ a) :
    ∑ x ∈ Ico a b, (1 : ℝ) / ((x : ℝ) * (x + 1)) ≤ 1 / a := by
  rcases le_or_gt a b with h | h
  · rw [tele_eq a b ha h]
    have : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
    linarith
  · rw [Ico_eq_empty (by omega), sum_empty]
    positivity

lemma sq_tail (m X : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Ico m X, (1 : ℝ) / ((i : ℝ) ^ 2) ≤ 2 / m := by
  calc ∑ i ∈ Ico m X, (1 : ℝ) / ((i : ℝ) ^ 2)
      ≤ ∑ i ∈ Ico m X, (2 : ℝ) / ((i : ℝ) * (i + 1)) := by
        apply sum_le_sum
        intro i hi
        rw [mem_Ico] at hi
        have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = 2 * ∑ i ∈ Ico m X, (1 : ℝ) / ((i : ℝ) * (i + 1)) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 2 * (1 / m) := by
        have := tele m X hm
        linarith
    _ = 2 / m := by ring

lemma inv_sq_sum (R : ℕ) : ∑ r ∈ range R, (1 : ℝ) / ((r : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h; simp
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot h]
    have h0 : (1 : ℝ) / (((0 : ℕ) : ℝ) ^ 2) = 0 := by simp
    rw [h0, zero_add]
    have := sq_tail 1 R le_rfl
    simpa using this

lemma block (r : ℕ) :
    ∑ p ∈ (range (2 ^ (r + 1))).filter (fun p => p.Prime ∧ 2 ^ r ≤ p),
      (1 : ℝ) / (p * Real.log p) ≤ 8 / ((r : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : ∑ p ∈ (range (2 ^ (0 + 1))).filter (fun p => p.Prime ∧ 2 ^ 0 ≤ p),
        (1 : ℝ) / (p * Real.log p) = 0 := by
      apply sum_eq_zero
      intro p hp
      rw [mem_filter, mem_range] at hp
      have h2 := hp.2.1.two_le
      have h3 : p < 2 := by simpa using hp.1
      omega
    rw [this]
    simp
  · set B := (range (2 ^ (r + 1))).filter (fun p => p.Prime ∧ 2 ^ r ≤ p) with hB
    have hc : r * B.card ≤ 2 ^ (r + 2) := by
      have h1 : (2 ^ r) ^ B.card ≤ ∏ p ∈ B, p :=
        Finset.pow_card_le_prod B (fun p => p) (2 ^ r) (fun p hp => (mem_filter.mp hp).2.2)
      have h2 : ∏ p ∈ B, p ≤ primorial (2 ^ (r + 1)) := by
        unfold primorial
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro p hp
          rw [hB, mem_filter, mem_range] at hp
          rw [mem_filter, mem_range]
          exact ⟨by omega, hp.2.1⟩
        · intro p hp _
          exact (mem_filter.mp hp).2.one_lt.le
      have h3 := primorial_le_four_pow (2 ^ (r + 1))
      have h4 : (2 ^ r) ^ B.card ≤ 4 ^ 2 ^ (r + 1) := h1.trans (h2.trans h3)
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h4
      have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
      calc r * B.card ≤ 2 * 2 ^ (r + 1) := h5
        _ = 2 ^ (r + 2) := by ring
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hl2 := Real.log_two_gt_d9
    calc ∑ p ∈ B, (1 : ℝ) / (p * Real.log p) ≤ ∑ p ∈ B, (2 : ℝ) / (r * 2 ^ r) := by
          apply sum_le_sum
          intro p hp
          have hp2 : 2 ^ r ≤ p := (mem_filter.mp hp).2.2
          have hpR : (2 : ℝ) ^ r ≤ p := by exact_mod_cast hp2
          have hlog : (r : ℝ) * Real.log 2 ≤ Real.log p := by
            rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpR
          have hlp : (r : ℝ) / 2 ≤ Real.log p := by nlinarith
          have hlp0 : 0 < Real.log p := by linarith
          have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hpR
          rw [div_le_div_iff₀ (mul_pos hp0 hlp0) (by positivity)]
          have : (2 : ℝ) ^ r * ((r : ℝ) / 2) ≤ p * Real.log p :=
            mul_le_mul hpR hlp (by positivity) (by positivity)
          nlinarith
      _ = B.card * ((2 : ℝ) / (r * 2 ^ r)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 8 / ((r : ℝ) ^ 2) := by
          have hcR : (r : ℝ) * B.card ≤ 2 ^ (r + 2) := by exact_mod_cast hc
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have e : (2 : ℝ) ^ (r + 2) = 4 * 2 ^ r := by ring
          rw [e] at hcR
          nlinarith [mul_le_mul_of_nonneg_left hcR (show (0 : ℝ) ≤ 2 * r by positivity)]

lemma primes_sum (X : ℕ) :
    ∑ p ∈ (range X).filter Nat.Prime, (1 : ℝ) / (p * Real.log p) ≤ 16 := by
  set P := (range X).filter Nat.Prime with hP
  rw [← sum_fiberwise_of_maps_to (s := P) (t := range X) (g := fun p => Nat.log 2 p)
    (fun p hp => by
      simp only [hP, mem_filter, mem_range] at hp ⊢
      have := Nat.log_lt_self 2 (show p ≠ 0 from hp.2.ne_zero)
      omega)]
  calc ∑ r ∈ range X, ∑ p ∈ P.filter (fun p => Nat.log 2 p = r), (1 : ℝ) / (p * Real.log p)
      ≤ ∑ r ∈ range X, 8 / ((r : ℝ) ^ 2) := by
        apply sum_le_sum
        intro r _
        refine le_trans ?_ (block r)
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [hP, mem_filter, mem_range] at hp ⊢
          obtain ⟨⟨_, hpp⟩, hl⟩ := hp
          refine ⟨?_, hpp, ?_⟩
          · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
            rw [hl] at this; exact this
          · have := Nat.pow_log_le_self 2 hpp.ne_zero
            rw [hl] at this; exact this
        · intro p _ _
          exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
    _ = 8 * ∑ r ∈ range X, (1 : ℝ) / ((r : ℝ) ^ 2) := by
        rw [mul_sum]; refine sum_congr rfl fun r _ => ?_; ring
    _ ≤ 8 * 2 := by have := inv_sq_sum X; linarith
    _ = 16 := by norm_num

lemma pp (p X : ℕ) (hp : p.Prime) :
    ∑ n ∈ (Ico 1 X).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2)
      ≤ 2 / p * (Nat.log p X + 1) := by
  have hp2 := hp.two_le
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hsub : (Ico 1 X).filter (p ∣ ·) ⊆ (Ico 1 X).image (p * ·) := by
    intro n hn
    rw [mem_filter, mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, ⟨i, rfl⟩⟩ := hn
    rw [mem_image]
    refine ⟨i, ?_, rfl⟩
    rw [mem_Ico]
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp at h1
      · exact h
    have : i ≤ p * i := Nat.le_mul_of_pos_left i hp0
    exact ⟨hi, by omega⟩
  calc _ ≤ ∑ n ∈ (Ico 1 X).image (p * ·), (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Ico 1 X, (p : ℝ) ^ (Nat.log p i) / p * (1 / ((i : ℝ) ^ 2)) := by
        rw [sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp0 hab)]
        refine sum_congr rfl fun i hi => ?_
        rw [mem_Ico] at hi
        rw [mul_comm p i, Nat.log_mul_base (by omega) (by omega), pow_succ]
        have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
        push_cast
        field_simp
    _ = ∑ K ∈ range (Nat.log p X + 1), ∑ i ∈ (Ico 1 X).filter (fun i => Nat.log p i = K),
          (p : ℝ) ^ (Nat.log p i) / p * (1 / ((i : ℝ) ^ 2)) := by
        refine (sum_fiberwise_of_maps_to (g := fun i => Nat.log p i)
          (t := range (Nat.log p X + 1)) ?_ _).symm
        intro i hi
        simp only [mem_Ico, mem_range] at hi ⊢
        have := Nat.log_mono_right (b := p) hi.2.le
        omega
    _ ≤ ∑ K ∈ range (Nat.log p X + 1), 2 / (p : ℝ) := by
        apply sum_le_sum
        intro K _
        have hsub2 : (Ico 1 X).filter (fun i => Nat.log p i = K) ⊆ Ico (p ^ K) X := by
          intro i hi
          rw [mem_filter, mem_Ico] at hi
          rw [mem_Ico]
          have := Nat.pow_log_le_self p (show i ≠ 0 by omega)
          rw [hi.2] at this
          exact ⟨this, hi.1.2⟩
        calc ∑ i ∈ (Ico 1 X).filter (fun i => Nat.log p i = K),
              (p : ℝ) ^ (Nat.log p i) / p * (1 / ((i : ℝ) ^ 2))
            = ∑ i ∈ (Ico 1 X).filter (fun i => Nat.log p i = K),
              (p : ℝ) ^ K / p * (1 / ((i : ℝ) ^ 2)) := by
              refine sum_congr rfl fun i hi => ?_
              rw [(mem_filter.mp hi).2]
          _ = (p : ℝ) ^ K / p * ∑ i ∈ (Ico 1 X).filter (fun i => Nat.log p i = K),
              (1 / ((i : ℝ) ^ 2)) := by rw [mul_sum]
          _ ≤ (p : ℝ) ^ K / p * ∑ i ∈ Ico (p ^ K) X, (1 / ((i : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity))
                (by positivity)
          _ ≤ (p : ℝ) ^ K / p * (2 / ((p ^ K : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (sq_tail _ X (Nat.one_le_pow _ _ hp0)) (by positivity)
          _ = 2 / p := by
              push_cast
              field_simp
    _ = 2 / p * (Nat.log p X + 1) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

lemma pp2 (p X : ℕ) (hp : p.Prime) (hpX : p < X) :
    ∑ n ∈ (Ico 1 X).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2)
      ≤ 4 * Real.log X * (1 / (p * Real.log p)) := by
  have hp2 := hp.two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hX0 : X ≠ 0 := by omega
  have hlpX : Real.log p ≤ Real.log X :=
    Real.log_le_log hpR (by exact_mod_cast hpX.le)
  have hK : (Nat.log p X : ℝ) * Real.log p ≤ Real.log X := by
    have h := Nat.pow_log_le_self p hX0
    have h' : (p : ℝ) ^ (Nat.log p X) ≤ X := by exact_mod_cast h
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h'
  have hK2 : ((Nat.log p X : ℝ) + 1) * Real.log p ≤ 2 * Real.log X := by nlinarith
  calc _ ≤ (2 : ℝ) / p * ((Nat.log p X : ℝ) + 1) := pp p X hp
    _ = 2 * ((Nat.log p X : ℝ) + 1) / p := by ring
    _ ≤ 4 * Real.log X / (p * Real.log p) := by
        rw [div_le_div_iff₀ hpR (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hK2 (show (0 : ℝ) ≤ 2 * p by positivity)]
    _ = 4 * Real.log X * (1 / (p * Real.log p)) := by ring

lemma fsum (X : ℕ) :
    ∑ n ∈ Ico 1 X, (f n : ℝ) / ((n : ℝ) ^ 2) ≤ 64 * Real.log X := by
  set P := (range X).filter Nat.Prime with hP
  have hlX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  calc ∑ n ∈ Ico 1 X, (f n : ℝ) / ((n : ℝ) ^ 2)
      ≤ ∑ n ∈ Ico 1 X, ∑ p ∈ P.filter (· ∣ n), (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2) := by
        apply sum_le_sum
        intro n hn
        rw [mem_Ico] at hn
        have e : (f n : ℝ) / ((n : ℝ) ^ 2)
            = ∑ p ∈ n.primeFactors, (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2) := by
          unfold f
          push_cast
          rw [Finset.sum_div]
        rw [e]
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          rw [hP, mem_filter, mem_filter, mem_range]
          have := Nat.le_of_dvd (by omega) hp'.2.1
          exact ⟨⟨by omega, hp'.1⟩, hp'.2.1⟩
        · intro p _ _
          positivity
    _ = ∑ p ∈ P, ∑ n ∈ (Ico 1 X).filter (p ∣ ·), (p : ℝ) ^ (Nat.log p n) / ((n : ℝ) ^ 2) := by
        apply Finset.sum_comm'
        intro n p
        simp only [mem_filter]
        tauto
    _ ≤ ∑ p ∈ P, 4 * Real.log X * (1 / (p * Real.log p)) := by
        apply sum_le_sum
        intro p hp
        rw [hP, mem_filter, mem_range] at hp
        exact pp2 p X hp.2 hp.1
    _ = 4 * Real.log X * ∑ p ∈ P, (1 / (p * Real.log p)) := by rw [mul_sum]
    _ ≤ 4 * Real.log X * 16 := by
        have := primes_sum X
        rw [← hP] at this
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 64 * Real.log X := by ring

lemma H_nonneg (x : ℕ) : 0 ≤ H x := by
  unfold H
  exact sum_nonneg fun n _ => by positivity

lemma avg (X : ℕ) :
    ∑ x ∈ Ico 1 X, H x / ((x : ℝ) * (x + 1)) ≤ ∑ n ∈ Ico 1 X, (f n : ℝ) / ((n : ℝ) ^ 2) := by
  have e1 : ∀ x : ℕ, H x / ((x : ℝ) * (x + 1))
      = ∑ n ∈ Ico 1 x, (f n : ℝ) / n * (1 / ((x : ℝ) * (x + 1))) := by
    intro x
    unfold H
    rw [div_eq_mul_one_div, sum_mul]
  simp_rw [e1]
  calc ∑ x ∈ Ico 1 X, ∑ n ∈ Ico 1 x, (f n : ℝ) / n * (1 / ((x : ℝ) * (x + 1)))
      = ∑ n ∈ Ico 1 X, ∑ x ∈ Ico (n + 1) X, (f n : ℝ) / n * (1 / ((x : ℝ) * (x + 1))) := by
        apply Finset.sum_comm'
        intro x n
        simp only [mem_Ico]
        omega
    _ ≤ ∑ n ∈ Ico 1 X, (f n : ℝ) / ((n : ℝ) ^ 2) := by
        apply sum_le_sum
        intro n hn
        rw [mem_Ico] at hn
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        rw [← mul_sum]
        have ht := tele (n + 1) X (by omega)
        push_cast at ht
        have hfn : (0 : ℝ) ≤ (f n : ℝ) / n := by positivity
        calc (f n : ℝ) / n * ∑ i ∈ Ico (n + 1) X, 1 / ((i : ℝ) * (i + 1))
            ≤ (f n : ℝ) / n * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left ht hfn
          _ ≤ (f n : ℝ) / n * (1 / n) := by
              apply mul_le_mul_of_nonneg_left _ hfn
              exact one_div_le_one_div_of_le (by linarith) (by linarith)
          _ = (f n : ℝ) / ((n : ℝ) ^ 2) := by ring

lemma harm (a b : ℕ) (hab : a ≤ b) :
    Real.log ((b : ℝ) + 1) - Real.log ((a : ℝ) + 1) ≤ ∑ x ∈ Ico a b, (1 : ℝ) / ((x : ℝ) + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have key : Real.log ((b : ℝ) + 1 + 1) - Real.log ((b : ℝ) + 1) ≤ 1 / ((b : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) by positivity)
      have e : ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) - 1 = 1 / ((b : ℝ) + 1) := by
        field_simp
        ring
      linarith
    push_cast
    linarith

end LF

/-- Erdős [Er84e] showed that $\liminf_{x\to\infty}H(x)/x<\infty$. -/
theorem erdos_878.variants.H_div_self_liminf_finite :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, H x / (x : ℝ) ≤ C := by
  refine ⟨200, ?_⟩
  by_contra hcon
  rw [Filter.not_frequently, Filter.eventually_atTop] at hcon
  obtain ⟨x0, hx0⟩ := hcon
  set y := x0 + 2 with hy
  set X := y ^ 4 with hXdef
  have hyX : y ≤ X := Nat.le_self_pow (by norm_num) y
  have hlow : 200 * (Real.log ((X : ℝ) + 1) - Real.log ((y : ℝ) + 1))
      ≤ ∑ x ∈ Ico 1 X, H x / ((x : ℝ) * (x + 1)) := by
    calc 200 * (Real.log ((X : ℝ) + 1) - Real.log ((y : ℝ) + 1))
        ≤ 200 * ∑ x ∈ Ico y X, (1 : ℝ) / ((x : ℝ) + 1) := by
          have := LF.harm y X hyX
          linarith
      _ = ∑ x ∈ Ico y X, (200 : ℝ) / ((x : ℝ) + 1) := by
          rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; ring
      _ ≤ ∑ x ∈ Ico y X, H x / ((x : ℝ) * (x + 1)) := by
          apply sum_le_sum
          intro x hx
          rw [mem_Ico] at hx
          have h1 := hx0 x (by omega)
          push Not at h1
          have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
          rw [lt_div_iff₀ hxR] at h1
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ ∑ x ∈ Ico 1 X, H x / ((x : ℝ) * (x + 1)) := by
          apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl)
          intro x _ _
          have := LF.H_nonneg x
          positivity
  have hup := (LF.avg X).trans (LF.fsum X)
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
  have hL : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hyR
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hXlog : Real.log (X : ℝ) = 4 * Real.log y := by
    rw [hXdef]; push_cast; rw [Real.log_pow]; push_cast; ring
  have hX1 : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1) := by
    have : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by positivity)
    exact Real.log_le_log this (by linarith)
  have hy1 : Real.log ((y : ℝ) + 1) ≤ Real.log 2 + Real.log y := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  linarith

end Erdos878

#print axioms Erdos878.erdos_878.variants.H_div_self_liminf_finite
