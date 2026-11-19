import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Real

namespace Erdos673

noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

lemma fin_dvd (n : ℕ) (hn : 0 < n) : (Set.ofPred (· ∣ n)).Finite := by
  apply n.divisors.finite_toSet.subset
  intro d hd
  simp only [Finset.mem_coe, Nat.mem_divisors]
  exact ⟨hd, hn.ne'⟩

lemma card_eq (n : ℕ) (hn : 0 < n) : (fin_dvd n hn).toFinset.card = n.divisors.card := by
  congr 1
  ext d
  simp only [Set.Finite.mem_toFinset, Nat.mem_divisors]
  exact ⟨fun h => ⟨h, hn.ne'⟩, fun h => h.1⟩

lemma G_eq (n : ℕ) : G n = ∑ j ∈ Finset.range (n.divisors.card - 1),
    (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
  Fin.sum_univ_eq_sum_range (fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1)) _

lemma G_le (n : ℕ) (hn : 0 < n) : G n ≤ n.divisors.card := by
  rw [G_eq]
  have hf := fin_dvd n hn
  have hc := card_eq n hn
  calc _ ≤ ∑ j ∈ Finset.range (n.divisors.card - 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        apply div_le_one_of_le₀
        · exact_mod_cast Nat.nth_le_nth_of_lt_card hf (Nat.le_succ j) (by omega)
        · positivity
    _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact_mod_cast Nat.sub_le _ _

lemma key (n m e : ℕ) (hn : 0 < n) (hm : 1 < m) (he : e ∣ n / m) (hmn : m ∣ n) :
    Nat.count (· ∣ n) e + 1 < n.divisors.card ∧
    (1 : ℝ) / m ≤ (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
      Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
  have hf := fin_dvd n hn
  have hc := card_eq n hn
  have hnm : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (by omega)
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hnm
  have hdiv : e ∣ n := he.trans (Nat.div_dvd_of_dvd hmn)
  have hem : e * m ∣ n := by
    obtain ⟨k, hk⟩ := he
    obtain ⟨l, hl⟩ := hmn
    refine ⟨k, ?_⟩
    have : n / m = l := by rw [hl, Nat.mul_div_cancel_left _ (by omega)]
    rw [hl, ← this, hk]; ring
  have hlt : e + 1 ≤ e * m := by nlinarith
  have h1 : Nat.count (· ∣ n) (e + 1) = Nat.count (· ∣ n) e + 1 :=
    Nat.count_succ_eq_succ_count_iff.2 hdiv
  have h2 : Nat.count (· ∣ n) (e + 1) ≤ Nat.count (· ∣ n) (e * m) := Nat.count_monotone _ hlt
  have h3 : Nat.count (· ∣ n) (e * m) < n.divisors.card := hc ▸ Nat.count_lt_card hf hem
  refine ⟨by omega, ?_⟩
  rw [Nat.nth_count (p := (· ∣ n)) hdiv]
  have h4 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) ≤ e * m := by
    calc _ ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) (e * m)) :=
          Nat.nth_le_nth_of_lt_card hf (by omega) (by omega)
      _ = e * m := Nat.nth_count (p := (· ∣ n)) hem
  have h5 : e < Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
    calc e = Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) := (Nat.nth_count (p := (· ∣ n)) hdiv).symm
      _ < _ := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) (by omega)
  have he' : (0 : ℝ) < e := by exact_mod_cast hepos
  have h4' : ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) ≤ (e : ℝ) * m := by
    exact_mod_cast h4
  have h5' : (0 : ℝ) < ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_le _).trans_lt h5
  calc (1 : ℝ) / m = e / (e * m) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left he'.le h5' h4'

theorem erdos_673.variants.tao (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card := by
  refine ⟨?_, G_le n hn⟩
  rw [G_eq]
  have hnm : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (by omega)
  have hinj : Set.InjOn (Nat.count (· ∣ n)) ((n / m).divisors : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∣ n := (Nat.dvd_of_mem_divisors ha).trans (Nat.div_dvd_of_dvd hmn)
    have hb' : b ∣ n := (Nat.dvd_of_mem_divisors hb).trans (Nat.div_dvd_of_dvd hmn)
    exact Nat.count_injective ha' hb' hab
  calc ((n / m).divisors.card : ℝ) / m = ∑ e ∈ (n / m).divisors, (1 : ℝ) / m := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ e ∈ (n / m).divisors, (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
          Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
        apply Finset.sum_le_sum
        intro e he
        exact (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).2
    _ = ∑ j ∈ (n / m).divisors.image (Nat.count (· ∣ n)),
          (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
        (Finset.sum_image (f := fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1))
          hinj).symm
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hj
          rw [Finset.mem_range]
          have := (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).1
          omega
        · intro j _ _
          positivity

lemma G_nonneg (n : ℕ) : 0 ≤ G n := by
  rw [G_eq]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma G_two (k : ℕ) (hk : 0 < k) : (k.divisors.card : ℝ) / 2 ≤ G (2 * k) := by
  have h := (erdos_673.variants.tao (2 * k) 2 (by omega) (by omega) (dvd_mul_right 2 k)).1
  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)] at h
  exact_mod_cast h

lemma sum_ge (X : ℕ) :
    ∑ k ∈ Finset.Ioc 0 (X / 2), (k.divisors.card : ℝ) / 2 ≤ ∑ n ∈ Finset.Icc 1 X, G n := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (Finset.Ioc 0 (X / 2) : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  calc _ ≤ ∑ k ∈ Finset.Ioc 0 (X / 2), G (2 * k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact G_two k (Finset.mem_Ioc.1 hk).1
    _ = ∑ n ∈ (Finset.Ioc 0 (X / 2)).image (fun k : ℕ => 2 * k), G n :=
        (Finset.sum_image (f := G) hinj).symm
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hn
          rw [Finset.mem_Ioc] at hk
          rw [Finset.mem_Icc]
          omega
        · intro n _ _
          exact G_nonneg n

lemma card_divisors_eq (N n : ℕ) (hn : n ∈ Finset.Ioc 0 N) :
    n.divisors.card = (Finset.filter (· ∣ n) (Finset.Ioc 0 N)).card := by
  congr 1
  ext a
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  constructor
  · rintro ⟨h, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
  · rintro ⟨_, h⟩
    exact ⟨h, by omega⟩

lemma sum_divisors_card (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, n.divisors.card = ∑ a ∈ Finset.Ioc 0 N, N / a := by
  rw [Finset.sum_congr rfl (fun n hn => card_divisors_eq N n hn)]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]

lemma floor_ge (N a : ℕ) (ha : 0 < a) : (N : ℝ) / a - 1 ≤ ((N / a : ℕ) : ℝ) := by
  have h1 : N = a * (N / a) + N % a := (Nat.div_add_mod N a).symm
  have h2 : N % a < a := Nat.mod_lt _ ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have h1' : (N : ℝ) = a * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : ((N % a : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast h2
  rw [div_sub_one ha0.ne', div_le_iff₀ ha0]
  linarith

lemma harmonic_eq (k : ℕ) : (harmonic k : ℝ) = ∑ a ∈ Finset.Ioc 0 k, (1 / (a : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [harmonic_succ, Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih]
    push_cast
    ring

lemma tau_sum (N : ℕ) :
    (N : ℝ) * harmonic N - N ≤ ∑ k ∈ Finset.Ioc 0 N, (k.divisors.card : ℝ) := by
  have h : (∑ k ∈ Finset.Ioc 0 N, (k.divisors.card : ℝ)) =
      ∑ a ∈ Finset.Ioc 0 N, ((N / a : ℕ) : ℝ) := by
    exact_mod_cast sum_divisors_card N
  rw [h, harmonic_eq, Finset.mul_sum]
  calc _ = ∑ a ∈ Finset.Ioc 0 N, ((N : ℝ) * (1 / (a : ℝ)) - 1) := by
        rw [Finset.sum_sub_distrib]; simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        rw [mul_one_div]
        exact floor_ge N a (Finset.mem_Ioc.1 ha).1

theorem erdos_673.variants.average :
    Tendsto (fun X : ℕ ↦ (∑ n ∈ Finset.Icc 1 X, G n) / X) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  rw [eventually_atTop]
  refine ⟨2 * ⌈Real.exp (8 * b + 2)⌉₊ + 2, fun X hX => ?_⟩
  set N := X / 2 with hN
  have hN0 : ⌈Real.exp (8 * b + 2)⌉₊ + 1 ≤ N := by omega
  have h4N : X ≤ 4 * N := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have h4N' : (X : ℝ) ≤ 4 * N := by exact_mod_cast h4N
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlog : 8 * b + 2 ≤ (harmonic N : ℝ) := by
    have h1 : Real.exp (8 * b + 2) ≤ ((N + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.exp (8 * b + 2))
      have h2 : ((⌈Real.exp (8 * b + 2)⌉₊ : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show ⌈Real.exp (8 * b + 2)⌉₊ ≤ N + 1 by omega)
      linarith
    have h3 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h3
    exact h3.trans (log_add_one_le_harmonic N)
  have hS : (N : ℝ) * harmonic N / 2 - N / 2 ≤ ∑ n ∈ Finset.Icc 1 X, G n := by
    have h1 := tau_sum N
    have h2 := sum_ge X
    rw [← hN] at h2
    rw [← Finset.sum_div] at h2
    linarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 X, G n := Finset.sum_nonneg (fun n _ => G_nonneg n)
  rw [le_div_iff₀ hXpos]
  rcases le_or_gt b 0 with hb | hb
  · nlinarith
  · nlinarith

end Erdos673

#print axioms Erdos673.erdos_673.variants.tao
#print axioms Erdos673.erdos_673.variants.average
