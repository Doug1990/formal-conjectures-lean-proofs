import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Finset
open scoped Topology Nat

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

end Set

namespace Erdos859

def DivisorSumSet (t : ℕ) := { n : ℕ | ∃ s ⊆ Nat.divisors n, t = ∑ i ∈ s, i }

lemma count_congr' (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ k, p k ↔ q k)
    (n : ℕ) : Nat.count p n = Nat.count q n := by
  simp only [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => h x))

lemma count_bound (q : ℕ → Prop) [DecidablePred q] (L : ℕ) (hL : 0 < L)
    (hq : ∀ k, q (k + L) ↔ q k) (n : ℕ) :
    |(Nat.count q n : ℝ) - n * (Nat.count q L / L)| ≤ L := by
  have hsh : ∀ m k, q (m * L + k) ↔ q k := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [show (m + 1) * L + k = (m * L + k) + L by ring, hq, ih]
  have hmul : ∀ m, Nat.count q (m * L) = m * Nat.count q L := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [add_mul, one_mul, Nat.count_add, ih, count_congr' _ q (fun k => hsh m k)]
      ring
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < L ∧ n = m * L + r :=
    ⟨n / L, n % L, Nat.mod_lt _ hL, (Nat.div_add_mod' n L).symm⟩
  rw [Nat.count_add, hmul, count_congr' _ q (fun k => hsh m k)]
  push_cast
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (m : ℝ) * L * (Nat.count q L / L) = m * Nat.count q L := by
    calc (m : ℝ) * L * (Nat.count q L / L) = m * (L * Nat.count q L / L) := by ring
      _ = m * Nat.count q L := by rw [mul_div_cancel_left₀ _ hL']
  have hcr : (Nat.count q r : ℝ) ≤ r := by exact_mod_cast Nat.count_le q
  have hrL : (r : ℝ) ≤ L := by exact_mod_cast hr.le
  have hc : (Nat.count q L : ℝ) / L ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.count_le q) (Nat.cast_nonneg _)
  have hc0 : 0 ≤ (Nat.count q L : ℝ) / L := by positivity
  have h1 : (r : ℝ) * (Nat.count q L / L) ≤ r :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) hc
  have h2 : 0 ≤ (r : ℝ) * (Nat.count q L / L) := by positivity
  have h3 : (0 : ℝ) ≤ Nat.count q r := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

lemma shift_bound (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hL : 0 < L)
    (hq : ∀ k, p (k + L + 1) ↔ p (k + 1)) (b : ℕ) :
    |(Nat.count p b : ℝ) - b * (Nat.count (fun k => p (k + 1)) L / L)| ≤ L + 2 := by
  cases b with
  | zero =>
    simp only [Nat.count_zero, Nat.cast_zero, zero_mul, sub_zero, abs_zero]
    positivity
  | succ n =>
    rw [Nat.count_succ']
    have h1 := count_bound (fun k => p (k + 1)) L hL hq n
    have hc : (Nat.count (fun k => p (k + 1)) L : ℝ) / L ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast Nat.count_le (fun k => p (k + 1))) (Nat.cast_nonneg _)
    have hc0 : 0 ≤ (Nat.count (fun k => p (k + 1)) L : ℝ) / L := by positivity
    rw [abs_le] at h1 ⊢
    obtain ⟨h1a, h1b⟩ := h1
    split_ifs <;> push_cast <;> constructor <;> nlinarith

lemma density_of_periodic (S : Set ℕ) [DecidablePred (· ∈ S)] (L : ℕ) (hL : 0 < L)
    (hq : ∀ k, (k + L + 1 ∈ S ↔ k + 1 ∈ S)) :
    S.HasDensity ((Nat.count (fun k => k + 1 ∈ S) L : ℝ) / L) := by
  have hbound := shift_bound (· ∈ S) L hL hq
  unfold Set.HasDensity
  have hpd : ∀ b : ℕ, Set.partialDensity S Set.univ b = (Nat.count (· ∈ S) b : ℝ) / b := by
    intro b
    have e1 : (S ∩ Set.univ ∩ Set.Iio b) = (((range b).filter (· ∈ S) : Finset ℕ) : Set ℕ) := by
      ext n
      simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_Iio,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      tauto
    have e2 : (Set.univ ∩ Set.Iio b : Set ℕ) = ((range b : Finset ℕ) : Set ℕ) := by
      ext n
      simp
    unfold Set.partialDensity
    rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range,
      Nat.count_eq_card_filter_range]
  simp only [hpd]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((L + 2) / ε)
  refine ⟨N + 1, fun b hb => ?_⟩
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hNb : (N : ℝ) ≤ b := by exact_mod_cast (show N ≤ b by omega)
  rw [Real.dist_eq, show (Nat.count (· ∈ S) b : ℝ) / b - Nat.count (fun k => k + 1 ∈ S) L / L
      = ((Nat.count (· ∈ S) b : ℝ) - b * (Nat.count (fun k => k + 1 ∈ S) L / L)) / b by
      rw [sub_div, mul_div_cancel_left₀ _ hb0.ne'],
    abs_div, abs_of_pos hb0, div_lt_iff₀ hb0]
  have h1 := hbound b
  have h2 : (L + 2 : ℝ) < N * ε := (div_lt_iff₀ hε).1 hN
  nlinarith

lemma transfer (t n m : ℕ) (hm : m ≠ 0) (h : ∀ d, 1 ≤ d → d ≤ t → d ∣ n → d ∣ m) :
    n ∈ DivisorSumSet t → m ∈ DivisorSumSet t := by
  rintro ⟨s, hs, rfl⟩
  refine ⟨s, fun i hi => ?_, rfl⟩
  have hin := hs hi
  have hpos := Nat.pos_of_mem_divisors hin
  rw [Nat.mem_divisors] at hin ⊢
  exact ⟨h i hpos (Finset.single_le_sum (fun j _ => Nat.zero_le j) hi) hin.1, hm⟩

lemma fact_mem (t : ℕ) : t ! ∈ DivisorSumSet t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨∅, Finset.empty_subset _, by simp⟩
  · refine ⟨{t}, Finset.singleton_subset_iff.2 (Nat.mem_divisors.2
      ⟨Nat.dvd_factorial ht le_rfl, (Nat.factorial_pos t).ne'⟩), by simp⟩

theorem erdos_859.variants.positive_density (t : ℕ) :
    (DivisorSumSet t).HasPosDensity := by
  classical
  have hL : 0 < t ! := Nat.factorial_pos t
  have hper : ∀ k, (k + t ! + 1 ∈ DivisorSumSet t ↔ k + 1 ∈ DivisorSumSet t) := by
    intro k
    have e : k + t ! + 1 = t ! + (k + 1) := by ring
    constructor
    · refine transfer t _ _ (by omega) (fun d hd1 hdt hd => ?_)
      exact (Nat.dvd_add_right (Nat.dvd_factorial hd1 hdt)).1 (e ▸ hd)
    · refine transfer t _ _ (by omega) (fun d hd1 hdt hd => ?_)
      rw [e]
      exact (Nat.dvd_add_right (Nat.dvd_factorial hd1 hdt)).2 hd
  have hpos : 0 < Nat.count (fun k => k + 1 ∈ DivisorSumSet t) t ! :=
    by
      rw [show t ! = (Nat.factorial t - 1) + 1 by omega, Nat.count_succ, if_pos (by
        show Nat.factorial t - 1 + 1 ∈ DivisorSumSet t
        rw [Nat.sub_add_cancel hL]; exact fact_mem t)]
      omega
  refine ⟨_, ?_, density_of_periodic (DivisorSumSet t) t ! hL hper⟩
  have : (0 : ℝ) < Nat.count (fun k => k + 1 ∈ DivisorSumSet t) t ! := by exact_mod_cast hpos
  positivity

end Erdos859

#print axioms Erdos859.erdos_859.variants.positive_density
