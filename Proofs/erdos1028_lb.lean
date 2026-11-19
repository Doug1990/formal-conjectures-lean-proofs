import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Lattice.Nat

open Filter

namespace Erdos1028

def imbalance (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|

noncomputable def H (n : ℕ) : ℕ :=
  sInf {m | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)}

namespace LB

def S (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ := ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y

lemma S_union (f : ℕ → ℕ → ℤ) (U V : Finset ℕ) (h : ∀ x ∈ U, ∀ y ∈ V, x < y) :
    S f (U ∪ V) = S f U + S f V + ∑ x ∈ U, ∑ y ∈ V, f x y := by
  have hd : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact lt_irrefl a (h a ha a hb)
  unfold S
  rw [Finset.sum_union hd]
  have h1 : ∀ x ∈ U, ∑ y ∈ (U ∪ V).filter (fun y => x < y), f x y
      = ∑ y ∈ U.filter (fun y => x < y), f x y + ∑ y ∈ V, f x y := by
    intro x hx
    rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hd)]
    congr 1
    rw [Finset.filter_true_of_mem]
    intro y hy
    exact h x hx y hy
  have h2 : ∀ x ∈ V, ∑ y ∈ (U ∪ V).filter (fun y => x < y), f x y
      = ∑ y ∈ V.filter (fun y => x < y), f x y := by
    intro x hx
    rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hd)]
    rw [Finset.filter_false_of_mem, Finset.sum_empty, zero_add]
    intro y hy hxy
    exact lt_asymm hxy (h y hy x hx)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

lemma abs_S_le (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (X : Finset ℕ) :
    |S f X| ≤ (X.card : ℤ) * X.card := by
  unfold S
  calc |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|
      ≤ ∑ x ∈ X, |∑ y ∈ X.filter (fun y => x < y), f x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ X, ∑ y ∈ X, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro x _
        calc |∑ y ∈ X.filter (fun y => x < y), f x y|
            ≤ ∑ y ∈ X.filter (fun y => x < y), |f x y| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ y ∈ X.filter (fun y => x < y), (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro y _
              rcases hf x y with h | h <;> simp [h]
          _ ≤ ∑ y ∈ X, (1 : ℤ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by norm_num)
    _ = (X.card : ℤ) * X.card := by simp

lemma ten (a1 a2 a3 a4 a5 : ℤ) (h1 : a1 = 1 ∨ a1 = -1) (h2 : a2 = 1 ∨ a2 = -1)
    (h3 : a3 = 1 ∨ a3 = -1) (h4 : a4 = 1 ∨ a4 = -1) (h5 : a5 = 1 ∨ a5 = -1) :
    12 ≤ |a1+a2+a3| + |a1+a2+a4| + |a1+a2+a5| + |a1+a3+a4| + |a1+a3+a5| + |a1+a4+a5|
      + |a2+a3+a4| + |a2+a3+a5| + |a2+a4+a5| + |a3+a4+a5| := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl <;> norm_num

lemma triple (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (n m : ℕ)
    (hm : ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ))
    (hn : 5 ≤ n) (i j k : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) (hk : k ≤ 5)
    (h : 6 * ((n : ℤ) - 5) ≤ 5 * ∑ b ∈ Finset.Icc 6 n, |f i b + f j b + f k b|) :
    6 * (n : ℤ) - 120 ≤ 20 * m := by
  set c : ℕ → ℤ := fun b => f i b + f j b + f k b with hc
  set B := Finset.Icc 6 n with hB
  set T : Finset ℕ := {i, j, k} with hT
  have hTsub : T ⊆ Finset.Icc 1 n := by
    intro x hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    omega
  have hTcard : |S f T| ≤ 9 := by
    have h1 := abs_S_le f hf T
    have h2 : T.card ≤ 3 := Finset.card_le_three
    have h3 : (T.card : ℤ) ≤ 3 := by exact_mod_cast h2
    have h4 : (0 : ℤ) ≤ T.card := by positivity
    nlinarith
  -- generic estimate for a subset B' of B
  have gen : ∀ B' ⊆ B, |∑ y ∈ B', c y| ≤ 2 * m + 9 := by
    intro B' hB'
    have hlt : ∀ x ∈ T, ∀ y ∈ B', x < y := by
      intro x hx y hy
      have := hB' hy
      simp only [hB, Finset.mem_Icc] at this
      simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    have hu := S_union f T B' hlt
    have hcross : ∑ x ∈ T, ∑ y ∈ B', f x y = ∑ y ∈ B', c y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      have hi' : i ∉ ({j, k} : Finset ℕ) := by simp; omega
      have hj' : j ∉ ({k} : Finset ℕ) := by simp; omega
      rw [hT, Finset.sum_insert hi', Finset.sum_insert hj', Finset.sum_singleton]
      simp only [hc]
      ring
    have hB'n : B' ⊆ Finset.Icc 1 n := by
      intro y hy
      have := hB' hy
      simp only [hB, Finset.mem_Icc] at this ⊢
      omega
    have e1 : |S f (T ∪ B')| ≤ m := hm _ (Finset.union_subset hTsub hB'n)
    have e2 : |S f B'| ≤ m := hm _ hB'n
    rw [hcross] at hu
    rw [abs_le] at e1 e2 hTcard ⊢
    constructor <;> linarith
  have hsplit : ∑ b ∈ B, |c b| = ∑ b ∈ B.filter (fun b => 0 < c b), c b
      - ∑ b ∈ B.filter (fun b => ¬ 0 < c b), c b := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun b => 0 < c b)]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mem_filter] at hb
      exact abs_of_pos hb.2
    · apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mem_filter] at hb
      exact abs_of_nonpos (not_lt.mp hb.2)
  have g1 := gen _ (Finset.filter_subset (fun b => 0 < c b) B)
  have g2 := gen _ (Finset.filter_subset (fun b => ¬ 0 < c b) B)
  rw [abs_le] at g1 g2
  have hh : ∑ b ∈ B, |c b| = ∑ b ∈ Finset.Icc 6 n, |f i b + f j b + f k b| := rfl
  linarith [hsplit, hh]

lemma bound (n m : ℕ) (hn : 120 ≤ n) (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1)
    (hm : ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)) : (n : ℤ) ≤ 4 * m := by
  have h5 : 5 ≤ n := by omega
  set B := Finset.Icc 6 n with hB
  have hcard : ((B.card : ℕ) : ℤ) = (n : ℤ) - 5 := by
    rw [hB, Nat.card_Icc]
    have e : n + 1 - 6 + 5 = n := by omega
    have e' : ((n + 1 - 6 : ℕ) : ℤ) + 5 = n := by exact_mod_cast e
    linarith
  have hsum : 12 * ((n : ℤ) - 5) ≤
      ∑ b ∈ B, |f 1 b + f 2 b + f 3 b| + ∑ b ∈ B, |f 1 b + f 2 b + f 4 b|
      + ∑ b ∈ B, |f 1 b + f 2 b + f 5 b| + ∑ b ∈ B, |f 1 b + f 3 b + f 4 b|
      + ∑ b ∈ B, |f 1 b + f 3 b + f 5 b| + ∑ b ∈ B, |f 1 b + f 4 b + f 5 b|
      + ∑ b ∈ B, |f 2 b + f 3 b + f 4 b| + ∑ b ∈ B, |f 2 b + f 3 b + f 5 b|
      + ∑ b ∈ B, |f 2 b + f 4 b + f 5 b| + ∑ b ∈ B, |f 3 b + f 4 b + f 5 b| := by
    simp only [← Finset.sum_add_distrib]
    rw [← hcard]
    have := Finset.card_nsmul_le_sum B _ (12 : ℤ)
      (fun b _ => ten _ _ _ _ _ (hf 1 b) (hf 2 b) (hf 3 b) (hf 4 b) (hf 5 b))
    rw [nsmul_eq_mul] at this
    linarith
  rcases le_or_gt (6 * (n : ℤ) - 120) (20 * m) with h | h
  · have : (120 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  · exfalso
    have t := fun i j k hi hij hjk hk =>
      lt_of_not_ge (fun hh => absurd (triple f hf n m hm h5 i j k hi hij hjk hk hh) (not_le.mpr h))
    have a1 := t 1 2 3 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a2 := t 1 2 4 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a3 := t 1 2 5 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a4 := t 1 3 4 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a5 := t 1 3 5 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a6 := t 1 4 5 le_rfl (by norm_num) (by norm_num) (by norm_num)
    have a7 := t 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a8 := t 2 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a9 := t 2 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a10 := t 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    linarith

lemma nonempty (n : ℕ) : (n * n) ∈ {m : ℕ | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)} := by
  refine ⟨fun _ _ => 1, fun _ _ => Or.inl rfl, ?_⟩
  intro X hX
  have h1 := abs_S_le (fun _ _ => 1) (fun _ _ => Or.inl rfl) X
  have h2 : X.card ≤ n := by
    have := Finset.card_le_card hX
    simpa using this
  have h3 : (X.card : ℤ) ≤ n := by exact_mod_cast h2
  have h4 : (0 : ℤ) ≤ X.card := by positivity
  have h5 : imbalance (fun _ _ => 1) X = |S (fun _ _ => 1) X| := rfl
  rw [h5]
  push_cast
  nlinarith

end LB

theorem erdos_1028.variants.lower_bound :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ (H n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨120, fun n hn => ?_⟩
  obtain ⟨f, hf, hm⟩ := Nat.sInf_mem ⟨_, LB.nonempty n⟩
  have h := LB.bound n (H n) hn f hf hm
  have h' : (n : ℝ) ≤ 4 * (H n : ℝ) := by exact_mod_cast h
  linarith

#print axioms erdos_1028.variants.lower_bound

end Erdos1028
