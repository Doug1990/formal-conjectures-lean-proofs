import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter

namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/-- Second moment identity: Σ_S (2 s_S - T)^2 = 2^|A| Σ a^2. -/
lemma sq_sum (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * ∑ a ∈ S, (a : ℝ) - ∑ a ∈ A, (a : ℝ)) ^ 2
      = 2 ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x A hx ih =>
    rw [Finset.sum_powerset_insert hx, Finset.sum_insert hx, Finset.card_insert_of_notMem hx,
      Finset.sum_insert hx]
    have h2 : ∀ S ∈ A.powerset,
        (2 * ∑ a ∈ insert x S, (a : ℝ) - ((x : ℝ) + ∑ a ∈ A, (a : ℝ))) ^ 2
          = (2 * ∑ a ∈ S, (a : ℝ) - ∑ a ∈ A, (a : ℝ) + x) ^ 2 := by
      intro S hS
      have hxS : x ∉ S := fun h => hx (Finset.mem_powerset.1 hS h)
      rw [Finset.sum_insert hxS]
      ring
    rw [Finset.sum_congr rfl h2, ← Finset.sum_add_distrib]
    have h3 : ∀ S ∈ A.powerset,
        (2 * ∑ a ∈ S, (a : ℝ) - ((x : ℝ) + ∑ a ∈ A, (a : ℝ))) ^ 2
          + (2 * ∑ a ∈ S, (a : ℝ) - ∑ a ∈ A, (a : ℝ) + x) ^ 2
          = 2 * (2 * ∑ a ∈ S, (a : ℝ) - ∑ a ∈ A, (a : ℝ)) ^ 2 + 2 * (x : ℝ) ^ 2 := by
      intro S _
      ring
    rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const,
      Finset.card_powerset, nsmul_eq_mul]
    push_cast
    ring

/-- Naturals whose doubles lie within L of T form a set of size at most L + 1. -/
lemma card_le_of_close (X : Finset ℕ) (T L : ℝ) (hL : 0 ≤ L)
    (h : ∀ s ∈ X, |2 * (s : ℝ) - T| < L) : (X.card : ℝ) ≤ L + 1 := by
  rcases X.eq_empty_or_nonempty with he | hne
  · simp [he]; linarith
  · set m := X.min' hne
    set M := X.max' hne
    have hsub : X ⊆ Finset.Icc m M := fun s hs =>
      Finset.mem_Icc.2 ⟨X.min'_le s hs, X.le_max' s hs⟩
    have hmM : m ≤ M := X.min'_le_max' hne
    have hc : X.card ≤ M + 1 - m := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at this
    have h1 := h M (X.max'_mem hne)
    have h2 := h m (X.min'_mem hne)
    rw [abs_lt] at h1 h2
    have hc' : (X.card : ℝ) ≤ (M : ℝ) - m + 1 := by
      have : ((M + 1 - m : ℕ) : ℝ) = (M : ℝ) - m + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hc
    linarith

lemma key (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N) (hn : 1 ≤ A.card) (hN : 1 ≤ N) :
    (3 / 4 : ℝ) * 2 ^ A.card ≤ 2 * Real.sqrt A.card * N + 1 := by
  obtain ⟨hA, hinj⟩ := h
  set n := A.card with hn_def
  set T : ℝ := ∑ a ∈ A, (a : ℝ)
  set L : ℝ := 2 * Real.sqrt n * N
  set f : Finset ℕ → ℝ := fun S => 2 * ∑ a ∈ S, (a : ℝ) - T
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := mul_nonneg (mul_nonneg zero_le_two hsqrt0) (Nat.cast_nonneg _)
  have hL2 : L ^ 2 = 4 * (n * (N : ℝ) ^ 2) := by
    simp only [L]; rw [mul_pow, mul_pow, hsq]; ring
  -- second moment bound
  have hsum : ∑ S ∈ A.powerset, f S ^ 2 ≤ 2 ^ n * (n * (N : ℝ) ^ 2) := by
    simp only [f, T]
    rw [sq_sum]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg zero_le_two _)
    have : ∑ a ∈ A, (a : ℝ) ^ 2 ≤ ∑ a ∈ A, (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have := (Finset.mem_Icc.1 (hA ha)).2
      have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      have h1 : (a : ℝ) ≤ N := by exact_mod_cast this
      exact pow_le_pow_left₀ h0 h1 2
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  set big := A.powerset.filter (fun S => L ≤ |f S|)
  set small := A.powerset.filter (fun S => ¬ L ≤ |f S|)
  have hbig : (big.card : ℝ) * L ^ 2 ≤ 2 ^ n * (n * (N : ℝ) ^ 2) := by
    have h1 : big.card • L ^ 2 ≤ ∑ S ∈ big, f S ^ 2 := by
      apply Finset.card_nsmul_le_sum
      intro S hS
      have hS' := (Finset.mem_filter.1 hS).2
      have := pow_le_pow_left₀ hL0 hS' 2
      rwa [sq_abs] at this
    have h2 : ∑ S ∈ big, f S ^ 2 ≤ ∑ S ∈ A.powerset, f S ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun S _ _ => sq_nonneg _)
    rw [nsmul_eq_mul] at h1
    linarith
  have hpos : 0 < n * (N : ℝ) ^ 2 := mul_pos (by linarith) (pow_pos (by linarith) 2)
  have hbig' : (big.card : ℝ) * 4 ≤ 2 ^ n := by
    have : ((big.card : ℝ) * 4) * (n * (N : ℝ) ^ 2) ≤ 2 ^ n * (n * (N : ℝ) ^ 2) := by
      calc ((big.card : ℝ) * 4) * (n * (N : ℝ) ^ 2) = (big.card : ℝ) * L ^ 2 := by
            rw [hL2]; ring
        _ ≤ _ := hbig
    exact le_of_mul_le_mul_right this hpos
  -- small subsets have distinct sums close to T / 2
  have hsmall : (small.card : ℝ) ≤ L + 1 := by
    have hinjOn : Set.InjOn (fun S : Finset ℕ => S.sum id) small := by
      intro S1 h1 S2 h2 heq
      have m1 : S1 ∈ A.powerset := (Finset.mem_filter.1 h1).1
      have m2 : S2 ∈ A.powerset := (Finset.mem_filter.1 h2).1
      have := @hinj ⟨S1, m1⟩ ⟨S2, m2⟩ heq
      exact congrArg Subtype.val this
    rw [← Finset.card_image_of_injOn hinjOn]
    apply card_le_of_close _ T L hL0
    intro s hs
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hs
    have hS' := (Finset.mem_filter.1 hS).2
    push Not at hS'
    have : (2 * ((S.sum id : ℕ) : ℝ) - T) = f S := by
      simp only [f]; push_cast; rfl
    rw [this]; exact hS'
  have htot : big.card + small.card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_powerset]
  have htotR : (big.card : ℝ) + small.card = 2 ^ n := by exact_mod_cast htot
  linarith

theorem erdos_1.variants.lb : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  refine ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _, ?_⟩
  intro N A h
  simp only [sub_zero]
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    have hN : 1 ≤ N := (Finset.mem_Icc.1 (h.1 ha)).1.trans (Finset.mem_Icc.1 (h.1 ha)).2
    have hk := key N A h hpos hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 0 < Real.sqrt A.card := Real.sqrt_pos.2 (by exact_mod_cast hpos)
    rw [div_le_iff₀ hs]
    rcases Nat.lt_or_ge A.card 2 with h1 | h2
    · have hc : A.card = 1 := by omega
      rw [hc]; simp; linarith
    · have h4 : (4 : ℝ) ≤ 2 ^ A.card := by
        have : (2 : ℝ) ^ 2 ≤ 2 ^ A.card := pow_le_pow_right₀ one_le_two h2
        linarith
      have : Real.sqrt A.card * N = (N : ℝ) * Real.sqrt A.card := by ring
      linarith

end Erdos1

#print axioms Erdos1.erdos_1.variants.lb
