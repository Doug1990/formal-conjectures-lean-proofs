import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos295

/-- Fibonacci–Sylvester: a/b < 1/M is a sum of distinct unit fractions with denominators > M. -/
lemma egypt (a : ℕ) : ∀ b M : ℕ, 0 < M → 0 < a → M * a < b →
    ∃ S : Finset ℕ, (∀ s ∈ S, M < s) ∧ ∑ s ∈ S, (1 / s : ℚ) = a / b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b M hM ha hab
  have hdiv := Nat.div_add_mod b a
  have hlt := Nat.mod_lt b ha
  set q := b / a with hq
  set t := b % a with ht
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) hab
  have hab' : a < b := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left a hM) hab
  by_cases h0 : t = 0
  · have hqa : b = a * q := by omega
    refine ⟨{q}, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      by_contra hc
      push Not at hc
      have h1 : q * a ≤ M * a := Nat.mul_le_mul_right a hc
      have h2 : b ≤ M * a := by rw [hqa, Nat.mul_comm]; exact h1
      exact absurd hab (not_lt.2 h2)
    · have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h] at hqa; omega
        · exact h
      rw [Finset.sum_singleton, hqa]
      push_cast
      have : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
      field_simp
  · have hbq : b < (q + 1) * a := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q a]; omega
    have hMq : M < q + 1 := by
      by_contra hc
      push Not at hc
      have h2 : (q + 1) * a ≤ M * a := Nat.mul_le_mul_right a hc
      exact lt_irrefl b (lt_trans (lt_of_lt_of_le hbq h2) hab)
    obtain ⟨S, hS, hsum⟩ := ih (a - t) (by omega) ((q + 1) * b) (q + 1) (by omega) (by omega)
      (mul_lt_mul_of_pos_left (by omega) (by omega))
    have hn : q + 1 ∉ S := fun h => lt_irrefl _ (hS _ h)
    refine ⟨insert (q + 1) S, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · exact hMq
      · exact lt_trans hMq (hS s hs)
    · rw [Finset.sum_insert hn, hsum]
      have key : ((a - t : ℕ) : ℚ) = (q + 1) * a - b := by
        have : (b : ℚ) = a * q + t := by exact_mod_cast hdiv.symm
        rw [Nat.cast_sub (by omega), this]
        ring
      rw [key]
      push_cast
      have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      have : ((q : ℚ) + 1) ≠ 0 := by
        have : (0 : ℚ) ≤ q := Nat.cast_nonneg q
        exact ne_of_gt (by linarith)
      field_simp
      ring

lemma half (N : ℕ) (hN : 0 < N) : (1 / 2 : ℚ) ≤ ∑ i ∈ Finset.Ico N (2 * N), (1 / i : ℚ) := by
  have h : ∀ i ∈ Finset.Ico N (2 * N), (1 / (2 * N : ℚ)) ≤ 1 / i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h0 : (0 : ℚ) < i := by exact_mod_cast (show 0 < i by omega)
    have : (i : ℚ) ≤ 2 * N := by exact_mod_cast (show i ≤ 2 * N by omega)
    exact one_div_le_one_div_of_le h0 this
  have hcard := Finset.card_nsmul_le_sum _ _ _ h
  rw [Nat.card_Ico, nsmul_eq_mul] at hcard
  have hc : ((2 * N - N : ℕ) : ℚ) = N := by
    rw [show 2 * N - N = N by omega]
  rw [hc] at hcard
  have : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  calc (1 / 2 : ℚ) = N * (1 / (2 * N)) := by field_simp
    _ ≤ _ := hcard

lemma one_le (N : ℕ) (hN : 0 < N) : (1 : ℚ) ≤ ∑ i ∈ Finset.Ico N (4 * N), (1 / i : ℚ) := by
  rw [← Finset.sum_Ico_consecutive _ (show N ≤ 2 * N by omega) (show 2 * N ≤ 4 * N by omega)]
  have h1 := half N hN
  have h2 := half (2 * N) (by omega)
  rw [show 2 * (2 * N) = 4 * N by ring] at h2
  linarith

lemma exists_set (N : ℕ) (hN : 2 ≤ N) :
    ∃ S : Finset ℕ, (∀ s ∈ S, N ≤ s) ∧ ∑ s ∈ S, (1 / s : ℚ) = 1 := by
  classical
  have hex : ∃ m, (1 : ℚ) ≤ ∑ i ∈ Finset.Ico N m, (1 / i : ℚ) := ⟨_, one_le N (by omega)⟩
  obtain ⟨m0, hP, hmin⟩ : ∃ m0, (1 : ℚ) ≤ ∑ i ∈ Finset.Ico N m0, (1 / i : ℚ) ∧
      ∀ k < m0, ¬ (1 : ℚ) ≤ ∑ i ∈ Finset.Ico N k, (1 / i : ℚ) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hm0pos : m0 ≠ 0 := by
    intro h
    rw [h] at hP
    simp at hP
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, m0 = m + 1 := ⟨m0 - 1, by omega⟩
  have hnP := hmin m (by omega)
  push Not at hnP
  have hmN : N ≤ m := by
    by_contra hc
    push Not at hc
    rw [Finset.Ico_eq_empty (by omega)] at hP
    simp at hP
    linarith
  rw [Finset.sum_Ico_succ_top hmN] at hP
  set H := ∑ i ∈ Finset.Ico N m, (1 / i : ℚ) with hH
  set r : ℚ := 1 - H with hr
  have rpos : 0 < r := by linarith
  have hm1 : (1 : ℚ) < m := by exact_mod_cast (show 1 < m by omega)
  have rlt : r < 1 / ((m - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    have : 1 / (m : ℚ) < 1 / ((m : ℚ) - 1) :=
      one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith
  -- write r = a / b
  have hnum : 0 < r.num := Rat.num_pos.2 rpos
  set a := r.num.toNat with ha
  set b := r.den with hb
  have hrab : r = (a : ℚ) / b := by
    have : ((a : ℤ) : ℚ) = (r.num : ℚ) := by
      rw [ha, Int.toNat_of_nonneg hnum.le]
    rw [← Int.cast_natCast a, this, hb]
    exact (Rat.num_div_den r).symm
  have ha0 : 0 < a := by omega
  have hb0 : (0 : ℚ) < b := by exact_mod_cast r.den_pos
  have hMab : (m - 1) * a < b := by
    have h1 : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    rw [hrab, div_lt_div_iff₀ hb0 h1] at rlt
    have : (((m - 1) * a : ℕ) : ℚ) < b := by rw [Nat.cast_mul]; linarith
    exact_mod_cast this
  obtain ⟨T, hT, hTsum⟩ := egypt a b (m - 1) (by omega) ha0 hMab
  have hdisj : Disjoint (Finset.Ico N m) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    rw [Finset.mem_Ico] at hx
    have := hT x hxT
    omega
  refine ⟨Finset.Ico N m ∪ T, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_union] at hs
    rcases hs with hs | hs
    · exact (Finset.mem_Ico.1 hs).1
    · have := hT s hs; omega
  · rw [Finset.sum_union hdisj, hTsum, ← hrab]
    linarith [hH, hr]

lemma exists_k (N : ℕ) : ∃ (k : ℕ) (n : Fin k → ℕ),
    (∀ i, N ≤ n i) ∧ StrictMono n ∧ ∑ i, (1 / n i : ℝ) = 1 := by
  obtain ⟨S, hS, hsum⟩ := exists_set (max N 2) (le_max_right _ _)
  refine ⟨S.card, S.orderEmbOfFin rfl, ?_, (S.orderEmbOfFin rfl).strictMono, ?_⟩
  · intro i
    exact le_trans (le_max_left _ _) (hS _ (S.orderEmbOfFin_mem rfl i))
  · have h1 : ∑ i, (1 / (S.orderEmbOfFin rfl i : ℕ) : ℝ) = ∑ s ∈ S, (1 / s : ℝ) := by
      conv_rhs => rw [← Finset.image_orderEmbOfFin_univ S rfl]
      rw [Finset.sum_image (fun x _ y _ h => (S.orderEmbOfFin rfl).injective h)]
    rw [h1]
    have h2 := congrArg (Rat.castHom ℝ) hsum
    rw [map_sum] at h2
    simpa using h2

end Erdos295

#print axioms Erdos295.exists_k
