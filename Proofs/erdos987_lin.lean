import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

open Filter Finset

/-- Restated from FormalConjecturesForMathlib/Analysis/SpecialFunctions/AdditiveCharacter.lean. -/
noncomputable def additiveChar (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[inherit_doc]
scoped[ExponentialSum] notation "e" => additiveChar

open scoped ExponentialSum

namespace Erdos987

noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

namespace VDC

/-- The van der Corput sequence (binary digit reversal). -/
noncomputable def v : ℕ → ℝ
  | 0 => 0
  | (j + 1) => (v ((j + 1) / 2) + (((j + 1) % 2 : ℕ) : ℝ)) / 2
decreasing_by omega

lemma v_zero : v 0 = 0 := by rw [v]

lemma v_eq (j : ℕ) : v j = (v (j / 2) + ((j % 2 : ℕ) : ℝ)) / 2 := by
  cases j with
  | zero => simp [v_zero]
  | succ m => rw [v]

lemma v_even (q : ℕ) : v (2 * q) = v q / 2 := by
  rw [v_eq (2 * q)]
  have h1 : 2 * q / 2 = q := by omega
  have h2 : 2 * q % 2 = 0 := by omega
  rw [h1, h2]; simp

lemma v_odd (q : ℕ) : v (2 * q + 1) = (v q + 1) / 2 := by
  rw [v_eq (2 * q + 1)]
  have h1 : (2 * q + 1) / 2 = q := by omega
  have h2 : (2 * q + 1) % 2 = 1 := by omega
  rw [h1, h2]; simp

lemma v_bounds (j : ℕ) : 0 ≤ v j ∧ v j < 1 ∧ (1 ≤ j → 0 < v j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp [v_zero]
    · have hlt : j / 2 < j := Nat.div_lt_self hpos (by norm_num)
      obtain ⟨a0, a1, a2⟩ := ih (j / 2) hlt
      rw [v_eq j]
      have hr : j % 2 = 0 ∨ j % 2 = 1 := Nat.mod_two_eq_zero_or_one j
      rcases hr with hr | hr
      · rw [hr]
        have : 1 ≤ j / 2 := by omega
        have := a2 this
        refine ⟨by push_cast; linarith, by push_cast; linarith, fun _ => by push_cast; linarith⟩
      · rw [hr]
        refine ⟨by push_cast; linarith, by push_cast; linarith, fun _ => by push_cast; linarith⟩

lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  unfold additiveChar
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma norm_e (a : ℝ) : ‖e a‖ = 1 := by
  unfold additiveChar
  exact Complex.norm_exp_ofReal_mul_I _

lemma e_nat (m : ℕ) : e (m : ℝ) = 1 := by
  unfold additiveChar
  have : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this]
  exact Complex.exp_nat_mul_two_pi_mul_I m

lemma e_half : e (1 / 2) = -1 := by
  unfold additiveChar
  have : ((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I := by
    push_cast; ring
  rw [this]
  exact Complex.exp_pi_mul_I

lemma sum_range_double (f : ℕ → ℂ) (q : ℕ) :
    ∑ j ∈ range (2 * q), f j = ∑ i ∈ range q, (f (2 * i) + f (2 * i + 1)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

noncomputable def F (t : ℝ) (n : ℕ) : ℂ := ∑ j ∈ range n, e (t * v j)

lemma F_even (t : ℝ) (q : ℕ) : F t (2 * q) = (1 + e (t / 2)) * F (t / 2) q := by
  unfold F
  rw [sum_range_double, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [v_even, v_odd]
  have h1 : t * (v i / 2) = t / 2 * v i := by ring
  have h2 : t * ((v i + 1) / 2) = t / 2 + t / 2 * v i := by ring
  rw [h1, h2, e_add]
  ring

lemma bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) : ‖F k n‖ ≤ 2 * (k : ℝ) - 1 := by
  induction k using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ n = 2 * q + r :=
      ⟨n / 2, n % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 2).symm⟩
    have hstep : ‖F k (2 * q + r)‖ ≤ ‖F k (2 * q)‖ + 1 := by
      interval_cases r
      · simp
      · have : F k (2 * q + 1) = F k (2 * q) + e (k * v (2 * q)) := by
          unfold F; rw [sum_range_succ]
        rw [this]
        calc ‖F k (2 * q) + e (k * v (2 * q))‖ ≤ ‖F k (2 * q)‖ + ‖e (k * v (2 * q))‖ :=
              norm_add_le _ _
          _ = ‖F k (2 * q)‖ + 1 := by rw [norm_e]
    rw [F_even, norm_mul] at hstep
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hm : 1 ≤ m := by omega
      have hc : ((2 * m : ℕ) : ℝ) / 2 = ((m : ℕ) : ℝ) := by push_cast; ring
      rw [hc, e_nat] at hstep
      have h2 : ‖(1 : ℂ) + 1‖ = 2 := by norm_num
      rw [h2] at hstep
      have := ih m (by omega) hm q
      push_cast at this hstep ⊢
      nlinarith
    · have hc : ((2 * m + 1 : ℕ) : ℝ) / 2 = ((m : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
      rw [hc, e_add, e_nat, e_half] at hstep
      have h0 : ‖(1 : ℂ) + 1 * -1‖ = 0 := by norm_num
      rw [h0, zero_mul, zero_add] at hstep
      push_cast at hstep ⊢
      have : (0 : ℝ) ≤ m := by positivity
      linarith

lemma F_succ (t : ℝ) (n : ℕ) : F t (n + 1) = F t n + e (t * v n) := by
  unfold F; rw [sum_range_succ]

/-- Sharp bound: `‖F k n‖ ≤ 2^(v₂ k) ≤ k`. -/
lemma bound2 (k : ℕ) (hk : 1 ≤ k) (n : ℕ) : ‖F k n‖ ≤ (k : ℝ) := by
  induction k using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ n = 2 * q + r :=
      ⟨n / 2, n % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 2).symm⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hm : 1 ≤ m := by omega
      have hc : ((2 * m : ℕ) : ℝ) / 2 = ((m : ℕ) : ℝ) := by push_cast; ring
      have hev : F ((2 * m : ℕ) : ℝ) (2 * q) = 2 * F (m : ℝ) q := by
        rw [F_even, hc, e_nat]; ring
      have ih1 := ih m (by omega) hm q
      have ih2 := ih m (by omega) hm (q + 1)
      interval_cases r
      · rw [add_zero, hev, norm_mul]
        have : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [this]; push_cast; linarith
      · have hod : F ((2 * m : ℕ) : ℝ) (2 * q + 1) = F (m : ℝ) q + F (m : ℝ) (q + 1) := by
          rw [F_succ, hev, F_succ, v_even]
          have : ((2 * m : ℕ) : ℝ) * (v q / 2) = (m : ℝ) * v q := by push_cast; ring
          rw [this]; ring
        rw [hod]
        calc ‖F (m : ℝ) q + F (m : ℝ) (q + 1)‖ ≤ ‖F (m : ℝ) q‖ + ‖F (m : ℝ) (q + 1)‖ :=
              norm_add_le _ _
          _ ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
    · have hc : ((2 * m + 1 : ℕ) : ℝ) / 2 = ((m : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
      have hz : F ((2 * m + 1 : ℕ) : ℝ) (2 * q) = 0 := by
        rw [F_even, hc, e_add, e_nat, e_half]; ring
      have h1 : ‖F ((2 * m + 1 : ℕ) : ℝ) (2 * q + r)‖ ≤ 1 := by
        interval_cases r
        · rw [add_zero, hz]; simp
        · rw [F_succ, hz, zero_add, norm_e]
      have : (0 : ℝ) ≤ m := by positivity
      push_cast at h1 ⊢
      linarith

lemma e_zero : e 0 = 1 := by simpa using e_nat 0

end VDC

open VDC in
theorem erdos_987.variants.linear_upper_bound_clunie :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ (((k : ℝ) + 1) : EReal) := by
  refine ⟨fun j => v (j + 1), fun j => ?_, fun k hk => ?_⟩
  · obtain ⟨_, h1, h2⟩ := v_bounds (j + 1)
    exact ⟨h2 (by omega), h1⟩
  · unfold A
    refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall (fun n => ?_))
    have hs : ∑ j ∈ range n, e (k * v (j + 1)) = F k (n + 1) - 1 := by
      unfold F
      rw [sum_range_succ', v_zero, mul_zero, e_zero]; ring
    have hb := bound2 k hk (n + 1)
    have : ‖∑ j ∈ range n, e (k * v (j + 1))‖ ≤ (k : ℝ) + 1 := by
      rw [hs]
      calc ‖F k (n + 1) - 1‖ ≤ ‖F k (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ (k : ℝ) + 1 := by rw [norm_one]; linarith
    exact EReal.coe_le_coe_iff.mpr this

open VDC in
theorem erdos_987.variants.linear_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ico (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((k : ℝ) : EReal) := by
  refine ⟨v, fun j => ?_, fun k hk => ?_⟩
  · obtain ⟨h0, h1, _⟩ := v_bounds j
    exact ⟨h0, h1⟩
  · unfold A
    refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall (fun n => ?_))
    exact EReal.coe_le_coe_iff.mpr (bound2 k hk n)

open VDC in
theorem erdos_987.variants.linear_upper_bound_weak :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((2 * k : ℝ) : EReal) := by
  refine ⟨fun j => v (j + 1), fun j => ?_, fun k hk => ?_⟩
  · obtain ⟨_, h1, h2⟩ := v_bounds (j + 1)
    exact ⟨h2 (by omega), h1⟩
  · unfold A
    refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall (fun n => ?_))
    have hs : ∑ j ∈ range n, e (k * v (j + 1)) = F k (n + 1) - 1 := by
      unfold F
      rw [sum_range_succ', v_zero, mul_zero]
      have : e 0 = 1 := by simpa using e_nat 0
      rw [this]; ring
    have hb := bound k hk (n + 1)
    have : ‖∑ j ∈ range n, e (k * v (j + 1))‖ ≤ 2 * (k : ℝ) := by
      rw [hs]
      calc ‖F k (n + 1) - 1‖ ≤ ‖F k (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 * (k : ℝ) := by rw [norm_one]; linarith
    exact EReal.coe_le_coe_iff.mpr this

end Erdos987

#print axioms Erdos987.erdos_987.variants.linear_upper_bound_weak
#print axioms Erdos987.erdos_987.variants.linear_upper_bound_clunie
#print axioms Erdos987.erdos_987.variants.linear_upper_bound
