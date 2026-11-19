import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

/-- Restated from FormalConjecturesForMathlib/Analysis/SpecialFunctions/AdditiveCharacter.lean. -/
noncomputable def additiveChar (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[inherit_doc]
scoped[ExponentialSum] notation "e" => additiveChar

open scoped ExponentialSum

namespace Erdos987

/-- Restated from FormalConjectures/ErdosProblems/987.lean. -/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

namespace SL

lemma e_zero : e 0 = 1 := by
  unfold additiveChar; simp

lemma norm_e (a : ℝ) : ‖e a‖ = 1 := by
  unfold additiveChar
  exact Complex.norm_exp_ofReal_mul_I _

lemma e_mul_conj (a b : ℝ) : e a * starRingEnd ℂ (e b) = e (a - b) := by
  unfold additiveChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma e_conj (a : ℝ) : starRingEnd ℂ (e a) = e (-a) := by
  simpa [e_zero] using e_mul_conj 0 a

lemma sq_sum {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    ((‖∑ i ∈ s, w i‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ s, ∑ i' ∈ s, w i * starRingEnd ℂ (w i') := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]

/-- Exponential sum with integer frequency. -/
noncomputable def T (t : ℕ → ℝ) (n : ℕ) (d : ℤ) : ℂ := ∑ j ∈ range n, e (d * t j)

lemma norm_T_le (t : ℕ → ℝ) (n : ℕ) (d : ℤ) : ‖T t n d‖ ≤ n := by
  unfold T
  calc ‖∑ j ∈ range n, e (d * t j)‖ ≤ ∑ j ∈ range n, ‖e (d * t j)‖ := norm_sum_le _ _
    _ = n := by simp [norm_e]

lemma norm_T_neg (t : ℕ → ℝ) (n : ℕ) (d : ℤ) : ‖T t n (-d)‖ = ‖T t n d‖ := by
  have : T t n (-d) = starRingEnd ℂ (T t n d) := by
    unfold T
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e_conj]
    congr 1
    push_cast
    ring
  rw [this, Complex.norm_conj]

lemma ident (t : ℕ → ℝ) (n N : ℕ) :
    ∑ m ∈ range N, ∑ m' ∈ range N, ‖T t n ((m : ℤ) - m')‖ ^ 2
      = ∑ j ∈ range n, ∑ l ∈ range n, ‖∑ m ∈ range N, e (m * (t j - t l))‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, sq_sum, T, e_mul_conj]
  calc _ = ∑ p ∈ range N ×ˢ range N, ∑ q ∈ range n ×ˢ range n,
        e (((p.1 : ℝ) - p.2) * (t q.1 - t q.2)) := by
          simp only [Finset.sum_product]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          congr 1
          push_cast
          ring
    _ = ∑ q ∈ range n ×ˢ range n, ∑ p ∈ range N ×ˢ range N,
        e (((p.1 : ℝ) - p.2) * (t q.1 - t q.2)) := Finset.sum_comm
    _ = _ := by
          simp only [Finset.sum_product]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
            Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
          congr 1
          ring

/-- Version of `core` that only needs the bound for frequencies `0 < k < n²`. -/
lemma core' (t : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (B : ℝ)
    (hB : ∀ k : ℕ, 0 < k → k < n * n → ‖T t n k‖ ≤ B) : (n : ℝ) ≤ 1 + B ^ 2 := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = n * n := ⟨_, rfl⟩
  rw [← hNdef] at hB
  have hid := ident t n N
  have h2 : (n : ℝ) * (N : ℝ) ^ 2 ≤
      ∑ j ∈ range n, ∑ l ∈ range n, ‖∑ m ∈ range N, e (m * (t j - t l))‖ ^ 2 := by
    calc (n : ℝ) * (N : ℝ) ^ 2 = ∑ j ∈ range n, ‖∑ m ∈ range N, e (m * (t j - t j))‖ ^ 2 := by
          simp [e_zero]
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
          Finset.single_le_sum (f := fun l => ‖∑ m ∈ range N, e (m * (t j - t l))‖ ^ 2)
            (fun _ _ => by positivity) hj
  have h3 : ∑ m ∈ range N, ∑ m' ∈ range N, ‖T t n ((m : ℤ) - m')‖ ^ 2 ≤
      ∑ m ∈ range N, ∑ m' ∈ range N, ((if m = m' then (n : ℝ) ^ 2 else 0) + B ^ 2) := by
    refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => ?_
    have hmN : m < N := Finset.mem_range.1 hm
    have hm'N : m' < N := Finset.mem_range.1 hm'
    by_cases h : m = m'
    · subst h
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_T_le t n ((m : ℤ) - m)) 2
      simp only [if_true]
      nlinarith [sq_nonneg B]
    · have hb : ‖T t n ((m : ℤ) - m')‖ ≤ B := by
        rcases lt_or_gt_of_ne h with hlt | hlt
        · have he : ((m : ℤ) - m') = -((m' - m : ℕ) : ℤ) := by
            rw [Nat.cast_sub hlt.le]; ring
          rw [he, norm_T_neg]
          exact hB _ (by omega) (by omega)
        · have he : ((m : ℤ) - m') = ((m - m' : ℕ) : ℤ) := by
            rw [Nat.cast_sub hlt.le]
          rw [he]
          exact hB _ (by omega) (by omega)
      have := pow_le_pow_left₀ (norm_nonneg _) hb 2
      simp only [h, if_false]
      linarith
  have h4 : ∑ m ∈ range N, ∑ m' ∈ range N, ((if m = m' then (n : ℝ) ^ 2 else 0) + B ^ 2)
      = (N : ℝ) * n ^ 2 + (N : ℝ) ^ 2 * B ^ 2 := by
    have hrow : ∀ m ∈ range N, (∑ m' ∈ range N, ((if m = m' then (n : ℝ) ^ 2 else 0) + B ^ 2))
        = (n : ℝ) ^ 2 + N * B ^ 2 := by
      intro m hm
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hm]
      simp
    rw [Finset.sum_congr rfl hrow]
    simp
    ring
  have hN : (N : ℝ) = (n : ℝ) ^ 2 := by rw [hNdef]; push_cast; ring
  have hfin : (n : ℝ) * (N : ℝ) ^ 2 ≤ (N : ℝ) * n ^ 2 + (N : ℝ) ^ 2 * B ^ 2 := by
    linarith
  rw [hN] at hfin
  have hp : 0 < (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have : (n : ℝ) ^ 4 * n ≤ (n : ℝ) ^ 4 * (1 + B ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left this hp

end SL

theorem erdos_987.variants.log_lower_bound
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ᶠ k : ℕ in atTop, ((c * Real.log k : ℝ) : EReal) ≤ A x k := by
  refine ⟨1, one_pos, ?_⟩
  rw [Filter.frequently_atTop]
  intro K0
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK⟩ : ∃ K, K = K0 + 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = ⌈Real.log (K : ℝ)⌉₊ + 19 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = s ^ 4 := ⟨_, rfl⟩
  have hev : ∀ m ∈ Finset.Ico 1 (L * L), ∀ᶠ n in atTop,
      ‖∑ j ∈ range n, e (((K * m : ℕ) : ℝ) * x j)‖ < Real.log ((K * m : ℕ) : ℝ) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.1 hm).1
    have hKm : K0 ≤ K * m :=
      calc K0 ≤ K := by omega
        _ ≤ K * m := Nat.le_mul_of_pos_right K hm1
    have h1 := hcon (K * m) hKm
    unfold A at h1
    have h2 := Filter.eventually_lt_of_limsup_lt h1
    filter_upwards [h2] with n hn
    have := EReal.coe_lt_coe_iff.1 hn
    linarith
  have hev' := (Filter.eventually_all_finset _).2 hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev'
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.one_le_pow _ _ (by omega)
  let t : ℕ → ℝ := fun j => (K : ℝ) * x (N + j)
  have hT : ∀ k : ℕ, 0 < k → k < L * L →
      ‖SL.T t L k‖ ≤ 2 * Real.log ((K * (L * L) : ℕ) : ℝ) := by
    intro k hk0 hkL
    have hmem : k ∈ Finset.Ico 1 (L * L) := Finset.mem_Ico.2 ⟨hk0, hkL⟩
    have hA := hN N le_rfl k hmem
    have hA' := hN (N + L) (by omega) k hmem
    have hsplit : SL.T t L k = ∑ j ∈ range (N + L), e (((K * k : ℕ) : ℝ) * x j)
        - ∑ j ∈ range N, e (((K * k : ℕ) : ℝ) * x j) := by
      rw [Finset.sum_range_add, add_sub_cancel_left]
      unfold SL.T
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [t]
      push_cast
      ring
    have hpos : (0 : ℝ) < ((K * k : ℕ) : ℝ) := by
      have : 0 < K * k := Nat.mul_pos (by omega) hk0
      exact_mod_cast this
    have hlog : Real.log ((K * k : ℕ) : ℝ) ≤ Real.log ((K * (L * L) : ℕ) : ℝ) :=
      Real.log_le_log hpos (Nat.cast_le.2 (Nat.mul_le_mul le_rfl hkL.le))
    rw [hsplit]
    calc _ ≤ ‖∑ j ∈ range (N + L), e (((K * k : ℕ) : ℝ) * x j)‖
          + ‖∑ j ∈ range N, e (((K * k : ℕ) : ℝ) * x j)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hcore := SL.core' t L hL1 _ hT
  -- arithmetic contradiction
  have hs19 : (19 : ℝ) ≤ s := by
    have : 19 ≤ s := by omega
    exact_mod_cast this
  have hspos : (0 : ℝ) < s := by linarith
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 (by omega)
  have hlogK : Real.log (K : ℝ) ≤ s := by
    refine (Nat.le_ceil _).trans ?_
    have : ⌈Real.log (K : ℝ)⌉₊ ≤ s := by omega
    exact_mod_cast this
  have hlogs : Real.log s ≤ s := by
    have := Real.log_le_sub_one_of_pos hspos
    linarith
  have hlogeq : Real.log ((K * (L * L) : ℕ) : ℝ) = Real.log K + 8 * Real.log s := by
    rw [hL]
    push_cast
    have h4 : ((s : ℝ) ^ 4) ≠ 0 := (pow_pos hspos 4).ne'
    rw [Real.log_mul hKpos.ne' (mul_ne_zero h4 h4), Real.log_mul h4 h4, Real.log_pow]
    push_cast
    ring
  have hy0 : 0 ≤ Real.log ((K * (L * L) : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ K * (L * L) := Nat.mul_pos (by omega) (Nat.mul_pos hL1 hL1)
    exact_mod_cast this
  have hy9 : Real.log ((K * (L * L) : ℕ) : ℝ) ≤ 9 * s := by
    rw [hlogeq]; linarith
  have hLr : (L : ℝ) = (s : ℝ) ^ 4 := by rw [hL]; push_cast; ring
  rw [hLr] at hcore
  set y := Real.log ((K * (L * L) : ℕ) : ℝ)
  have h1 : y ^ 2 ≤ 81 * (s : ℝ) ^ 2 := by nlinarith
  have hs2 : (361 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have h2 : 361 * (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 4 := by nlinarith
  nlinarith

theorem erdos_987.parts.i :
    ∀ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      atTop.limsup (fun k : ℕ => A x k) = ⊤ := by
  intro x hx
  obtain ⟨c, hc, hfr⟩ := erdos_987.variants.log_lower_bound x hx
  refine (EReal.eq_top_iff_forall_lt _).2 fun b => ?_
  have hev : ∀ᶠ k : ℕ in atTop, b + 1 ≤ c * Real.log k := by
    have : Tendsto (fun k : ℕ => c * Real.log k) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact this.eventually_ge_atTop _
  have hfr2 : ∃ᶠ k : ℕ in atTop, ((b + 1 : ℝ) : EReal) ≤ A x k := by
    refine (hfr.and_eventually hev).mono fun k hk => ?_
    exact (EReal.coe_le_coe_iff.2 hk.2).trans hk.1
  have := Filter.le_limsup_of_frequently_le hfr2 (by isBoundedDefault)
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) this

end Erdos987

#print axioms Erdos987.erdos_987.variants.log_lower_bound
#print axioms Erdos987.erdos_987.parts.i
