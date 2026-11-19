import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Finset

namespace Erdos856

/-- A finite set `A` of natural numbers contains `k` distinct elements with the same pairwise least
common multiple. -/
def HasEqualLcmTuple (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.card = k ∧ ∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- $f_k(N)$. -/
noncomputable def f (k N : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ¬ HasEqualLcmTuple k A ∧
    s = ∑ n ∈ A, (n : ℝ)⁻¹}

namespace QL

noncomputable def inv : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; exact mul_inv _ _

lemma inv_apply (n : ℕ) : inv n = (n : ℝ)⁻¹ := rfl

lemma harm (b : ℕ) :
    Real.log ((b : ℝ) + 1) ≤ ∑ x ∈ range b, (1 : ℝ) / ((x : ℝ) + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ]
    have key : Real.log ((b : ℝ) + 1 + 1) - Real.log ((b : ℝ) + 1) ≤ 1 / ((b : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) by positivity)
      have e : ((b : ℝ) + 1 + 1) / ((b : ℝ) + 1) - 1 = 1 / ((b : ℝ) + 1) := by
        field_simp
        ring
      linarith
    push_cast
    linarith

lemma harm_le_prod (N : ℕ) :
    ∑ m ∈ Ico 1 N, (m : ℝ)⁻¹ ≤ ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := inv) (fun {p} hp => by
      rw [inv_apply, norm_inv, Real.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) N).2
  have h2 := sum_le_hasSum ((Ico 1 N).subtype (· ∈ N.smoothNumbers))
    (fun i _ => by rw [inv_apply]; positivity) h
  rw [Finset.sum_subtype_eq_sum_filter] at h2
  have hf : (Ico 1 N).filter (· ∈ N.smoothNumbers) = Ico 1 N := by
    apply filter_true_of_mem
    intro m hm
    rw [mem_Ico] at hm
    exact Nat.mem_smoothNumbers_of_lt (by omega) hm.2
  rw [hf] at h2
  simpa [inv_apply] using h2

lemma factor_le (p : ℕ) (hp : 2 ≤ p) : (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (1 / (p : ℝ))) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have e : (1 - (p : ℝ)⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
    have hpne : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    have e2 : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
    rw [e2, inv_div, div_add_one hp1]
    congr 1; ring
  rw [e]
  refine le_trans (Real.add_one_le_exp _) (Real.exp_le_exp.mpr ?_)
  rw [div_le_iff₀ (by linarith), mul_one_div, mul_comm, ← mul_div_assoc, le_div_iff₀ (by linarith)]
  linarith

/-- MERTENS-TYPE LOWER BOUND: `log log N ≤ 2 Σ_{p<N} 1/p`. -/
lemma loglog_le (N : ℕ) (hN : 2 ≤ N) :
    Real.log (Real.log N) ≤ 2 * ∑ p ∈ (range N).filter Nat.Prime, (1 : ℝ) / p := by
  have h1 : Real.log N ≤ ∑ m ∈ Ico 1 N, (m : ℝ)⁻¹ := by
    have := harm (N - 1)
    have e1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1] at this
    refine this.trans (le_of_eq ?_)
    rw [range_eq_Ico]
    have := sum_Ico_add' (fun m : ℕ => (m : ℝ)⁻¹) 0 (N - 1) 1
    rw [show N - 1 + 1 = N by omega, zero_add] at this
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    push_cast; rw [one_div]
  have h3 : ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ ≤
      ∏ p ∈ N.primesBelow, Real.exp (2 * (1 / (p : ℝ))) := by
    apply Finset.prod_le_prod
    · intro p hp
      have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt)
      have : 0 < 1 - (p : ℝ)⁻¹ := by linarith
      positivity
    · intro p hp
      exact factor_le p (Nat.prime_of_mem_primesBelow hp).two_le
  rw [← Real.exp_sum, ← mul_sum] at h3
  have h4 := h1.trans ((harm_le_prod N).trans h3)
  have hpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have := Real.log_le_log hpos h4
  rw [Real.log_exp] at this
  simpa [Nat.primesBelow] using this

end QL

namespace UL

/-- `L/q` and `L/r` for distinct primes `q, r` have lcm `L`. -/
lemma lcm_eq {a b q r L : ℕ} (hq : q.Prime) (hr : r.Prime) (ha : a * q = L) (hb : b * r = L)
    (hab : a ≠ b) : Nat.lcm a b = L := by
  have hqr : q ≠ r := by
    rintro rfl
    exact hab (Nat.eq_of_mul_eq_mul_right hq.pos (ha.trans hb.symm))
  have hra : r ∣ a := by
    have : r ∣ a * q := ⟨b, by rw [ha, ← hb, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hr).mp this with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hq).mp h).symm hqr
  obtain ⟨c, rfl⟩ := hra
  have hbc : b = c * q := by
    apply Nat.eq_of_mul_eq_mul_right hr.pos
    rw [hb, ← ha]; ring
  subst hbc
  rw [show r * c = c * r by ring, Nat.lcm_mul_left,
    Nat.Coprime.lcm_eq_mul ((Nat.coprime_primes hr hq).mpr hqr.symm), ← ha]
  ring

lemma fiber_card {k : ℕ} {A : Finset ℕ} (hfree : ¬ HasEqualLcmTuple k A) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ) (hA0 : ∀ a ∈ A, 0 < a) :
    ((A ×ˢ P).filter (fun x => x.1 * x.2 = L)).card < k := by
  by_contra hcon
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (not_lt.mp hcon)
  have hinj : Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx' := mem_filter.mp (hT hx)
    have hy' := mem_filter.mp (hT hy)
    have hpos := hA0 _ (mem_product.mp hx'.1).1
    have h2 : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [hx'.2]
      rw [hxy, hy'.2]
    exact Prod.ext hxy h2
  apply hfree
  refine ⟨T.image Prod.fst, ?_, by rw [card_image_of_injOn hinj, hTc], L, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    exact (mem_product.mp (mem_filter.mp (hT hx)).1).1
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    have hx' := mem_filter.mp (hT hx)
    have hy' := mem_filter.mp (hT hy)
    exact lcm_eq (hP _ (mem_product.mp hx'.1).2) (hP _ (mem_product.mp hy'.1).2) hx'.2 hy'.2 hab

lemma core {k N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hfree : ¬ HasEqualLcmTuple k A) :
    (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ (range N).filter Nat.Prime, (1 : ℝ) / p) ≤
      ((k : ℝ) - 1) * ∑ L ∈ Icc 1 (N * N), (L : ℝ)⁻¹ := by
  set P := (range N).filter Nat.Prime with hPdef
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hA0 : ∀ a ∈ A, 0 < a := fun a ha => (mem_Icc.mp (hA ha)).1
  have e0 : (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ P, (1 : ℝ) / p) =
      ∑ x ∈ A ×ˢ P, (x.1 : ℝ)⁻¹ * (1 / (x.2 : ℝ)) := by
    rw [sum_product, sum_mul_sum]
  have hmaps : ∀ x ∈ A ×ˢ P, x.1 * x.2 ∈ Icc 1 (N * N) := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx
    have ha := mem_Icc.mp (hA h1)
    have hp := hP _ h2
    have hpN : x.2 < N := mem_range.mp (mem_filter.mp h2).1
    rw [mem_Icc]
    constructor
    · exact Nat.mul_pos ha.1 hp.pos
    · exact Nat.mul_le_mul ha.2 hpN.le
  rw [e0, ← sum_fiberwise_of_maps_to hmaps, mul_sum]
  apply sum_le_sum
  intro L _
  have e : ∀ x ∈ (A ×ˢ P).filter (fun x => x.1 * x.2 = L),
      (x.1 : ℝ)⁻¹ * (1 / (x.2 : ℝ)) = (L : ℝ)⁻¹ := by
    intro x hx
    rw [← (mem_filter.mp hx).2, Nat.cast_mul, mul_inv, one_div]
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul]
  have hc := fiber_card hfree P hP L hA0
  have hc' : (((A ×ˢ P).filter (fun x => x.1 * x.2 = L)).card : ℝ) ≤ (k : ℝ) - 1 := by
    have h0 : ((A ×ˢ P).filter (fun x => x.1 * x.2 = L)).card + 1 ≤ k := hc
    have h' : ((((A ×ˢ P).filter (fun x => x.1 * x.2 = L)).card + 1 : ℕ) : ℝ) ≤ k := by
      exact_mod_cast h0
    push_cast at h'
    linarith
  exact mul_le_mul_of_nonneg_right hc' (by positivity)

lemma harm_up (M : ℕ) : ∑ L ∈ Icc 1 (M + 1), (L : ℝ)⁻¹ ≤ 1 + Real.log ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega)]
    have key : ((M + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((M : ℝ) + 1 + 1) - Real.log ((M : ℝ) + 1) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < ((M : ℝ) + 1) / ((M : ℝ) + 1 + 1) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have e : ((M : ℝ) + 1) / ((M : ℝ) + 1 + 1) - 1 = -((M + 1 + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      linarith
    push_cast at ih key ⊢
    linarith

lemma harm_up' (M : ℕ) (hM : 1 ≤ M) : ∑ L ∈ Icc 1 M, (L : ℝ)⁻¹ ≤ 1 + Real.log M := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have := harm_up M'
  push_cast
  exact this

lemma fin_ineq (X S l B c : ℝ) (hX : 0 ≤ X) (h1 : X * S ≤ c * (3 * B)) (h2 : l ≤ 2 * S)
    (hl : 0 < l) : X ≤ 6 * c * (B / l) := by
  rw [← mul_div_assoc, le_div_iff₀ hl]
  have := mul_le_mul_of_nonneg_left h2 hX
  linarith

end UL

theorem erdos_856.variants.erdos_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, f k N ≤ C * (Real.log N / Real.log (Real.log N)) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨6 * ((k : ℝ) - 1), by linarith, ?_⟩
  rw [eventually_atTop]
  refine ⟨3, fun N hN => ?_⟩
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : 0 < Real.log (Real.log N) := Real.log_pos hlog1
  have hH : ∑ L ∈ Icc 1 (N * N), (L : ℝ)⁻¹ ≤ 3 * Real.log N := by
    have hpos : 0 < N * N := Nat.mul_pos (by omega) (by omega)
    have h := UL.harm_up' (N * N) hpos
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
    rw [Nat.cast_mul, Real.log_mul hN0 hN0] at h
    linarith
  have hS := QL.loglog_le N (by omega)
  apply csSup_le
  · refine ⟨_, ∅, empty_subset _, ?_, rfl⟩
    rintro ⟨S, hS, hc, _⟩
    rw [subset_empty.mp hS, card_empty] at hc
    omega
  · rintro s ⟨A, hA, hfree, rfl⟩
    have hc := UL.core hA hfree
    have hX : 0 ≤ ∑ a ∈ A, (a : ℝ)⁻¹ := sum_nonneg fun a _ => by positivity
    have h1 := hc.trans (mul_le_mul_of_nonneg_left hH (by linarith))
    exact UL.fin_ineq _ _ _ _ _ hX h1 hS hll

end Erdos856

#print axioms Erdos856.erdos_856.variants.erdos_upper
