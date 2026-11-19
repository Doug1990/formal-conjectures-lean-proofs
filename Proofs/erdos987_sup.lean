import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.LiminfLimsup
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

lemma core (t : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (B : ℝ)
    (hB : ∀ d : ℤ, d ≠ 0 → ‖T t n d‖ ≤ B) : (n : ℝ) ≤ 1 + B ^ 2 := by
  set N := n * n with hNdef
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
    refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun m' _ => ?_
    by_cases h : m = m'
    · subst h
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_T_le t n ((m : ℤ) - m)) 2
      simp only [if_true]
      nlinarith [sq_nonneg B]
    · have hd : ((m : ℤ) - m') ≠ 0 := by omega
      have := pow_le_pow_left₀ (norm_nonneg _) (hB _ hd) 2
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

theorem erdos_987.variants.sup_limsup_infty
    (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    atTop.limsup (fun k : ℕ =>
      ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) = ⊤ := by
  by_contra hne
  obtain ⟨B, hB⟩ : ∃ B : ℝ, atTop.limsup (fun k : ℕ =>
      ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) < (B : EReal) := by
    have := mt (EReal.eq_top_iff_forall_lt _).2 hne
    simp only [not_forall, not_lt] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y + 1, lt_of_le_of_lt hy (EReal.coe_lt_coe_iff.2 (by linarith))⟩
  have hev := Filter.eventually_lt_of_limsup_lt hB
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  have hbound : ∀ k ≥ K, ∀ n : ℕ, ‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ ≤ B := by
    intro k hk n
    have h1 := hK k hk
    have h2 : ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal) ≤
        ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal) :=
      le_iSup (fun n : ℕ => ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) n
    exact EReal.coe_le_coe_iff.1 (h2.trans h1.le)
  set K' := K + 1 with hK'
  let t : ℕ → ℝ := fun j => (K' : ℝ) * x j
  have hpos : ∀ n : ℕ, ∀ k : ℕ, k ≠ 0 → ‖SL.T t n k‖ ≤ B := by
    intro n k hk
    have e1 : SL.T t n k = ∑ j ∈ range n, e (((k * K' : ℕ) : ℝ) * x j) := by
      unfold SL.T
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [t]
      push_cast
      ring
    rw [e1]
    apply hbound
    have : K' ≤ k * K' := Nat.le_mul_of_pos_left K' (by omega)
    omega
  have hT : ∀ n : ℕ, ∀ d : ℤ, d ≠ 0 → ‖SL.T t n d‖ ≤ B := by
    intro n d hd
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact hpos n k (by rintro rfl; exact hd rfl)
    · rw [SL.norm_T_neg]
      exact hpos n k (by rintro rfl; exact hd (by simp))
  set n := ⌈B ^ 2⌉₊ + 2 with hn
  have := SL.core t n (by omega) B (hT n)
  have hc := Nat.le_ceil (B ^ 2)
  have : (n : ℝ) = (⌈B ^ 2⌉₊ : ℝ) + 2 := by rw [hn]; push_cast; ring
  linarith

end Erdos987

#print axioms Erdos987.erdos_987.variants.sup_limsup_infty
