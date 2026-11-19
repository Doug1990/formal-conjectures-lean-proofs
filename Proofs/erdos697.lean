import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

/-! Definitions restated from FormalConjecturesForMathlib/Data/Set/Density.lean -/
namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

open Filter Set Real
open scoped Topology

namespace Erdos697

namespace P

open Classical

lemma ncard_Iio' (N : ℕ) : (Set.Iio N).ncard = N := by
  rw [show Set.Iio N = ((Finset.range N : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

lemma cnt_succ (S : Set ℕ) (N : ℕ) :
    (S ∩ Set.Iio (N+1)).ncard = (S ∩ Set.Iio N).ncard + if N ∈ S then 1 else 0 := by
  have hfin : (S ∩ Set.Iio N).Finite := (Set.finite_Iio N).subset Set.inter_subset_right
  by_cases h : N ∈ S
  · have e : S ∩ Set.Iio (N+1) = insert N (S ∩ Set.Iio N) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_insert_iff]
      constructor
      · rintro ⟨hx, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
        · exact Or.inr ⟨hx, h'⟩
        · exact Or.inl h'
      · rintro (rfl | ⟨hx, hlt⟩)
        · exact ⟨h, Nat.lt_succ_self _⟩
        · exact ⟨hx, by omega⟩
    rw [e, Set.ncard_insert_of_notMem (by simp) hfin, if_pos h]
  · have e : S ∩ Set.Iio (N+1) = S ∩ Set.Iio N := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio]
      constructor
      · rintro ⟨hx, hlt⟩
        refine ⟨hx, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
        · exact h'
        · exact absurd (h' ▸ hx) h
      · rintro ⟨hx, hlt⟩
        exact ⟨hx, by omega⟩
    rw [e, if_neg h, add_zero]

lemma cnt_le (S : Set ℕ) (N : ℕ) : (S ∩ Set.Iio N).ncard ≤ N := by
  calc (S ∩ Set.Iio N).ncard ≤ (Set.Iio N).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio N)
    _ = N := ncard_Iio' N

/-- Generic: a quadratic error bound gives a density. -/
lemma dens_of_sq (S : Set ℕ) (α K : ℝ) (_hK : 0 ≤ K)
    (h : ∀ N : ℕ, 1 ≤ N → (((S ∩ Set.Iio N).ncard : ℝ) - α * N) ^ 2 ≤ K * N) :
    S.HasDensity α := by
  unfold Set.HasDensity Set.partialDensity
  simp only [Set.inter_univ, Set.univ_inter, ncard_Iio']
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (K / ε ^ 2)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0:ℝ) < N := by linarith
  have hb := h N (by omega)
  have hNK : K < ε ^ 2 * N := by
    have h1 : (N0:ℝ) < N := by exact_mod_cast (show N0 < N by omega)
    have h2 : K / ε ^ 2 < N := by linarith
    rw [div_lt_iff₀ (by positivity)] at h2
    linarith
  rw [Real.dist_eq]
  set c : ℝ := ((S ∩ Set.Iio N).ncard : ℝ)
  have hx : (c / N - α) * N = c - α * N := by
    rw [sub_mul, div_mul_cancel₀ _ hNpos.ne']
  have hsq : ((c / N - α) * N) ^ 2 < (ε * N) ^ 2 := by
    rw [hx]
    nlinarith
  have habs := abs_lt_of_sq_lt_sq hsq (by positivity)
  rw [abs_mul, abs_of_pos hNpos] at habs
  exact lt_of_mul_lt_mul_right habs hNpos.le

/-- Periodic sets: shifting the window by one period adds one period's count. -/
lemma per_step (S : Set ℕ) (L : ℕ) (hS : ∀ n, n ∈ S ↔ n + L ∈ S) (N : ℕ) :
    (S ∩ Set.Iio (N + L)).ncard = (S ∩ Set.Iio N).ncard + (S ∩ Set.Iio L).ncard := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show N + 1 + L = (N + L) + 1 by ring, cnt_succ, cnt_succ, ih]
    by_cases h : N ∈ S
    · rw [if_pos h, if_pos ((hS N).mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h ((hS N).mpr h'))]; ring

lemma per_mul (S : Set ℕ) (L : ℕ) (hS : ∀ n, n ∈ S ↔ n + L ∈ S) (q r : ℕ) :
    (S ∩ Set.Iio (q * L + r)).ncard = q * (S ∩ Set.Iio L).ncard + (S ∩ Set.Iio r).ncard := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * L + r = (q * L + r) + L by ring, per_step S L hS, ih]
    ring

/-- A periodic set has a density. -/
lemma per_dens (S : Set ℕ) (L : ℕ) (hL : 0 < L) (hS : ∀ n, n ∈ S ↔ n + L ∈ S) :
    S.HasDensity (((S ∩ Set.Iio L).ncard : ℝ) / L) := by
  apply dens_of_sq S _ ((L : ℝ) ^ 2) (by positivity)
  intro N hN
  have hdec : N = (N / L) * L + N % L := by
    rw [mul_comm]; exact (Nat.div_add_mod N L).symm
  have hr : N % L < L := Nat.mod_lt N hL
  have hc : (S ∩ Set.Iio L).ncard ≤ L := cnt_le S L
  have he : (S ∩ Set.Iio (N % L)).ncard ≤ N % L := cnt_le S _
  have hcnt := per_mul S L hS (N / L) (N % L)
  rw [← hdec] at hcnt
  rw [hcnt]
  generalize (S ∩ Set.Iio L).ncard = c at hc ⊢
  generalize (S ∩ Set.Iio (N % L)).ncard = e at he ⊢
  have hNr : (N : ℝ) = ((N / L : ℕ) : ℝ) * L + ((N % L : ℕ) : ℝ) := by
    exact_mod_cast hdec
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  push_cast
  have hD : ((N / L : ℕ) : ℝ) * c + e - c / L * N = e - c * ((N % L : ℕ) : ℝ) / L := by
    rw [hNr]; field_simp; ring
  rw [hD]
  have hrR : ((N % L : ℕ) : ℝ) < L := by exact_mod_cast hr
  have hcR : (c : ℝ) ≤ L := by exact_mod_cast hc
  have heR : (e : ℝ) ≤ ((N % L : ℕ) : ℝ) := by exact_mod_cast he
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  generalize ((N % L : ℕ) : ℝ) = r at hrR heR
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hr0 : (0 : ℝ) ≤ r := le_trans he0 heR
  have ht0 : 0 ≤ (c : ℝ) * r / L := by positivity
  have ht1 : (c : ℝ) * r / L ≤ r := by
    rw [div_le_iff₀ hLpos, mul_comm (r : ℝ)]
    exact mul_le_mul_of_nonneg_right hcR hr0
  have hx1 : -(L : ℝ) ≤ (e : ℝ) - c * r / L := by linarith
  have hx2 : (e : ℝ) - c * r / L ≤ L := by linarith
  have h1 : ((e : ℝ) - c * r / L) ^ 2 ≤ (L : ℝ) ^ 2 := sq_le_sq' hx1 hx2
  exact h1.trans (le_mul_of_one_le_right (by positivity) hN1)

end P

theorem density_exists (m : ℕ) (α : ℝ) : ∃ δ, HasDensity
    {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp (m ^ α)) ∧ d ∣ n} δ := by
  set L := (⌈exp ((m : ℝ) ^ α)⌉₊).factorial
  refine ⟨_, P.per_dens _ L (Nat.factorial_pos _) ?_⟩
  intro n
  have hdL : ∀ d : ℕ, (d : ℝ) ∈ Set.Ioo 1 (exp ((m : ℝ) ^ α)) → d ∣ L := by
    intro d hd
    apply Nat.dvd_factorial
    · have : (1 : ℝ) < d := hd.1
      exact_mod_cast (show (0:ℝ) < d by linarith)
    · exact_mod_cast hd.2.le.trans (Nat.le_ceil _)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h1, h2, dvd_add h3 (hdL d h2)⟩
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h1, h2, (Nat.dvd_add_left (hdL d h2)).mp h3⟩

noncomputable def δ (m : ℕ) (α : ℝ) : ℝ := (density_exists m α).choose

namespace Q

open Classical

/-- The set, with a general exponent `β` in place of `m ^ α`. -/
def T (m : ℕ) (β : ℝ) : Set ℕ :=
  {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp β) ∧ d ∣ n}

lemma dvdL (β : ℝ) (d : ℕ) (hd : (d : ℝ) ∈ Set.Ioo 1 (exp β)) :
    d ∣ (⌈exp β⌉₊).factorial := by
  apply Nat.dvd_factorial
  · have : (1 : ℝ) < d := hd.1
    exact_mod_cast (show (0:ℝ) < d by linarith)
  · exact_mod_cast hd.2.le.trans (Nat.le_ceil _)

lemma per (m : ℕ) (β : ℝ) (n : ℕ) :
    n ∈ T m β ↔ n + (⌈exp β⌉₊).factorial ∈ T m β := by
  simp only [T, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h1, h2, dvd_add h3 (dvdL β d h2)⟩
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h1, h2, (Nat.dvd_add_left (dvdL β d h2)).mp h3⟩

lemma bound (m : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hm : 0 < m) (L : ℕ) (hL0 : 0 < L)
    (hL : ∀ d : ℕ, (d : ℝ) ∈ Set.Ioo 1 (exp β) → d ∣ L) :
    ((T m β ∩ Set.Iio L).ncard : ℝ) / L < (β + 1) / m := by
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL0
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < (β + 1) / m := by positivity
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ, ∀ d, d ∈ D ↔ d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp β) := by
    refine ⟨(Finset.Icc 2 ⌈exp β⌉₊).filter (fun d => d ≡ 1 [MOD m] ∧ (d : ℝ) < exp β), ?_⟩
    intro d
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h2, _⟩, h1, h3⟩
      exact ⟨h1, by exact_mod_cast (show 1 < d by omega), h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨?_, ?_⟩, h1, h3⟩
      · have : 1 < d := by exact_mod_cast h2
        omega
      · exact_mod_cast h3.le.trans (Nat.le_ceil _)
  have hsub : T m β ∩ Set.Iio L ⊆
      ↑(D.biUnion (fun d => (Finset.range (L / d)).image (· * d))) := by
    rintro n ⟨⟨d, h1, h2, ⟨j, rfl⟩⟩, hn⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image,
      Finset.mem_range]
    refine ⟨d, (hD d).mpr ⟨h1, h2⟩, j, ?_, by ring⟩
    have hdL := hL d h2
    rw [Set.mem_Iio] at hn
    have : d * j < d * (L / d) := by rw [Nat.mul_div_cancel' hdL]; exact hn
    exact Nat.lt_of_mul_lt_mul_left this
  have hcard : ((T m β ∩ Set.Iio L).ncard : ℝ) ≤ ∑ d ∈ D, (L : ℝ) / d := by
    have h1 : (T m β ∩ Set.Iio L).ncard ≤
        (D.biUnion (fun d => (Finset.range (L / d)).image (· * d))).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have h2 := Finset.card_biUnion_le (s := D) (t := fun d => (Finset.range (L / d)).image (· * d))
    have h3 : ∀ d ∈ D, ((Finset.range (L / d)).image (· * d)).card ≤ L / d :=
      fun d _ => Finset.card_image_le.trans (Finset.card_range _).le
    have h4 : (T m β ∩ Set.Iio L).ncard ≤ ∑ d ∈ D, L / d :=
      h1.trans (h2.trans (Finset.sum_le_sum h3))
    calc ((T m β ∩ Set.Iio L).ncard : ℝ) ≤ ((∑ d ∈ D, L / d : ℕ) : ℝ) := by exact_mod_cast h4
      _ = ∑ d ∈ D, ((L / d : ℕ) : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ d ∈ D, (L : ℝ) / d := Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
  have hdiv : ((T m β ∩ Set.Iio L).ncard : ℝ) / L ≤ ∑ d ∈ D, 1 / (d : ℝ) := by
    rw [div_le_iff₀ hLpos, Finset.sum_mul]
    refine hcard.trans (le_of_eq (Finset.sum_congr rfl fun d _ => ?_))
    rw [div_eq_mul_one_div, mul_comm]
  by_cases hne : D.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hdiv
    linarith
  have hd1 : ∀ d ∈ D, 1 < d := by
    intro d hd
    have := ((hD d).mp hd).2.1
    exact_mod_cast this
  have hlt : ∑ d ∈ D, 1 / (d : ℝ) < ∑ d ∈ D, 1 / ((d : ℝ) - 1) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro d hd
    have : (1 : ℝ) < d := by exact_mod_cast hd1 d hd
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  -- reindex by k = (d - 1) / m
  have hg : ∀ d ∈ D, m * ((d - 1) / m) = d - 1 := by
    intro d hd
    have h1 := ((hD d).mp hd).1
    have h1d := hd1 d hd
    exact Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' (by omega : 1 ≤ d)).mp h1.symm)
  set K := ⌊exp β / m⌋₊ with hK
  have hsum : ∑ d ∈ D, 1 / ((d : ℝ) - 1) ≤ 1 / (m : ℝ) * ∑ k ∈ Finset.Icc 1 K, (k : ℝ)⁻¹ := by
    have e1 : ∀ d ∈ D, 1 / ((d : ℝ) - 1) = 1 / (m : ℝ) * (((d - 1) / m : ℕ) : ℝ)⁻¹ := by
      intro d hd
      have h1d := hd1 d hd
      have hc : ((m * ((d - 1) / m) : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) := by rw [hg d hd]
      push_cast [Nat.cast_sub (show 1 ≤ d by omega)] at hc
      rw [← hc, one_div, one_div, mul_inv]
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hinj : Set.InjOn (fun d => (d - 1) / m) D := by
      intro d hd d' hd' h
      have e := hg d hd
      have e' := hg d' hd'
      have h1 := hd1 d hd
      have h1' := hd1 d' hd'
      simp only at h
      rw [h] at e
      generalize m * ((d' - 1) / m) = t at e e'
      omega
    rw [← Finset.sum_image (f := fun k : ℕ => (k : ℝ)⁻¹) (s := D) (g := fun d => (d - 1) / m) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨d, hd, rfl⟩ := hk
      have e := hg d hd
      have h1 := hd1 d hd
      have hX := ((hD d).mp hd).2.2
      rw [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos ((d - 1) / m) with h0 | h0
        · rw [h0, mul_zero] at e; omega
        · exact h0
      · apply Nat.le_floor
        rw [le_div_iff₀ hmR]
        have hc : ((m * ((d - 1) / m) : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) := by rw [e]
        push_cast [Nat.cast_sub (show 1 ≤ d by omega)] at hc
        linarith
    · intro k _ _
      positivity
  have hH : ∑ k ∈ Finset.Icc 1 K, (k : ℝ)⁻¹ ≤ 1 + β := by
    have h1 : ∑ k ∈ Finset.Icc 1 K, (k : ℝ)⁻¹ = (harmonic K : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [h1]
    refine (harmonic_le_one_add_log K).trans ?_
    have : Real.log K ≤ β := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · rw [h0]; simp; exact hβ
      · have hK0 : (0:ℝ) < K := by exact_mod_cast h0
        calc Real.log K ≤ Real.log (exp β / m) :=
              Real.log_le_log hK0 (Nat.floor_le (by positivity))
          _ = β - Real.log m := by
              rw [Real.log_div (Real.exp_pos β).ne' hmR.ne', Real.log_exp]
          _ ≤ β := by
              have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
              linarith
    linarith
  calc ((T m β ∩ Set.Iio L).ncard : ℝ) / L < ∑ d ∈ D, 1 / ((d : ℝ) - 1) := hdiv.trans_lt hlt
    _ ≤ 1 / (m : ℝ) * ∑ k ∈ Finset.Icc 1 K, (k : ℝ)⁻¹ := hsum
    _ ≤ 1 / (m : ℝ) * (1 + β) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (β + 1) / m := by rw [one_div_mul_eq_div, add_comm]

lemma delta_eq (m : ℕ) (α : ℝ) :
    δ m α = ((T m ((m : ℝ) ^ α) ∩ Set.Iio (⌈exp ((m : ℝ) ^ α)⌉₊).factorial).ncard : ℝ) /
      (⌈exp ((m : ℝ) ^ α)⌉₊).factorial := by
  have h1 := (density_exists m α).choose_spec
  have h2 := P.per_dens (T m ((m : ℝ) ^ α)) _ (Nat.factorial_pos _) (per m _)
  unfold Set.HasDensity at h1 h2
  exact tendsto_nhds_unique h1 h2

end Q

theorem erdos_697.variants.delta_lt (m : ℕ) (α : ℝ) (hm : 0 < m) : δ m α < (m ^ α + 1) / m := by
  rw [Q.delta_eq]
  exact Q.bound m _ (Real.rpow_nonneg (Nat.cast_nonneg m) α) hm _ (Nat.factorial_pos _)
    (Q.dvdL _)

end Erdos697

#print axioms Erdos697.density_exists
#print axioms Erdos697.erdos_697.variants.delta_lt
