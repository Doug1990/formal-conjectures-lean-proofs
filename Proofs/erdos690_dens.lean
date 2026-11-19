import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorial.Basic
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

namespace Erdos690

def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1}

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

/-- Removing the point 0 does not change the density. -/
lemma dens_insert (S : Set ℕ) (h0 : 0 ∉ S) (α : ℝ) (h : (insert 0 S).HasDensity α) :
    S.HasDensity α := by
  unfold Set.HasDensity Set.partialDensity at h ⊢
  simp only [Set.inter_univ, Set.univ_inter, ncard_Iio'] at h ⊢
  have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have h3 := h.sub h2
  rw [sub_zero] at h3
  apply h3.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hfin : (S ∩ Set.Iio N).Finite := (Set.finite_Iio N).subset Set.inter_subset_right
  have e : insert 0 S ∩ Set.Iio N = insert 0 (S ∩ Set.Iio N) :=
    Set.insert_inter_of_mem (show 0 ∈ Set.Iio N from by simp only [Set.mem_Iio]; omega)
  rw [e, Set.ncard_insert_of_notMem (fun hh => h0 hh.1) hfin]
  push_cast
  ring

end P

lemma per (k p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    n ∈ kthPrimeFactorSet k p ↔ n + p.factorial ∈ kthPrimeFactorSet k p := by
  have hdvd : ∀ q, q.Prime → q ≤ p → (q ∣ n ↔ q ∣ n + p.factorial) := by
    intro q hq hqp
    have hqL : q ∣ p.factorial := Nat.dvd_factorial hq.pos hqp
    constructor
    · intro h
      exact dvd_add h hqL
    · intro h
      have := Nat.dvd_sub h hqL
      rwa [Nat.add_sub_cancel] at this
  have hn0 : n ≠ 0 := by omega
  have hn0' : n + p.factorial ≠ 0 := by omega
  have hF : n.primeFactors.filter (· < p) = (n + p.factorial).primeFactors.filter (· < p) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, hn0, hn0', not_false_eq_true,
      and_true]
    constructor
    · rintro ⟨⟨hq, hqn⟩, hqp⟩
      exact ⟨⟨hq, (hdvd q hq hqp.le).mp hqn⟩, hqp⟩
    · rintro ⟨⟨hq, hqn⟩, hqp⟩
      exact ⟨⟨hq, (hdvd q hq hqp.le).mpr hqn⟩, hqp⟩
  have hP : p ∈ n.primeFactors ↔ p ∈ (n + p.factorial).primeFactors := by
    simp only [Nat.mem_primeFactors, ne_eq, hn0, hn0', not_false_eq_true, and_true]
    exact and_congr_right (fun _ => hdvd p hp le_rfl)
  change (0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1) ↔
    (0 < n + p.factorial ∧ p ∈ (n + p.factorial).primeFactors ∧
      ((n + p.factorial).primeFactors.filter (· < p)).card = k - 1)
  rw [hF, hP]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨by omega, h1, h2⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨by omega, h1, h2⟩

theorem erdos_690.variants.hasDensity (k p : ℕ) (hk : 1 ≤ k) (hp : p.Prime) :
    ∃ δ : ℝ, (kthPrimeFactorSet k p).HasDensity δ := by
  set S := kthPrimeFactorSet k p with hS
  have hL : 0 < p.factorial := Nat.factorial_pos p
  have hper : ∀ n, 1 ≤ n → (n ∈ S ↔ n + p.factorial ∈ S) := per k p hp
  have h0 : 0 ∉ S := fun h => lt_irrefl 0 h.1
  by_cases hLS : p.factorial ∈ S
  · refine ⟨_, P.dens_insert S h0 _ (P.per_dens (insert 0 S) p.factorial hL ?_)⟩
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_add]
      exact iff_of_true (Set.mem_insert 0 S) (Set.mem_insert_of_mem 0 hLS)
    · have a : n ≠ 0 := by omega
      have b : n + p.factorial ≠ 0 := by omega
      simp only [Set.mem_insert_iff, a, b, false_or]
      exact hper n hn
  · refine ⟨_, P.per_dens S p.factorial hL ?_⟩
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_add]
      exact iff_of_false h0 hLS
    · exact hper n hn

end Erdos690

#print axioms Erdos690.erdos_690.variants.hasDensity
