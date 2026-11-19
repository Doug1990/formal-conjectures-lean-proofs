import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Filter Topology
open scoped Nat

/-! Definitions restated from FormalConjecturesForMathlib/Data/Set/Density.lean -/
namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

/-- Restated from FormalConjecturesForMathlib/Order/Unimodular.lean -/
def UnimodularOn (f : ℕ → ℝ) (a : ℕ) : Prop :=
  ∃ M > a, MonotoneOn f (Set.Ioc a M) ∧ AntitoneOn f (Set.Ici M)

namespace Erdos692

def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}

def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop :=
  (exactlyOneDivisorIn n m).HasDensity δ

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

/-- The divisor-count set as a Finset. -/
lemma ncard_eq (n m x : ℕ) :
    {d ∈ Set.Ioo n m | d ∣ x}.ncard = ((Finset.Ioo n m).filter (· ∣ x)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext d
  simp

/-- The count over one period, as a decidable Finset expression. -/
def cnt (n m L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun x => ((Finset.Ioo n m).filter (· ∣ x)).card = 1)).card

lemma mem_iff (n m x : ℕ) :
    x ∈ exactlyOneDivisorIn n m ↔ ((Finset.Ioo n m).filter (· ∣ x)).card = 1 := by
  show {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1 ↔ _
  rw [ncard_eq]

lemma per692 (n m L : ℕ) (hdiv : ∀ d ∈ Finset.Ioo n m, d ∣ L) (x : ℕ) :
    x ∈ exactlyOneDivisorIn n m ↔ x + L ∈ exactlyOneDivisorIn n m := by
  rw [mem_iff, mem_iff]
  have e : (Finset.Ioo n m).filter (· ∣ x) = (Finset.Ioo n m).filter (· ∣ x + L) := by
    apply Finset.filter_congr
    intro d hd
    have hdL := hdiv d hd
    constructor
    · intro h1
      exact dvd_add h1 hdL
    · intro h1
      have := Nat.dvd_sub h1 hdL
      rwa [Nat.add_sub_cancel] at this
  rw [e]

lemma ncard_cnt (n m L : ℕ) :
    (exactlyOneDivisorIn n m ∩ Set.Iio L).ncard = cnt n m L := by
  have e2 : exactlyOneDivisorIn n m ∩ Set.Iio L =
      ↑((Finset.range L).filter (fun x => ((Finset.Ioo n m).filter (· ∣ x)).card = 1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.coe_filter, Finset.mem_range,
      Set.mem_ofPred_eq, mem_iff]
    tauto
  rw [e2, Set.ncard_coe_finset]
  rfl

/-- If every `d ∈ (n, m)` divides `L > 0`, then `δ₁(n, m) = cnt / L` is a density. -/
lemma delta_has (n m L : ℕ) (hL : 0 < L) (hdiv : ∀ d ∈ Finset.Ioo n m, d ∣ L) :
    IsDelta₁ n m ((cnt n m L : ℝ) / L) := by
  have hp := P.per_dens _ L hL (per692 n m L hdiv)
  rwa [ncard_cnt] at hp

lemma delta_eq (n m L : ℕ) (hL : 0 < L) (hdiv : ∀ d ∈ Finset.Ioo n m, d ∣ L) (δ : ℝ)
    (h : IsDelta₁ n m δ) : δ = (cnt n m L : ℝ) / L :=
  tendsto_nhds_unique h (delta_has n m L hL hdiv)

lemma c6 : cnt 3 6 20 = 7 := by decide
lemma c7 : cnt 3 7 60 = 20 := by decide
set_option maxRecDepth 20000 in
lemma c8 : cnt 3 8 420 = 152 := by decide

theorem erdos_692.variants.cambie_three :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      δ 3 7 < δ 3 6 ∧ δ 3 7 < δ 3 8 := by
  intro δ hδ
  have h6 := delta_eq 3 6 20 (by norm_num) (by decide) _ (hδ 3 6)
  have h7 := delta_eq 3 7 60 (by norm_num) (by decide) _ (hδ 3 7)
  have h8 := delta_eq 3 8 420 (by norm_num) (by decide) _ (hδ 3 8)
  rw [c6] at h6
  rw [c7] at h7
  rw [c8] at h8
  rw [h6, h7, h8]
  norm_num

/-- Every `δ₁(a, b)` exists (period `b!`). -/
lemma delta_all (a b : ℕ) : IsDelta₁ a b ((cnt a b b ! : ℝ) / b !) := by
  apply delta_has a b b ! (Nat.factorial_pos b)
  intro d hd
  rw [Finset.mem_Ioo] at hd
  exact Nat.dvd_factorial (by omega) hd.2.le

theorem erdos_692.parts.i :
    ¬ ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) → ∀ n, UnimodularOn (δ n) (n + 1) := by
  intro h
  set δ : ℕ → ℕ → ℝ := fun a b => (cnt a b b ! : ℝ) / b ! with hδdef
  have hδ : ∀ a b, IsDelta₁ a b (δ a b) := delta_all
  obtain ⟨h1, h2⟩ := erdos_692.variants.cambie_three δ hδ
  obtain ⟨M, hM, hmono, hanti⟩ := h δ hδ 3
  by_cases hM7 : M ≤ 7
  · have := hanti (show M ≤ 7 from hM7) (show M ≤ 8 by omega) (show (7 : ℕ) ≤ 8 by norm_num)
    linarith
  · have := hmono (show (6 : ℕ) ∈ Set.Ioc (3 + 1) M by
        simp only [Set.mem_Ioc]; omega)
      (show (7 : ℕ) ∈ Set.Ioc (3 + 1) M by simp only [Set.mem_Ioc]; omega)
      (show (6 : ℕ) ≤ 7 by norm_num)
    linarith

end Erdos692

#print axioms Erdos692.erdos_692.variants.cambie_three
#print axioms Erdos692.erdos_692.parts.i
