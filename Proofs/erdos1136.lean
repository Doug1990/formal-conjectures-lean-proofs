import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
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

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos1136

def AvoidsPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

def muellerSet : Set ℕ := {n | ∃ i : ℕ, n ≡ 3 * 2 ^ i [MOD 2 ^ (i + 2)]}

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

/-! Müller's set -/

lemma mem_of_mod3 (n : ℕ) (h : n % 4 = 3) : n ∈ muellerSet := by
  refine ⟨0, ?_⟩
  unfold Nat.ModEq
  rw [show (2:ℕ) ^ (0 + 2) = 4 by norm_num, pow_zero, mul_one]
  omega

lemma not_mem_of_mod1 (n : ℕ) (h : n % 4 = 1) : n ∉ muellerSet := by
  rintro ⟨i, hi⟩
  rcases i with _ | j
  · unfold Nat.ModEq at hi
    rw [show (2:ℕ) ^ (0 + 2) = 4 by norm_num, pow_zero, mul_one] at hi
    omega
  · have h2 : (2:ℕ) ∣ 2 ^ (j + 1 + 2) := dvd_pow_self 2 (by omega)
    have h3 := Nat.ModEq.of_dvd h2 hi
    rw [show 3 * 2 ^ (j + 1) = 2 * (3 * 2 ^ j) by ring] at h3
    unfold Nat.ModEq at h3
    rw [Nat.mul_mod_right] at h3
    omega

lemma mem_double (n : ℕ) : 2 * n ∈ muellerSet ↔ n ∈ muellerSet := by
  constructor
  · rintro ⟨i, hi⟩
    rcases i with _ | j
    · unfold Nat.ModEq at hi
      rw [show (2:ℕ) ^ (0 + 2) = 4 by norm_num, pow_zero, mul_one] at hi
      omega
    · refine ⟨j, ?_⟩
      rw [show 3 * 2 ^ (j + 1) = 2 * (3 * 2 ^ j) by ring,
        show (2:ℕ) ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) by ring] at hi
      exact Nat.ModEq.mul_left_cancel' (by norm_num) hi
  · rintro ⟨i, hi⟩
    refine ⟨i + 1, ?_⟩
    rw [show 3 * 2 ^ (i + 1) = 2 * (3 * 2 ^ i) by ring,
      show (2:ℕ) ^ (i + 1 + 2) = 2 * 2 ^ (i + 2) by ring]
    exact Nat.ModEq.mul_left' 2 hi

lemma odd_mem (n : ℕ) (h : n ∈ muellerSet) (h2 : n % 2 = 1) : n % 4 = 3 := by
  by_contra h'
  exact not_mem_of_mod1 n (by omega) h

lemma avoids : AvoidsPowersOfTwo muellerSet := by
  intro a ha b hb k
  induction k generalizing a b with
  | zero =>
    intro h
    rw [pow_zero] at h
    rcases (show (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) by omega) with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · exact not_mem_of_mod1 1 (by norm_num) hb
    · exact not_mem_of_mod1 1 (by norm_num) ha
  | succ k ih =>
    intro h
    have hp : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hp] at h
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
      exact ih a' ((mem_double a').mp ha) b' ((mem_double b').mp hb) (by omega)
    · omega
    · omega
    · have h4a := odd_mem a ha ha2
      have h4b := odd_mem b hb hb2
      rcases k with _ | k
      · rw [pow_zero] at h
        omega
      · have : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        omega

/-- counting function of Müller's set -/
noncomputable def C (N : ℕ) : ℕ := (muellerSet ∩ Set.Iio N).ncard

lemma C_succ (N : ℕ) : C (N + 1) = C N + if N ∈ muellerSet then 1 else 0 :=
  cnt_succ muellerSet N

lemma rec2 (K : ℕ) : C (2 * K) = 2 * K / 4 + C K ∧ C (2 * K + 1) = (2 * K + 1) / 4 + C (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    obtain ⟨_, h1⟩ := ih
    have e1 : C (2 * (K + 1)) = 2 * (K + 1) / 4 + C (K + 1) := by
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by ring, C_succ, h1]
      by_cases hm : (2 * K + 1) % 4 = 3
      · rw [if_pos (mem_of_mod3 _ hm)]
        omega
      · rw [if_neg (not_mem_of_mod1 _ (by omega))]
        omega
    refine ⟨e1, ?_⟩
    rw [C_succ, e1, show K + 1 + 1 = (K + 1) + 1 by rfl, C_succ (K + 1)]
    by_cases hm : K + 1 ∈ muellerSet
    · rw [if_pos ((mem_double _).mpr hm), if_pos hm]
      omega
    · rw [if_neg (fun h => hm ((mem_double _).mp h)), if_neg hm]
      omega

lemma rec (N : ℕ) : C N = N / 4 + C ((N + 1) / 2) := by
  obtain ⟨K, rfl | rfl⟩ := Nat.even_or_odd' N
  · rw [(rec2 K).1, show (2 * K + 1) / 2 = K by omega]
  · rw [(rec2 K).2, show (2 * K + 1 + 1) / 2 = K + 1 by omega]

lemma bound (k : ℕ) : ∀ N : ℕ, N ≤ 2 ^ k → |(C N : ℝ) - N / 2| ≤ k + 1 := by
  induction k with
  | zero =>
    intro N hN
    have h1 : (C N : ℝ) ≤ N := by exact_mod_cast cnt_le muellerSet N
    have h0 : (0:ℝ) ≤ C N := Nat.cast_nonneg _
    have hN' : (N:ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by simpa using hN)
    rw [abs_le]
    push_cast
    constructor <;> linarith
  | succ k ih =>
    intro N hN
    have hp : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hB : (N + 1) / 2 ≤ 2 ^ k := by omega
    have h := ih _ hB
    have hr := rec N
    have h4 : 4 * (N / 4) + 2 * ((N + 1) / 2) = 2 * N ∨
        4 * (N / 4) + 2 * ((N + 1) / 2) + 2 = 2 * N := by omega
    have hrR : (C N : ℝ) = ((N / 4 : ℕ) : ℝ) + (C ((N + 1) / 2) : ℝ) := by
      exact_mod_cast hr
    rw [hrR]
    rw [abs_le] at h ⊢
    push_cast
    rcases h4 with h4 | h4
    · have h4' : (4 * ((N / 4 : ℕ) : ℝ) + 2 * (((N + 1) / 2 : ℕ) : ℝ)) = 2 * N := by
        exact_mod_cast h4
      constructor <;> linarith [h.1, h.2]
    · have h4' : (4 * ((N / 4 : ℕ) : ℝ) + 2 * (((N + 1) / 2 : ℕ) : ℝ) + 2) = 2 * N := by
        exact_mod_cast h4
      constructor <;> linarith [h.1, h.2]

lemma sqpow (k : ℕ) : (k + 1) ^ 2 ≤ 2 ^ (k + 2) ∧ 2 * k + 3 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e : (2:ℕ) ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
    rw [e]
    constructor <;> nlinarith [ih.1, ih.2]

lemma sq_bound (N : ℕ) (hN : 1 ≤ N) : ((C N : ℝ) - 1 / 2 * N) ^ 2 ≤ 8 * N := by
  set k := Nat.log 2 N with hk
  have h1 : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hb := bound (k + 1) N h1.le
  have hs := (sqpow (k + 1)).1
  have hs' : (k + 1 + 1) ^ 2 ≤ 8 * N := by
    have : (2:ℕ) ^ (k + 1 + 2) = 8 * 2 ^ k := by ring
    omega
  have hsR : ((k:ℝ) + 1 + 1) ^ 2 ≤ 8 * N := by exact_mod_cast hs'
  rw [show (1:ℝ) / 2 * N = N / 2 by ring]
  have habs := hb
  push_cast at habs
  have := abs_le.mp habs
  nlinarith [this.1, this.2]

lemma mueller_density : muellerSet.HasDensity (1 / 2) :=
  dens_of_sq muellerSet (1 / 2) 8 (by norm_num) (fun N hN => sq_bound N hN)

/-! multiples of three -/

lemma three_count (N : ℕ) : ({n : ℕ | 3 ∣ n} ∩ Set.Iio N).ncard = (N + 2) / 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [cnt_succ, ih]
    by_cases h : 3 ∣ N
    · rw [if_pos (show N ∈ {n : ℕ | 3 ∣ n} from h)]
      omega
    · rw [if_neg (show N ∉ {n : ℕ | 3 ∣ n} from h)]
      omega

lemma three_density : Set.HasDensity {n : ℕ | 3 ∣ n} (1 / 3) := by
  refine dens_of_sq _ (1 / 3) 1 (by norm_num) (fun N hN => ?_)
  rw [three_count]
  have h3 : 3 * ((N + 2) / 3) = N ∨ 3 * ((N + 2) / 3) = N + 1 ∨ 3 * ((N + 2) / 3) = N + 2 := by
    omega
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  rcases h3 with h | h | h
  · have hR : 3 * (((N + 2) / 3 : ℕ) : ℝ) = N := by exact_mod_cast h
    nlinarith
  · have hR : 3 * (((N + 2) / 3 : ℕ) : ℝ) = N + 1 := by exact_mod_cast h
    nlinarith
  · have hR : 3 * (((N + 2) / 3 : ℕ) : ℝ) = N + 2 := by exact_mod_cast h
    nlinarith

/-! upper bound -/

lemma le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ (a + 1) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    omega

lemma card_bound (A : Set ℕ) (hA : AvoidsPowersOfTwo A) (k : ℕ) :
    (A ∩ Set.Iio (2 ^ (k + 1))).ncard ≤ 2 ^ k := by
  have hp : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  calc (A ∩ Set.Iio (2 ^ (k + 1))).ncard
      ≤ (Set.Iio (2 ^ k)).ncard := by
        refine Set.ncard_le_ncard_of_injOn
          (fun x => if x < 2 ^ k then x else 2 ^ (k + 1) - x) ?_ ?_ (Set.finite_Iio _)
        · intro x hx
          have hx2 : x < 2 ^ (k + 1) := hx.2
          have hne := hA x hx.1 x hx.1 (k + 1)
          simp only [Set.mem_Iio]
          split_ifs with h1
          · exact h1
          · omega
        · intro x hx y hy hxy
          have hx2 : x < 2 ^ (k + 1) := hx.2
          have hy2 : y < 2 ^ (k + 1) := hy.2
          have h1 := hA x hx.1 y hy.1 (k + 1)
          have h2 := hA y hy.1 x hx.1 (k + 1)
          simp only at hxy
          split_ifs at hxy <;> omega
    _ = 2 ^ k := ncard_Iio' _

end P

theorem erdos_1136 :
    ∃ A : Set ℕ, (1 / 3 : ℝ) < A.lowerDensity ∧ AvoidsPowersOfTwo A := by
  refine ⟨muellerSet, ?_, P.avoids⟩
  have h : Tendsto (fun b : ℕ => muellerSet.partialDensity Set.univ b) atTop (𝓝 (1 / 2)) :=
    P.mueller_density
  unfold Set.lowerDensity
  rw [h.liminf_eq]
  norm_num

theorem erdos_1136.variants.multiples_of_three :
    AvoidsPowersOfTwo {n : ℕ | 3 ∣ n} ∧ Set.HasDensity {n : ℕ | 3 ∣ n} (1 / 3) := by
  refine ⟨?_, P.three_density⟩
  intro a ha b hb k h
  have ha' : 3 ∣ a := ha
  have hb' : 3 ∣ b := hb
  have h3 : 3 ∣ 2 ^ k := h ▸ dvd_add ha' hb'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem erdos_1136.variants.mueller :
    AvoidsPowersOfTwo muellerSet ∧ muellerSet.HasDensity (1 / 2) :=
  ⟨P.avoids, P.mueller_density⟩

theorem erdos_1136.variants.upper_bound (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    A.lowerDensity ≤ 1 / 2 := by
  unfold Set.lowerDensity
  refine Filter.liminf_le_of_frequently_le ?_ ?_
  · rw [Filter.frequently_atTop]
    intro a
    refine ⟨2 ^ (a + 1), (by have := P.le_two_pow a; omega), ?_⟩
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, P.ncard_Iio']
    have hc := P.card_bound A hA a
    have hcR : ((A ∩ Set.Iio (2 ^ (a + 1))).ncard : ℝ) ≤ (2:ℝ) ^ a := by exact_mod_cast hc
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have e : (2:ℝ) ^ (a + 1) = 2 * 2 ^ a := by ring
    rw [e]
    linarith
  · exact Filter.isBoundedUnder_of ⟨0, fun x => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

end Erdos1136

#print axioms Erdos1136.erdos_1136
#print axioms Erdos1136.erdos_1136.variants.multiples_of_three
#print axioms Erdos1136.erdos_1136.variants.mueller
#print axioms Erdos1136.erdos_1136.variants.upper_bound
