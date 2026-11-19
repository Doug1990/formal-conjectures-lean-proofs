import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Finite.Lattice

open Filter Set

namespace Erdos12

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

namespace ES

lemma ndvd {a x k : ℕ} (h1 : k * a < x) (h2 : x < (k + 1) * a) : ¬ a ∣ x := by
  rintro ⟨q, rfl⟩
  rw [Nat.mul_comm k a] at h1
  rw [Nat.mul_comm (k + 1) a] at h2
  have e1 := Nat.lt_of_mul_lt_mul_left h1
  have e2 := Nat.lt_of_mul_lt_mul_left h2
  omega

lemma exT (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (M Y : ℕ) :
    ∃ T, Y < T ∧ (1 ≤ M → 3 * M + 1 < f (1 + 3 * (M * T))) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hf.eventually_gt_atTop (3 * M + 1))
  refine ⟨Y + N0 + 1, by omega, fun hM => hN0 _ ?_⟩
  have : Y + N0 + 1 ≤ M * (Y + N0 + 1) := Nat.le_mul_of_pos_left _ hM
  omega

def Up (p : ℕ × ℕ) : ℕ := 1 + 3 * (p.1 * p.2)

noncomputable def Tc (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (M Y : ℕ) : ℕ :=
  Classical.choose (exT f hf M Y)

lemma Tc_spec (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (M Y : ℕ) :
    Y < Tc f hf M Y ∧ (1 ≤ M → 3 * M + 1 < f (1 + 3 * (M * Tc f hf M Y))) :=
  Classical.choose_spec (exT f hf M Y)

noncomputable def sqn (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : ℕ → ℕ × ℕ
  | 0 => (1, Tc f hf 1 0)
  | k + 1 => (Nat.factorial (Up (sqn f hf k)),
      Tc f hf (Nat.factorial (Up (sqn f hf k))) (Up (sqn f hf k)))

variable (f : ℕ → ℕ) (hf : Tendsto f atTop atTop)

noncomputable def M (k : ℕ) : ℕ := (sqn f hf k).1
noncomputable def T (k : ℕ) : ℕ := (sqn f hf k).2
noncomputable def U (k : ℕ) : ℕ := Up (sqn f hf k)

lemma U_eq (k : ℕ) : U f hf k = 1 + 3 * (M f hf k * T f hf k) := rfl

lemma M_succ (k : ℕ) : M f hf (k + 1) = Nat.factorial (U f hf k) := rfl

lemma M_pos (k : ℕ) : 1 ≤ M f hf k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact Nat.factorial_pos _

lemma T_spec (k : ℕ) : 1 ≤ T f hf k ∧ 3 * M f hf k + 1 < f (U f hf k) := by
  cases k with
  | zero =>
    have h := Tc_spec f hf 1 0
    exact ⟨h.1, h.2 le_rfl⟩
  | succ k =>
    have h := Tc_spec f hf (Nat.factorial (U f hf k)) (U f hf k)
    exact ⟨lt_of_le_of_lt (Nat.zero_le _) h.1, h.2 (Nat.factorial_pos _)⟩

lemma T_succ (k : ℕ) : U f hf k < T f hf (k + 1) :=
  (Tc_spec f hf (Nat.factorial (U f hf k)) (U f hf k)).1

lemma U_lt (k : ℕ) : U f hf k < U f hf (k + 1) := by
  have h1 := T_succ f hf k
  have h2 : T f hf (k + 1) ≤ M f hf (k + 1) * T f hf (k + 1) :=
    Nat.le_mul_of_pos_left _ (M_pos f hf (k + 1))
  rw [U_eq f hf (k + 1)]
  omega

lemma U_mono : StrictMono (U f hf) := strictMono_nat_of_lt_succ (U_lt f hf)

def blk (k n : ℕ) : Prop := ∃ t, 2 * T f hf k ≤ t ∧ t < 3 * T f hf k ∧ n = 1 + M f hf k * t

def A : Set ℕ := {n | ∃ k, blk f hf k n}

lemma bounds {k n : ℕ} (h : blk f hf k n) :
    1 ≤ M f hf k ∧ 1 ≤ M f hf k * T f hf k ∧ 1 + 2 * (M f hf k * T f hf k) ≤ n ∧
      n + M f hf k ≤ U f hf k ∧ U f hf k = 1 + 3 * (M f hf k * T f hf k) := by
  obtain ⟨t, h1, h2, rfl⟩ := h
  have hM := M_pos f hf k
  have hT := (T_spec f hf k).1
  have hP : 1 ≤ M f hf k * T f hf k := Nat.mul_pos hM hT
  have e1 : M f hf k * (2 * T f hf k) ≤ M f hf k * t := Nat.mul_le_mul_left _ h1
  have e2 : M f hf k * (t + 1) ≤ M f hf k * (3 * T f hf k) := Nat.mul_le_mul_left _ h2
  have e1' : 2 * (M f hf k * T f hf k) ≤ M f hf k * t := by
    calc 2 * (M f hf k * T f hf k) = M f hf k * (2 * T f hf k) := by ring
      _ ≤ _ := e1
  have e2' : M f hf k * t + M f hf k ≤ 3 * (M f hf k * T f hf k) := by
    calc M f hf k * t + M f hf k = M f hf k * (t + 1) := by ring
      _ ≤ _ := e2
      _ = 3 * (M f hf k * T f hf k) := by ring
  refine ⟨hM, hP, by omega, by rw [U_eq]; omega, U_eq f hf k⟩

lemma cross {k l n m : ℕ} (hkl : k < l) (hn : blk f hf k n) (hm : blk f hf l m) :
    n < m ∧ n ∣ M f hf l := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hU : U f hf k ≤ U f hf l := (U_mono f hf).monotone (by omega)
  have bn := bounds f hf hn
  have bm := bounds f hf hm
  have hT := T_succ f hf l
  have h3 : T f hf (l + 1) ≤ M f hf (l + 1) * T f hf (l + 1) :=
    Nat.le_mul_of_pos_left _ (M_pos f hf (l + 1))
  refine ⟨by omega, ?_⟩
  rw [M_succ]
  exact Nat.dvd_factorial (by omega) (by omega)

lemma one_mod {a l m : ℕ} (ha : a ∣ M f hf l) (hm : blk f hf l m) : ∃ r, m = 1 + a * r := by
  obtain ⟨t, -, -, rfl⟩ := hm
  obtain ⟨s, hs⟩ := ha
  exact ⟨s * t, by rw [hs, Nat.mul_assoc]⟩

theorem good : IsGood (A f hf) := by
  refine ⟨?_, ?_⟩
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    have hT := (T_spec f hf (B + 1)).1
    have hmem : 1 + M f hf (B + 1) * (2 * T f hf (B + 1)) ∈ A f hf :=
      ⟨B + 1, _, le_rfl, by omega, rfl⟩
    have h1 := hB hmem
    have h2 := T_succ f hf B
    have h3 : B ≤ U f hf B := (U_mono f hf).id_le B
    have h4 : 2 * T f hf (B + 1) ≤ M f hf (B + 1) * (2 * T f hf (B + 1)) :=
      Nat.le_mul_of_pos_left _ (M_pos f hf (B + 1))
    omega
  · rintro a ⟨i, ha⟩ b ⟨j, hb⟩ c ⟨l, hc⟩ hdvd hab hac
    by_contra hbc
    have ba := bounds f hf ha
    rcases lt_trichotomy j i with hji | rfl | hij
    · have := (cross f hf hji hb ha).1
      omega
    · have bb := bounds f hf hb
      rcases lt_trichotomy l j with hli | rfl | hil
      · have := (cross f hf hli hc ha).1
        omega
      · have bc := bounds f hf hc
        exact ndvd (k := 2) (by omega) (by omega) hdvd
      · obtain ⟨r, hr⟩ := one_mod f hf (cross f hf hil ha hc).2 hc
        have e : b + c = a * r + (b + 1) := by omega
        rw [e] at hdvd
        have h' := (Nat.dvd_add_right (Nat.dvd_mul_right a r)).mp hdvd
        exact ndvd (k := 1) (by omega) (by omega) h'
    · obtain ⟨r, hr⟩ := one_mod f hf (cross f hf hij ha hb).2 hb
      rcases lt_trichotomy l i with hli | rfl | hil
      · have := (cross f hf hli hc ha).1
        omega
      · have bc := bounds f hf hc
        have e : b + c = a * r + (c + 1) := by omega
        rw [e] at hdvd
        have h' := (Nat.dvd_add_right (Nat.dvd_mul_right a r)).mp hdvd
        exact ndvd (k := 1) (by omega) (by omega) h'
      · obtain ⟨r', hr'⟩ := one_mod f hf (cross f hf hil ha hc).2 hc
        have e : b + c = a * (r + r') + 2 := by rw [hr, hr']; ring
        rw [e] at hdvd
        have h' := (Nat.dvd_add_right (Nat.dvd_mul_right a (r + r'))).mp hdvd
        have := Nat.le_of_dvd (by norm_num) h'
        omega

theorem count (k : ℕ) :
    ((U f hf k : ℕ) : ℝ) / f (U f hf k) < (A f hf ∩ Icc 1 (U f hf k)).ncard := by
  have hM := M_pos f hf k
  have hTs := T_spec f hf k
  have hsub : (((Finset.Ico (2 * T f hf k) (3 * T f hf k)).image
      (fun t => 1 + M f hf k * t) : Finset ℕ) : Set ℕ) ⊆ A f hf ∩ Icc 1 (U f hf k) := by
    intro n hn
    simp only [Finset.coe_image, Finset.coe_Ico, Set.mem_image, Set.mem_Ico] at hn
    obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := hn
    have hb := bounds f hf (⟨t, h1, h2, rfl⟩ : blk f hf k (1 + M f hf k * t))
    exact ⟨⟨k, t, h1, h2, rfl⟩, by omega, by omega⟩
  have hinj : Function.Injective (fun t => 1 + M f hf k * t) := by
    intro x y h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hM (by omega)
  have hcard : ((Finset.Ico (2 * T f hf k) (3 * T f hf k)).image
      (fun t => 1 + M f hf k * t)).card = T f hf k := by
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Ico]
    omega
  have hle : T f hf k ≤ (A f hf ∩ Icc 1 (U f hf k)).ncard := by
    rw [← hcard, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub ((Set.finite_Icc 1 (U f hf k)).subset inter_subset_right)
  have hmul : T f hf k * (3 * M f hf k + 2) ≤ T f hf k * f (U f hf k) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : T f hf k * (3 * M f hf k + 2) = 3 * (M f hf k * T f hf k) + 2 * T f hf k := by
    ring
  have hnat : U f hf k < (A f hf ∩ Icc 1 (U f hf k)).ncard * f (U f hf k) := by
    have h2 : T f hf k * f (U f hf k) ≤ (A f hf ∩ Icc 1 (U f hf k)).ncard * f (U f hf k) :=
      Nat.mul_le_mul_right _ hle
    rw [U_eq] at h2 hmul ⊢
    omega
  have hfpos : (0 : ℝ) < f (U f hf k) := by exact_mod_cast (show 0 < f (U f hf k) by omega)
  rw [div_lt_iff₀ hfpos]
  exact_mod_cast hnat

end ES

theorem erdos_12.variants.erdos_sarkozy (f : ℕ → ℕ) (hf : atTop.Tendsto f atTop) :
    ∃ A, IsGood A ∧ {N : ℕ | (N : ℝ) / f N < (A ∩ Icc 1 N).ncard}.Infinite := by
  refine ⟨ES.A f hf, ES.good f hf, ?_⟩
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have h1 := hB (ES.count f hf (B + 1))
  have h2 : B + 1 ≤ ES.U f hf (B + 1) := (ES.U_mono f hf).id_le (B + 1)
  omega

#print axioms Erdos12.erdos_12.variants.erdos_sarkozy

end Erdos12
