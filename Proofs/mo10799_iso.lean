import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.LinearCombination

namespace Mathoverflow10799

open Finset Real

noncomputable def μ {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ #S * (1 - p) ^ (n - #S)

noncomputable def μFamily {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S ∈ F, μ p S

def boundaryCount (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ Xor (S ∈ F) (symmDiff S {i} ∈ F)).card

noncomputable def edgeBoundary (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S : Finset (Fin n), μ p S * boundaryCount n F S

abbrev IsMonotoneIncreasing {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUpperSet (↑F : Set (Finset (Fin n)))

section general

variable {α : Type*} [DecidableEq α]

noncomputable def mu (p : ℝ) (U S : Finset α) : ℝ := p ^ #S * (1 - p) ^ (#U - #S)

open Classical in
noncomputable def Mm (p : ℝ) (P : Finset α → Prop) (U : Finset α) : ℝ :=
  ∑ S ∈ U.powerset, if P S then mu p U S else 0

open Classical in
noncomputable def hc (P : Finset α → Prop) (U S : Finset α) : ℝ :=
  ∑ i ∈ U, if (P S ↔ P (symmDiff S {i})) then 0 else 1

noncomputable def Bb (p : ℝ) (P : Finset α → Prop) (U : Finset α) : ℝ :=
  ∑ S ∈ U.powerset, mu p U S * hc P U S

open Classical in
noncomputable def dd (P : Finset α → Prop) (j : α) (S : Finset α) : ℝ :=
  if (P S ↔ P (insert j S)) then 0 else 1

lemma sd_not {j : α} {S : Finset α} (h : j ∉ S) : symmDiff S {j} = insert j S := by
  ext x
  simp only [mem_symmDiff, mem_insert, mem_singleton]
  rcases eq_or_ne x j with rfl | h1
  · simp [h]
  · simp [h1]

lemma sd_self {j : α} {S : Finset α} (h : j ∉ S) : symmDiff (insert j S) {j} = S := by
  ext x
  simp only [mem_symmDiff, mem_insert, mem_singleton]
  rcases eq_or_ne x j with rfl | h1
  · simp [h]
  · simp [h1]

lemma sd_insert {i j : α} {S : Finset α} (h : i ≠ j) :
    symmDiff (insert j S) {i} = insert j (symmDiff S {i}) := by
  ext x
  simp only [mem_symmDiff, mem_insert, mem_singleton]
  rcases eq_or_ne x j with rfl | h1
  · simp [Ne.symm h]
  · simp [h1]

lemma mu_left {p : ℝ} {j : α} {U S : Finset α} (hj : j ∉ U) (hS : S ⊆ U) :
    mu p (insert j U) S = (1 - p) * mu p U S := by
  unfold mu
  have := card_le_card hS
  rw [card_insert_of_notMem hj, show #U + 1 - #S = (#U - #S) + 1 by omega, pow_succ]
  ring

lemma mu_right {p : ℝ} {j : α} {U S : Finset α} (hj : j ∉ U) (hS : S ⊆ U) :
    mu p (insert j U) (insert j S) = p * mu p U S := by
  unfold mu
  have hjS : j ∉ S := fun h => hj (hS h)
  have := card_le_card hS
  rw [card_insert_of_notMem hj, card_insert_of_notMem hjS,
    show #U + 1 - (#S + 1) = #U - #S by omega, pow_succ]
  ring

lemma hc_left {P : Finset α → Prop} {j : α} {U S : Finset α} (hj : j ∉ U) (hS : S ⊆ U) :
    hc P (insert j U) S = dd P j S + hc P U S := by
  have hjS : j ∉ S := fun h => hj (hS h)
  unfold hc
  rw [sum_insert hj, sd_not hjS]
  rfl

lemma hc_right {P : Finset α → Prop} {j : α} {U S : Finset α} (hj : j ∉ U) (hS : S ⊆ U) :
    hc P (insert j U) (insert j S) = dd P j S + hc (fun T => P (insert j T)) U S := by
  have hjS : j ∉ S := fun h => hj (hS h)
  unfold hc
  rw [sum_insert hj, sd_self hjS]
  congr 1
  · unfold dd
    by_cases h1 : P S <;> by_cases h2 : P (insert j S) <;> simp [h1, h2]
  · refine sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [sd_insert hij]

lemma Mm_insert {p : ℝ} {P : Finset α → Prop} {j : α} {U : Finset α} (hj : j ∉ U) :
    Mm p P (insert j U) = (1 - p) * Mm p P U + p * Mm p (fun T => P (insert j T)) U := by
  unfold Mm
  rw [sum_powerset_insert hj, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun S hS => ?_
    rw [mu_left hj (mem_powerset.1 hS)]
    split_ifs <;> ring
  · refine sum_congr rfl fun S hS => ?_
    rw [mu_right hj (mem_powerset.1 hS)]
    split_ifs <;> ring

lemma Bb_insert {p : ℝ} {P : Finset α → Prop} {j : α} {U : Finset α} (hj : j ∉ U) :
    Bb p P (insert j U) = (1 - p) * Bb p P U + p * Bb p (fun T => P (insert j T)) U
      + ∑ S ∈ U.powerset, mu p U S * dd P j S := by
  unfold Bb
  rw [sum_powerset_insert hj]
  have e1 : ∑ S ∈ U.powerset, mu p (insert j U) S * hc P (insert j U) S
      = ∑ S ∈ U.powerset, ((1 - p) * (mu p U S * hc P U S) + (1 - p) * (mu p U S * dd P j S)) :=
    sum_congr rfl fun S hS => by
      rw [mu_left hj (mem_powerset.1 hS), hc_left hj (mem_powerset.1 hS)]; ring
  have e2 : ∑ S ∈ U.powerset, mu p (insert j U) (insert j S) * hc P (insert j U) (insert j S)
      = ∑ S ∈ U.powerset, (p * (mu p U S * hc (fun T => P (insert j T)) U S)
          + p * (mu p U S * dd P j S)) :=
    sum_congr rfl fun S hS => by
      rw [mu_right hj (mem_powerset.1 hS), hc_right hj (mem_powerset.1 hS)]; ring
  rw [e1, e2, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
  ring

lemma dd_sum {p : ℝ} {P : Finset α → Prop} {j : α} {U : Finset α}
    (hmono : ∀ S T, S ⊆ T → P S → P T) :
    ∑ S ∈ U.powerset, mu p U S * dd P j S
      = Mm p (fun T => P (insert j T)) U - Mm p P U := by
  unfold Mm
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun S _ => ?_
  unfold dd
  by_cases h1 : P S
  · have h2 : P (insert j S) := hmono _ _ (subset_insert _ _) h1
    simp [h1, h2]
  · by_cases h2 : P (insert j S) <;> simp [h1, h2]

omit [DecidableEq α] in
lemma mu_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U S : Finset α) : 0 ≤ mu p U S :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma Mm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : Finset α → Prop) (U : Finset α) :
    0 ≤ Mm p P U := by
  unfold Mm
  refine sum_nonneg fun S _ => ?_
  split_ifs
  · exact mu_nonneg hp0 hp1 U S
  · exact le_refl _

lemma Mm_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {P : Finset α → Prop} {j : α}
    {U : Finset α} (hmono : ∀ S T, S ⊆ T → P S → P T) :
    Mm p P U ≤ Mm p (fun T => P (insert j T)) U := by
  unfold Mm
  refine sum_le_sum fun S _ => ?_
  by_cases h1 : P S
  · have h2 : P (insert j S) := hmono _ _ (subset_insert _ _) h1
    simp [h1, h2]
  · rw [if_neg h1]
    split_ifs
    · exact mu_nonneg hp0 hp1 U S
    · exact le_refl _

end general

lemma core_ineq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l * (negMulLog (1 - p) + negMulLog p)
      ≤ negMulLog (l * (1 - p)) + negMulLog (1 - l * (1 - p)) := by
  have e := negMulLog_mul l (1 - p)
  have hGl := negMulLog_nonneg hl0 hl1
  have hc := concaveOn_negMulLog.2 (Set.mem_Ici.2 hp0.le) (Set.mem_Ici.2 zero_le_one)
    hl0 (sub_nonneg.2 hl1) (by ring)
  simp only [smul_eq_mul, negMulLog_one, mul_zero, add_zero, mul_one] at hc
  rw [show 1 - l * (1 - p) = l * p + (1 - l) by ring]
  have := mul_nonneg (sub_nonneg.2 hp1.le) hGl
  linarith

lemma two_point {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    negMulLog ((1 - p) * a + p * b)
      ≤ (1 - p) * negMulLog a + p * negMulLog b + p * (-log p) * (b - a) := by
  obtain ⟨x, hx⟩ : ∃ x, x = (1 - p) * a + p * b := ⟨_, rfl⟩
  rw [← hx]
  have hqa : 0 ≤ (1 - p) * a := mul_nonneg (sub_nonneg.2 hp1.le) ha
  have hpb : 0 ≤ p * b := mul_nonneg hp0.le (ha.trans hab)
  rcases (show 0 ≤ x by linarith).eq_or_lt with h0 | hxpos
  · have e1 : (1 - p) * a = 0 := by linarith
    have e2 : p * b = 0 := by linarith
    have ha0 : a = 0 := (mul_eq_zero.1 e1).resolve_left (by linarith)
    have hb0 : b = 0 := (mul_eq_zero.1 e2).resolve_left hp0.ne'
    subst ha0 hb0
    rw [← h0]
    simp
  · obtain ⟨l, hl⟩ : ∃ l, l = a / x := ⟨_, rfl⟩
    have h6 : a = l * x := by rw [hl, div_mul_cancel₀ a hxpos.ne']
    have hl0 : 0 ≤ l := hl ▸ div_nonneg ha hxpos.le
    have hpba : 0 ≤ p * (b - a) := mul_nonneg hp0.le (sub_nonneg.2 hab)
    have hl1 : l ≤ 1 := by
      rw [hl, div_le_one hxpos]; linarith
    have core := core_ineq hp0 hp1 hl0 hl1
    have h1 := negMulLog_mul (1 - p) a
    have h2 := negMulLog_mul p b
    have h3 : negMulLog ((1 - p) * a) = (l * (1 - p)) * negMulLog x
        + x * negMulLog (l * (1 - p)) := by
      rw [show (1 - p) * a = x * (l * (1 - p)) by rw [h6]; ring, negMulLog_mul]
    have h4 : negMulLog (p * b) = (1 - l * (1 - p)) * negMulLog x
        + x * negMulLog (1 - l * (1 - p)) := by
      rw [show p * b = x * (1 - l * (1 - p)) by linear_combination -hx - (1 - p) * h6,
        negMulLog_mul]
    have h5 : negMulLog p = p * (-log p) := by unfold negMulLog; ring
    have key : (1 - p) * negMulLog a + p * negMulLog b + p * (-log p) * (b - a) - negMulLog x
        = x * ((negMulLog (l * (1 - p)) + negMulLog (1 - l * (1 - p)))
          - l * (negMulLog (1 - p) + negMulLog p)) := by
      linear_combination -h1 - h2 + h3 + h4 + (l * x - b) * h5
        - (negMulLog (1 - p) + p * (-log p)) * h6
    have hnn := mul_nonneg hxpos.le (sub_nonneg.2 core)
    linarith

theorem main_ineq {α : Type*} [DecidableEq α] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (U : Finset α) : ∀ P : Finset α → Prop, (∀ S T, S ⊆ T → P S → P T) →
      negMulLog (Mm p P U) ≤ p * (-log p) * Bb p P U := by
  refine Finset.induction_on U ?_ ?_
  · intro P _
    unfold Mm Bb hc
    simp only [powerset_empty, sum_singleton, sum_empty, mul_zero]
    split_ifs <;> simp [mu]
  · intro j U hj ih P hP
    have hP1 : ∀ S T, S ⊆ T → P (insert j S) → P (insert j T) :=
      fun S T h => hP _ _ (insert_subset_insert j h)
    rw [Mm_insert hj, Bb_insert hj, dd_sum hP]
    have i1 := ih P hP
    have i2 := ih _ hP1
    have ha := Mm_nonneg hp0.le hp1.le P U
    have hab := Mm_mono (j := j) (U := U) hp0.le hp1.le hP
    have tp := two_point hp0 hp1 ha hab
    have j1 := mul_le_mul_of_nonneg_left i1 (sub_nonneg.2 hp1.le)
    have j2 := mul_le_mul_of_nonneg_left i2 hp0.le
    linarith

theorem discrete_isoperimetric_inequality (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F) :
    let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p := by
  intro m
  have hmono : ∀ S T : Finset (Fin n), S ⊆ T → S ∈ F → T ∈ F := fun S T h hS => by
    have := hF (show S ≤ T from h) (by simpa using hS)
    simpa using this
  have main := main_ineq hp hp' (univ : Finset (Fin n)) (fun S => S ∈ F) hmono
  have hM : Mm p (fun S => S ∈ F) univ = m := by
    calc Mm p (fun S => S ∈ F) univ = ∑ S : Finset (Fin n), if S ∈ F then μ p S else 0 := by
          unfold Mm
          rw [powerset_univ]
          refine sum_congr rfl fun S _ => ?_
          by_cases h : S ∈ F <;> simp [h, mu, μ]
      _ = m := by
          show _ = μFamily p F
          unfold μFamily
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hB : Bb p (fun S => S ∈ F) univ = edgeBoundary n p F := by
    unfold Bb edgeBoundary
    rw [powerset_univ]
    refine sum_congr rfl fun S _ => ?_
    have e1 : mu p univ S = μ p S := by simp [mu, μ]
    have e2 : hc (fun S => S ∈ F) univ S = (boundaryCount n F S : ℝ) := by
      unfold hc boundaryCount
      rw [Finset.card_filter]
      push_cast
      refine sum_congr rfl fun i _ => ?_
      by_cases h1 : S ∈ F <;> by_cases h2 : symmDiff S {i} ∈ F <;> simp [h1, h2]
    rw [e1, e2]
  rw [hM, hB] at main
  have hlog : log p < 0 := Real.log_neg hp hp'
  have hL : 0 < p * -log p := mul_pos hp (neg_pos.2 hlog)
  have e : m * Real.logb p m / p = negMulLog m / (p * -log p) := by
    unfold negMulLog Real.logb
    have : log p ≠ 0 := hlog.ne
    field_simp
  show m * Real.logb p m / p ≤ edgeBoundary n p F
  rw [e, div_le_iff₀ hL]
  linarith

#print axioms discrete_isoperimetric_inequality

end Mathoverflow10799
