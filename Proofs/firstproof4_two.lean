import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Polynomial Finset ENNReal
open scoped Nat

namespace Arxiv.«2602.05192»

noncomputable def finiteAdditiveConvolution {F : Type} [Field F] (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2)
  ∑ k ∈ range (n + 1), c k • X^(n - k)

local notation p " (⊞_"n ")" q:65  => finiteAdditiveConvolution n p q

noncomputable def Φ (p : ℝ[X]) : ℝ≥0∞ :=
  if p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, 1 / (i - j)) ^ 2).toNNReal
  else
    ⊤

def FourProp (p q : ℝ[X]) (n : ℕ) : Prop :=
    p.degree = n → p.roots.card = n → q.degree = n  → q.roots.card = n → p.Monic → q.Monic →
    1 / Φ p + 1 / Φ q ≤ 1 / Φ (p (⊞_n) q)

/-- `1/Φ` of a monic quadratic with roots `a, b` is `(a-b)^2/2`. -/
lemma phi_quad (a b : ℝ) :
    1 / Φ ((X - C a) * (X - C b)) = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  have hr : ((X - C a) * (X - C b)).roots = a ::ₘ {b} := by
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, Multiset.singleton_add]
  by_cases hab : a = b
  · subst hab
    have hnd : ¬ (a ::ₘ ({a} : Multiset ℝ)).Nodup := by
      rw [Multiset.nodup_cons]; simp
    simp only [Φ, hr, if_neg hnd, sub_self]
    simp
  · have hnd : (a ::ₘ ({b} : Multiset ℝ)).Nodup := by
      rw [Multiset.nodup_cons]
      exact ⟨by simpa using hab, Multiset.nodup_singleton b⟩
    have hts : (a ::ₘ ({b} : Multiset ℝ)).toFinset = {a, b} := by
      rw [Multiset.toFinset_cons, Multiset.toFinset_singleton]
    have e1 : ({a, b} : Finset ℝ).erase a = {b} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h1
        · exact h2
      · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩
    have e2 : ({a, b} : Finset ℝ).erase b = {a} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · rintro rfl; exact ⟨hab, Or.inl rfl⟩
    have hsub : a - b ≠ 0 := sub_ne_zero.2 hab
    have hsum : (∑ i ∈ ({a, b} : Finset ℝ), (∑ j ∈ ({a, b} : Finset ℝ).erase i, 1 / (i - j)) ^ 2)
        = 2 / (a - b) ^ 2 := by
      rw [Finset.sum_pair hab, e1, e2, Finset.sum_singleton, Finset.sum_singleton]
      have : b - a = -(a - b) := by ring
      rw [this]
      field_simp
      ring
    simp only [Φ, hr, if_pos hnd, hts]
    rw [hsum]
    have hpos : 0 < 2 / (a - b) ^ 2 := by positivity
    have h1 : ((2 / (a - b) ^ 2).toNNReal : ℝ≥0∞) = ENNReal.ofReal (2 / (a - b) ^ 2) := rfl
    rw [h1, one_div, ← ENNReal.ofReal_inv_of_pos hpos]
    congr 1
    field_simp

/-- Coefficient form of the degree-2 convolution. -/
lemma conv2 (p q : ℝ[X]) : (p (⊞_2) q) =
    C (p.coeff 2 * q.coeff 2) * X ^ 2 + C (p.coeff 1 * q.coeff 2 + p.coeff 2 * q.coeff 1) * X
      + C (p.coeff 0 * q.coeff 2 + p.coeff 2 * q.coeff 0 + p.coeff 1 * q.coeff 1 / 2) := by
  ext m
  simp only [finiteAdditiveConvolution, coeff_smul, coeff_X_pow, smul_eq_mul,
    Finset.sum_range_succ, Finset.sum_range_zero, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, coeff_add, coeff_C_mul, coeff_X,
    coeff_C]
  rcases m with _ | _ | _ | m <;> simp [Nat.factorial] <;> ring

lemma quad_eq (s t : ℝ) : (X - C s) * (X - C t) = X ^ 2 - C (s + t) * X + C (s * t) := by
  simp only [map_add, map_mul]; ring

lemma coeffs (s t : ℝ) :
    ((X - C s) * (X - C t)).coeff 2 = 1 ∧ ((X - C s) * (X - C t)).coeff 1 = -(s + t) ∧
      ((X - C s) * (X - C t)).coeff 0 = s * t := by
  rw [quad_eq]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_X_pow, coeff_X, coeff_C]

lemma conv_quad (a b c d : ℝ) :
    let S := a + b + c + d
    let Δ := (a - b) ^ 2 + (c - d) ^ 2
    (((X - C a) * (X - C b)) (⊞_2) ((X - C c) * (X - C d))) =
      (X - C ((S + Real.sqrt Δ) / 2)) * (X - C ((S - Real.sqrt Δ) / 2)) := by
  intro S Δ
  obtain ⟨p2, p1, p0⟩ := coeffs a b
  obtain ⟨q2, q1, q0⟩ := coeffs c d
  have hΔ : 0 ≤ Δ := by positivity
  have hsq := Real.sq_sqrt hΔ
  rw [conv2, p2, p1, p0, q2, q1, q0, quad_eq]
  have e1 : (S + Real.sqrt Δ) / 2 + (S - Real.sqrt Δ) / 2 = -(-(a + b) * 1 + 1 * -(c + d)) := by
    simp only [S]; ring
  have e2 : (S + Real.sqrt Δ) / 2 * ((S - Real.sqrt Δ) / 2) =
      a * b * 1 + 1 * (c * d) + -(a + b) * -(c + d) / 2 := by
    have : (S + Real.sqrt Δ) / 2 * ((S - Real.sqrt Δ) / 2) = (S ^ 2 - Real.sqrt Δ ^ 2) / 4 := by
      ring
    rw [this, hsq]; simp only [S, Δ]; ring
  rw [e1, e2, map_neg, one_mul, map_one, one_mul]
  ring

lemma factor (p : ℝ[X]) (hd : p.degree = (2 : ℕ)) (hc : p.roots.card = 2) (hm : p.Monic) :
    ∃ a b : ℝ, p = (X - C a) * (X - C b) := by
  have hnd : p.natDegree = 2 := natDegree_eq_of_degree_eq_some hd
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hc, hnd])
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, b, ?_⟩
  rw [← h, hab]
  simp

theorem four_2 : ∀ (p q : ℝ[X]), FourProp p q 2 := by
  intro p q hpd hpc hqd hqc hpm hqm
  obtain ⟨a, b, rfl⟩ := factor p hpd hpc hpm
  obtain ⟨c, d, rfl⟩ := factor q hqd hqc hqm
  rw [conv_quad, phi_quad, phi_quad, phi_quad,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  have hΔ : 0 ≤ (a - b) ^ 2 + (c - d) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hΔ
  have : (a + b + c + d + √((a - b) ^ 2 + (c - d) ^ 2)) / 2 -
      (a + b + c + d - √((a - b) ^ 2 + (c - d) ^ 2)) / 2 = √((a - b) ^ 2 + (c - d) ^ 2) := by ring
  rw [this, hsq]
  ring

end Arxiv.«2602.05192»

#print axioms Arxiv.«2602.05192».four_2
