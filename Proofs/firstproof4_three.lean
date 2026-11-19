import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

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

/-- Shift-invariant coefficient `A` of a monic cubic. -/
noncomputable def Aq (f : ℝ[X]) : ℝ := f.coeff 1 - f.coeff 2 ^ 2 / 3
/-- Shift-invariant coefficient `B` of a monic cubic. -/
noncomputable def Bq (f : ℝ[X]) : ℝ :=
  f.coeff 0 - f.coeff 2 * f.coeff 1 / 3 + 2 * f.coeff 2 ^ 3 / 27
/-- `disc / (18 A²)`. -/
noncomputable def Fv (A B : ℝ) : ℝ := (-4 * A ^ 3 - 27 * B ^ 2) / (18 * A ^ 2)

lemma conv3 (p q : ℝ[X]) : (p (⊞_3) q) =
    C (p.coeff 3 * q.coeff 3) * X ^ 3 + C (p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2) * X ^ 2
    + C (p.coeff 1 * q.coeff 3 + p.coeff 3 * q.coeff 1 + 2 / 3 * p.coeff 2 * q.coeff 2) * X
    + C (p.coeff 0 * q.coeff 3 + p.coeff 3 * q.coeff 0
        + (p.coeff 1 * q.coeff 2 + p.coeff 2 * q.coeff 1) / 3) := by
  ext m
  simp only [finiteAdditiveConvolution, coeff_smul, coeff_X_pow, smul_eq_mul,
    Finset.sum_range_succ, Finset.sum_range_zero, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, coeff_add, coeff_C_mul, coeff_X,
    coeff_C]
  rcases m with _ | _ | _ | _ | m <;> simp [Nat.factorial] <;> ring

lemma cubic_coeff (f : ℝ[X]) (α β γ δ : ℝ)
    (hf : f = C α * X ^ 3 + C β * X ^ 2 + C γ * X + C δ) :
    f.coeff 3 = α ∧ f.coeff 2 = β ∧ f.coeff 1 = γ ∧ f.coeff 0 = δ ∧
      ∀ N, 3 < N → f.coeff N = 0 := by
  subst hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [coeff_X_pow]
  · simp [coeff_X_pow]
  · simp [coeff_X_pow]
  · simp [coeff_X_pow, coeff_X, coeff_C]
  · intro N hN
    simp [coeff_X_pow, coeff_X, coeff_C, show N ≠ 3 by omega, show N ≠ 2 by omega,
      show (1 : ℕ) ≠ N by omega, show N ≠ 0 by omega]

lemma cubic_facts (g : ℝ[X]) (h3 : g.coeff 3 = 1) (hN : ∀ N, 3 < N → g.coeff N = 0) :
    g.Monic ∧ g.natDegree = 3 := by
  have hle : g.natDegree ≤ 3 := natDegree_le_iff_coeff_eq_zero.2 hN
  have hge : 3 ≤ g.natDegree := le_natDegree_of_ne_zero (by rw [h3]; exact one_ne_zero)
  have hn : g.natDegree = 3 := le_antisymm hle hge
  exact ⟨by rw [Monic, leadingCoeff, hn, h3], hn⟩

lemma cubic_eq (a b c : ℝ) : (X - C a) * (X - C b) * (X - C c) =
    C 1 * X ^ 3 + C (-(a + b + c)) * X ^ 2 + C (a * b + a * c + b * c) * X + C (-(a * b * c)) := by
  simp only [map_one, map_neg, map_add, map_mul]; ring

lemma factor3 (p : ℝ[X]) (hnd : p.natDegree = 3) (hc : p.roots.card = 3) (hm : p.Monic) :
    ∃ a b c : ℝ, p = (X - C a) * (X - C b) * (X - C c) := by
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hc, hnd])
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.1 hc
  refine ⟨a, b, c, ?_⟩
  rw [← h, habc]
  simp [mul_assoc]

lemma phi_cubic (a b c : ℝ) :
    1 / Φ ((X - C a) * (X - C b) * (X - C c)) = ENNReal.ofReal
      (2 * ((a - b) * (b - c) * (c - a)) ^ 2 / ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2) := by
  have hr : ((X - C a) * (X - C b) * (X - C c)).roots = a ::ₘ b ::ₘ {c} := by
    rw [roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
      (X_sub_C_ne_zero c)), roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, add_assoc, Multiset.singleton_add,
      Multiset.singleton_add]
  by_cases hd : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨hab, hac, hbc⟩ := hd
    have hnd : (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).Nodup := by
      simp [Multiset.nodup_cons, hab, hac, hbc]
    have hts : (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).toFinset = {a, b, c} := by
      rw [Multiset.toFinset_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    have ha : a ∉ ({b, c} : Finset ℝ) := by simp [hab, hac]
    have hin : ∀ i : ℝ, ∑ j ∈ ({a, b, c} : Finset ℝ).erase i, 1 / (i - j) =
        1 / (i - a) + (1 / (i - b) + 1 / (i - c)) := by
      intro i
      rw [Finset.sum_erase _ (by simp), Finset.sum_insert ha, Finset.sum_pair hbc]
    have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
    have h2 : b - c ≠ 0 := sub_ne_zero.2 hbc
    have h3 : c - a ≠ 0 := sub_ne_zero.2 (Ne.symm hac)
    have h1' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have h2' : c - b ≠ 0 := sub_ne_zero.2 (Ne.symm hbc)
    have h3' : a - c ≠ 0 := sub_ne_zero.2 hac
    have hP : (a - b) * (b - c) * (c - a) ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
    have hPpos : 0 < ((a - b) * (b - c) * (c - a)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hP))
    have hQpos : 0 < (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
      have : 0 < (a - b) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))
      have : 0 ≤ (b - c) ^ 2 := sq_nonneg _
      have : 0 ≤ (c - a) ^ 2 := sq_nonneg _
      linarith
    have hQ : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≠ 0 := ne_of_gt hQpos
    have hS : (1 / (a - a) + (1 / (a - b) + 1 / (a - c))) ^ 2 +
        ((1 / (b - a) + (1 / (b - b) + 1 / (b - c))) ^ 2 +
          (1 / (c - a) + (1 / (c - b) + 1 / (c - c))) ^ 2) =
        ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 / (2 * ((a - b) * (b - c) * (c - a)) ^ 2) := by
      simp only [sub_self]
      field_simp
      ring
    simp only [Φ, hr, if_pos hnd, hts]
    simp only [hin]
    rw [Finset.sum_insert ha, Finset.sum_pair hbc, hS]
    have hpos : 0 < ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 /
        (2 * ((a - b) * (b - c) * (c - a)) ^ 2) :=
      div_pos (pow_pos hQpos 2) (mul_pos two_pos hPpos)
    have he : (((((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 /
        (2 * ((a - b) * (b - c) * (c - a)) ^ 2))).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 /
        (2 * ((a - b) * (b - c) * (c - a)) ^ 2)) := rfl
    rw [he, one_div, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]
  · have hor : a = b ∨ a = c ∨ b = c := by tauto
    have hnd : ¬ (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).Nodup := by
      intro hn
      simp [Multiset.nodup_cons] at hn
      tauto
    have hW : 2 * ((a - b) * (b - c) * (c - a)) ^ 2 /
        ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 = 0 := by
      rcases hor with h | h | h <;> simp [h]
    simp only [Φ, hr, if_neg hnd, hW]
    simp

lemma aux_div (P Q : ℝ) : P / (18 * (-Q / 6) ^ 2) = 2 * P / Q ^ 2 := by ring

lemma inv_phi3 (f : ℝ[X]) (hm : f.Monic) (hn : f.natDegree = 3) (hc : f.roots.card = 3) :
    1 / Φ f = ENNReal.ofReal (Fv (Aq f) (Bq f)) ∧ Aq f ≤ 0 ∧ (Aq f = 0 → Bq f = 0) ∧
      0 ≤ Fv (Aq f) (Bq f) := by
  obtain ⟨a, b, c, rfl⟩ := factor3 f hn hc hm
  obtain ⟨-, e2, e1, e0, -⟩ := cubic_coeff _ _ _ _ _ (cubic_eq a b c)
  have hA : Aq ((X - C a) * (X - C b) * (X - C c)) =
      -((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 6 := by
    unfold Aq; rw [e2, e1]; ring
  have hD : -4 * Aq ((X - C a) * (X - C b) * (X - C c)) ^ 3 -
      27 * Bq ((X - C a) * (X - C b) * (X - C c)) ^ 2 = ((a - b) * (b - c) * (c - a)) ^ 2 := by
    unfold Aq Bq; rw [e2, e1, e0]; ring
  have hF : Fv (Aq ((X - C a) * (X - C b) * (X - C c))) (Bq ((X - C a) * (X - C b) * (X - C c)))
      = 2 * ((a - b) * (b - c) * (c - a)) ^ 2 / ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ^ 2 := by
    unfold Fv; rw [hD, hA, aux_div]
  have hQ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
  refine ⟨by rw [hF, phi_cubic], by rw [hA]; linarith, ?_, by rw [hF]; positivity⟩
  intro h0
  rw [hA] at h0
  have s1 := sq_nonneg (a - b)
  have s2 := sq_nonneg (b - c)
  have s3 := sq_nonneg (c - a)
  have q1 : (a - b) ^ 2 = 0 := by linarith
  have q2 : (b - c) ^ 2 = 0 := by linarith
  have r1 : a - b = 0 := (pow_eq_zero_iff two_ne_zero).1 q1
  have r2 : b - c = 0 := (pow_eq_zero_iff two_ne_zero).1 q2
  have hb : b = a := by linarith
  have hc' : c = a := by linarith
  unfold Bq; rw [e2, e1, e0, hb, hc']; ring

lemma card_ne_two (g : ℝ[X]) (hg : g.natDegree = 3) (hm : g.Monic) : g.roots.card ≠ 2 := by
  intro h2
  obtain ⟨r, s, hrs⟩ := Multiset.card_eq_two.1 h2
  obtain ⟨h, hh⟩ := prod_multiset_X_sub_C_dvd g
  have hg0 : g ≠ 0 := hm.ne_zero
  have hprod : (g.roots.map fun a => X - C a).prod = (X - C r) * (X - C s) := by
    rw [hrs]; simp
  rw [hprod] at hh
  have hrs0 : (X - C r) * (X - C s) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero s)
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh
    exact hg0 hh
  have hdeg : h.natDegree = 1 := by
    have := congrArg natDegree hh
    rw [natDegree_mul hrs0 hh0, natDegree_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero s),
      natDegree_X_sub_C, natDegree_X_sub_C, hg] at this
    omega
  obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one (degree_eq_iff_natDegree_eq hh0 |>.2 hdeg)
  have hroots : g.roots = (X - C r).roots + (X - C s).roots + h.roots := by
    conv_lhs => rw [hh]
    rw [roots_mul (hh ▸ hg0), roots_mul hrs0]
  have hcard : 1 ≤ Multiset.card h.roots :=
    Multiset.card_pos_iff_exists_mem.2 ⟨x, (mem_roots hh0).2 hx⟩
  rw [hroots, roots_X_sub_C, roots_X_sub_C] at h2
  simp only [Multiset.card_add, Multiset.card_singleton] at h2
  omega

lemma phi_small (g : ℝ[X]) (h : g.roots.card ≤ 1) : 1 / Φ g = ⊤ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · rw [Multiset.card_eq_zero] at h0
    simp [Φ, h0]
  · obtain ⟨r, hr⟩ := Multiset.card_eq_one.1 h1
    simp [Φ, hr]

lemma conv_ineq (A1 A2 x y : ℝ) (l1 : A1 < 0) (l2 : A2 < 0) :
    ((A1 * x + A2 * y) / (A1 + A2)) ^ 2 ≤ x ^ 2 + y ^ 2 := by
  have hs : 0 < (A1 + A2) ^ 2 := by
    have : A1 + A2 < 0 := by linarith
    rw [sq]; exact mul_pos_of_neg_of_neg this this
  rw [div_pow, div_le_iff₀ hs]
  have e : (x ^ 2 + y ^ 2) * (A1 + A2) ^ 2 - (A1 * x + A2 * y) ^ 2 =
      (A1 * y) ^ 2 + (A2 * x) ^ 2 + (A1 * A2) * ((x - y) ^ 2 + x ^ 2 + y ^ 2) := by ring
  have t1 := sq_nonneg (A1 * y)
  have t2 := sq_nonneg (A2 * x)
  have t3 : 0 ≤ (A1 * A2) * ((x - y) ^ 2 + x ^ 2 + y ^ 2) :=
    mul_nonneg (mul_pos_of_neg_of_neg l1 l2).le (by positivity)
  linarith

lemma key_ineq (A1 B1 A2 B2 : ℝ) (h1 : A1 ≤ 0) (h2 : A2 ≤ 0) (h1' : A1 = 0 → B1 = 0)
    (h2' : A2 = 0 → B2 = 0) :
    Fv A1 B1 + Fv A2 B2 ≤ Fv (A1 + A2) (B1 + B2) := by
  rcases eq_or_lt_of_le h1 with e1 | l1
  · rw [e1, h1' e1]; simp [Fv]
  rcases eq_or_lt_of_le h2 with e2 | l2
  · rw [e2, h2' e2]; simp [Fv]
  have hF : ∀ A B : ℝ, A < 0 → Fv A B = -2 * A / 9 - 3 / 2 * (B / A) ^ 2 := by
    intro A B hA
    have : A ≠ 0 := ne_of_lt hA
    unfold Fv; field_simp; ring
  have l3 : A1 + A2 < 0 := by linarith
  rw [hF _ _ l1, hF _ _ l2, hF _ _ l3]
  have n1 : A1 ≠ 0 := ne_of_lt l1
  have n2 : A2 ≠ 0 := ne_of_lt l2
  have hx : B1 = A1 * (B1 / A1) := by field_simp
  have hy : B2 = A2 * (B2 / A2) := by field_simp
  have hc := conv_ineq A1 A2 (B1 / A1) (B2 / A2) l1 l2
  rw [← hx, ← hy] at hc
  linarith

theorem four_3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  intro p q hpd hpc hqd hqc hpm hqm
  have hpn : p.natDegree = 3 := natDegree_eq_of_degree_eq_some hpd
  have hqn : q.natDegree = 3 := natDegree_eq_of_degree_eq_some hqd
  have hp3 : p.coeff 3 = 1 := by rw [← hpn]; exact hpm
  have hq3 : q.coeff 3 = 1 := by rw [← hqn]; exact hqm
  obtain ⟨g3, g2, g1, g0, gN⟩ := cubic_coeff _ _ _ _ _ (conv3 p q)
  obtain ⟨hgm, hgn⟩ := cubic_facts (p (⊞_3) q) (by rw [g3, hp3, hq3]; ring) gN
  have hA : Aq (p (⊞_3) q) = Aq p + Aq q := by
    unfold Aq; rw [g2, g1, hp3, hq3]; ring
  have hB : Bq (p (⊞_3) q) = Bq p + Bq q := by
    unfold Bq; rw [g2, g1, g0, hp3, hq3]; ring
  obtain ⟨ep, Ap, Bp, Fp⟩ := inv_phi3 p hpm hpn hpc
  obtain ⟨eqq, Aqq, Bqq, Fq⟩ := inv_phi3 q hqm hqn hqc
  have hle := card_roots' (p (⊞_3) q)
  rw [hgn] at hle
  have hcases : Multiset.card (p (⊞_3) q).roots = 3 ∨ Multiset.card (p (⊞_3) q).roots = 2 ∨
      Multiset.card (p (⊞_3) q).roots ≤ 1 := by omega
  rcases hcases with h3 | h2 | h1
  · obtain ⟨eg, -, -, -⟩ := inv_phi3 _ hgm hgn h3
    rw [ep, eqq, eg, ← ENNReal.ofReal_add Fp Fq]
    apply ENNReal.ofReal_le_ofReal
    rw [hA, hB]
    exact key_ineq _ _ _ _ Ap Aqq Bp Bqq
  · exact absurd h2 (card_ne_two _ hgn hgm)
  · rw [phi_small _ h1]
    exact le_top

end Arxiv.«2602.05192»

#print axioms Arxiv.«2602.05192».four_3
