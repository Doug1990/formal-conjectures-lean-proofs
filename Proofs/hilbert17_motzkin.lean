import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Common

open Real MvPolynomial

namespace Hilbert17

noncomputable def f : MvPolynomial (Fin 2) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 4 - 3 * X 0 ^ 2 * X 1 ^ 2 + 1

lemma int_aux (B p q x y : ℤ) (hB : 0 ≤ B) (hx : 0 ≤ x) (hyB : y < B)
    (h : B * p + x ≤ B * q + y) : p ≤ q := by
  by_contra hc
  have hc' : q + 1 ≤ p := by omega
  have h1 := mul_le_mul_of_nonneg_left hc' hB
  have h2 : B * (q + 1) = B * q + B := by ring
  linarith

lemma core {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (κ : (Fin 2 →₀ ℕ) → ℤ)
    (hadd : ∀ a b, κ (a + b) = κ a + κ b) (m : Fin 2 →₀ ℕ)
    (hmax : ∀ i a, coeff a (S i) ≠ 0 → κ a ≤ κ m)
    (hinj : ∀ i a, coeff a (S i) ≠ 0 → κ a = κ m → a = m)
    (j : Fin n) (hj : coeff m (S j) ≠ 0) :
    0 < coeff (m + m) (∑ i, S i ^ 2) := by
  rw [coeff_sum]
  have h : ∀ i, coeff (m + m) (S i ^ 2) = coeff m (S i) ^ 2 := by
    intro i
    rw [pow_two, coeff_mul, Finset.sum_eq_single (m, m)]
    · rw [pow_two]
    · intro x hx hne
      rw [Finset.mem_antidiagonal] at hx
      by_contra hc
      have h1 : coeff x.1 (S i) ≠ 0 := left_ne_zero_of_mul hc
      have h2 : coeff x.2 (S i) ≠ 0 := right_ne_zero_of_mul hc
      have e := hadd x.1 x.2
      rw [hx, hadd] at e
      have l1 := hmax i _ h1
      have l2 := hmax i _ h2
      have q1 : x.1 = m := hinj i _ h1 (by linarith)
      have q2 : x.2 = m := hinj i _ h2 (by linarith)
      exact hne (Prod.ext q1 q2)
    · intro h
      exact (h (Finset.mem_antidiagonal.2 rfl)).elim
  simp only [h]
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))⟩

lemma newton {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (w0 w1 K : ℤ) (hw1 : w1 ≠ 0)
    (hf : ∀ m : Fin 2 →₀ ℕ, 2 * K < w0 * (m 0 : ℤ) + w1 * (m 1 : ℤ) →
      coeff m (∑ i, S i ^ 2) = 0) :
    ∀ i a, coeff a (S i) ≠ 0 → w0 * (a 0 : ℤ) + w1 * (a 1 : ℤ) ≤ K := by
  classical
  intro i a ha
  by_contra hlt
  rw [not_le] at hlt
  let φ : (Fin 2 →₀ ℕ) → ℤ := fun x => w0 * (x 0 : ℤ) + w1 * (x 1 : ℤ)
  let T : Finset (Σ _ : Fin n, Fin 2 →₀ ℕ) :=
    (Finset.univ : Finset (Fin n)).sigma (fun i => (S i).support)
  have memT : ∀ i x, coeff x (S i) ≠ 0 → (⟨i, x⟩ : Σ _ : Fin n, Fin 2 →₀ ℕ) ∈ T :=
    fun i x hx => Finset.mem_sigma.2 ⟨Finset.mem_univ _, mem_support_iff.2 hx⟩
  let B : ℕ := T.sup (fun p => p.2 0 + p.2 1) + 1
  have hB : ∀ i x, coeff x (S i) ≠ 0 → x 0 < B ∧ x 1 < B := by
    intro i x hx
    have := Finset.le_sup (f := fun p : (Σ _ : Fin n, Fin 2 →₀ ℕ) => p.2 0 + p.2 1)
      (memT i x hx)
    simp only at this
    omega
  let κ : (Fin 2 →₀ ℕ) → ℤ := fun x => (B : ℤ) * φ x + (x 0 : ℤ)
  have hadd : ∀ a b, κ (a + b) = κ a + κ b := by
    intro a b
    simp only [κ, φ, Finsupp.add_apply, Nat.cast_add]
    ring
  obtain ⟨⟨j, m⟩, hm, hmax⟩ := Finset.exists_max_image T (fun p => κ p.2) ⟨_, memT i a ha⟩
  have hjm : coeff m (S j) ≠ 0 := mem_support_iff.1 (Finset.mem_sigma.1 hm).2
  have hmax' : ∀ i x, coeff x (S i) ≠ 0 → κ x ≤ κ m := fun i x hx => hmax _ (memT i x hx)
  have hBm := hB j m hjm
  have hphi : φ a ≤ φ m := by
    have hBa := hB i a ha
    exact int_aux B (φ a) (φ m) (a 0) (m 0) (by positivity) (by positivity)
      (by exact_mod_cast hBm.1) (hmax' i a ha)
  have hinj : ∀ i x, coeff x (S i) ≠ 0 → κ x = κ m → x = m := by
    intro i x hx he
    have hBx := hB i x hx
    have p1 := int_aux B (φ x) (φ m) (x 0) (m 0) (by positivity) (by positivity)
      (by exact_mod_cast hBm.1) he.le
    have p2 := int_aux B (φ m) (φ x) (m 0) (x 0) (by positivity) (by positivity)
      (by exact_mod_cast hBx.1) he.ge
    have hp : φ x = φ m := le_antisymm p1 p2
    have he' : (B : ℤ) * φ x + (x 0 : ℤ) = (B : ℤ) * φ m + (m 0 : ℤ) := he
    rw [hp] at he'
    have hx0 : (x 0 : ℤ) = m 0 := by linarith
    have hw : w0 * (x 0 : ℤ) = w0 * (m 0 : ℤ) := by rw [hx0]
    have hp' : w0 * (x 0 : ℤ) + w1 * (x 1 : ℤ) = w0 * (m 0 : ℤ) + w1 * (m 1 : ℤ) := hp
    have h1 : w1 * (x 1 : ℤ) = w1 * (m 1 : ℤ) := by linarith
    have h1' : (x 1 : ℤ) = m 1 := mul_left_cancel₀ hw1 h1
    ext k
    fin_cases k
    · exact_mod_cast hx0
    · exact_mod_cast h1'
  have hpos := core S κ hadd m hmax' hinj j hjm
  have hz := hf (m + m) (by
    have : φ (m + m) = φ m + φ m := by
      simp only [φ, Finsupp.add_apply, Nat.cast_add]; ring
    have h2 : w0 * ((m + m) 0 : ℤ) + w1 * ((m + m) 1 : ℤ) = φ (m + m) := rfl
    rw [h2, this]
    have : φ a = w0 * (a 0 : ℤ) + w1 * (a 1 : ℤ) := rfl
    linarith)
  linarith

lemma coord (m : Fin 2 →₀ ℕ) (a b : ℕ) :
    (Finsupp.single 0 a + Finsupp.single 1 b = m) ↔ (m 0 = a ∧ m 1 = b) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext k
    fin_cases k <;> simp [h0, h1]

lemma coord0 (m : Fin 2 →₀ ℕ) : ((0 : Fin 2 →₀ ℕ) = m) ↔ (m 0 = 0 ∧ m 1 = 0) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext k
    fin_cases k <;> simp [h0, h1]

lemma coeff_f (m : Fin 2 →₀ ℕ) :
    coeff m f = (if m 0 = 4 ∧ m 1 = 2 then 1 else 0) + (if m 0 = 2 ∧ m 1 = 4 then 1 else 0)
      - 3 * (if m 0 = 2 ∧ m 1 = 2 then 1 else 0) + (if m 0 = 0 ∧ m 1 = 0 then 1 else 0) := by
  have e3 : (3 : MvPolynomial (Fin 2) ℝ) = C 3 := (map_ofNat C 3).symm
  simp only [f, e3, mul_assoc, X_pow_eq_monomial, monomial_mul, one_mul, coeff_add,
    coeff_sub, coeff_C_mul, coeff_monomial, coeff_one, coord, coord0]

theorem f_not_sum_of_squares :
    ¬∃ (n : ℕ) (hn : 0 < n) (S : Fin n → MvPolynomial (Fin 2) ℝ), f = ∑ i, S i ^ 2 := by
  rintro ⟨n, -, S, hS⟩
  have hC := newton S (-2) 1 0 one_ne_zero (by
    intro m hm
    rw [← hS, coeff_f]
    split_ifs <;> first | ring1 | (exfalso; omega))
  have hD := newton S 1 (-2) 0 (by norm_num) (by
    intro m hm
    rw [← hS, coeff_f]
    split_ifs <;> first | ring1 | (exfalso; omega))
  have hE := newton S 1 1 3 one_ne_zero (by
    intro m hm
    rw [← hS, coeff_f]
    split_ifs <;> first | ring1 | (exfalso; omega))
  set s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hs
  have hval : coeff (s + s) f = -3 := by
    rw [coeff_f]
    simp [hs]
  have hsq : ∀ i, coeff (s + s) (S i ^ 2) = coeff s (S i) ^ 2 := by
    intro i
    rw [pow_two, coeff_mul, Finset.sum_eq_single (s, s)]
    · rw [pow_two]
    · intro x hx hne
      rw [Finset.mem_antidiagonal] at hx
      by_contra hc
      have h1 : coeff x.1 (S i) ≠ 0 := left_ne_zero_of_mul hc
      have h2 : coeff x.2 (S i) ≠ 0 := right_ne_zero_of_mul hc
      have c1 := hC i _ h1
      have c2 := hC i _ h2
      have d1 := hD i _ h1
      have d2 := hD i _ h2
      have e1 := hE i _ h1
      have e2 := hE i _ h2
      have x0 : x.1 0 + x.2 0 = 2 := by
        have := congrArg (fun g : Fin 2 →₀ ℕ => g 0) hx
        simpa [hs] using this
      have x1 : x.1 1 + x.2 1 = 2 := by
        have := congrArg (fun g : Fin 2 →₀ ℕ => g 1) hx
        simpa [hs] using this
      have q1 : x.1 = s := by
        rw [hs]; exact ((coord x.1 1 1).2 ⟨by omega, by omega⟩).symm
      have q2 : x.2 = s := by
        rw [hs]; exact ((coord x.2 1 1).2 ⟨by omega, by omega⟩).symm
      exact hne (Prod.ext q1 q2)
    · intro h
      exact (h (Finset.mem_antidiagonal.2 rfl)).elim
  have hnn : 0 ≤ coeff (s + s) (∑ i, S i ^ 2) := by
    rw [coeff_sum]
    exact Finset.sum_nonneg fun i _ => by rw [hsq]; exact sq_nonneg _
  rw [← hS, hval] at hnn
  norm_num at hnn

end Hilbert17

#print axioms Hilbert17.f_not_sum_of_squares
