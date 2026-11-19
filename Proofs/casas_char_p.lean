import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

-- Proof of CasasAlvero.casas_alvero.positive_char_counterexample
-- (Paper/CasasAlvero.lean:161). Definitions and the used API lemma restated verbatim.

namespace CasasAlvero

open Polynomial

variable {K L : Type*} [Field K] [Field L] {f : K →+* L}

def HasCasasAlveroProp (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ¬ IsCoprime P (P.hasseDeriv i)

def HasCasasAlveroPropᵣ (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ∃ α : K, IsRoot P α ∧ IsRoot (P.hasseDeriv i) α

theorem HasCasasAlveroPropᵣ.hasCasasAlveroProp {P : K[X]}
    (hca : HasCasasAlveroPropᵣ P) : HasCasasAlveroProp P := by
  intro i hi coprime
  simp_rw [HasCasasAlveroPropᵣ, ← dvd_iff_isRoot] at hca
  have ⟨α, hα, hαi⟩ := hca i hi
  exact not_isUnit_X_sub_C _ (coprime.isUnit_of_dvd' hα hαi)

namespace CharPAux

variable (K) in
lemma natDeg {p : ℕ} : ((X ^ (p + 1) - X ^ p : K[X])).natDegree = p + 1 := by
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp

variable (K) in
lemma monic {p : ℕ} : ((X ^ (p + 1) - X ^ p : K[X])).Monic :=
  (monic_X_pow (p + 1)).sub_of_left
    (by rw [degree_X_pow, degree_X_pow]; exact_mod_cast Nat.lt_succ_self p)

lemma hasse (p i : ℕ) : hasseDeriv i (X ^ (p + 1) - X ^ p : K[X]) =
    monomial (p + 1 - i) (((p + 1).choose i : ℕ) : K) - monomial (p - i) ((p.choose i : ℕ) : K) := by
  rw [map_sub, X_pow_eq_monomial, X_pow_eq_monomial, hasseDeriv_monomial, hasseDeriv_monomial,
    mul_one, mul_one]

lemma generic {p : ℕ} [CharP K p] (hp : p.Prime) :
    let P : K[X] := X ^ (p + 1) - X ^ p
    Monic P ∧ HasCasasAlveroProp P ∧ ¬∃ α : K, P = (X - C α) ^ P.natDegree := by
  intro P
  have hd : P.natDegree = p + 1 := natDeg K
  have hp0 := hp.ne_zero
  refine ⟨monic K, HasCasasAlveroPropᵣ.hasCasasAlveroProp ?_, ?_⟩
  · intro i hi
    rw [hd, Finset.mem_range] at hi
    by_cases hip : i < p
    · refine ⟨0, ?_, ?_⟩
      · simp only [P, IsRoot, eval_sub, eval_pow, eval_X]
        rw [zero_pow (by omega), zero_pow hp0, sub_zero]
      · have h1 : p + 1 - i ≠ 0 := by omega
        have h2 : p - i ≠ 0 := by omega
        simp only [P]
        rw [hasse, IsRoot, eval_sub, eval_monomial, eval_monomial, zero_pow h1, zero_pow h2,
          mul_zero, mul_zero, sub_zero]
    · have hi' : i = p := by omega
      subst hi'
      refine ⟨1, ?_, ?_⟩
      · simp only [P, IsRoot, eval_sub, eval_pow, eval_X, one_pow, sub_self]
      · simp only [P]
        rw [hasse, IsRoot, eval_sub, eval_monomial, eval_monomial, one_pow, one_pow, mul_one,
          mul_one, Nat.choose_succ_self_right, Nat.choose_self, Nat.cast_succ, Nat.cast_one,
          CharP.cast_eq_zero K i, zero_add, sub_self]
  · rintro ⟨α, h⟩
    rw [hd] at h
    have h0 := congrArg (eval (0 : K)) h
    simp only [P, eval_sub, eval_pow, eval_X, eval_C] at h0
    rw [zero_pow (by omega), zero_pow hp0, sub_zero, zero_sub] at h0
    have hα : α = 0 := neg_eq_zero.1 ((pow_eq_zero_iff (n := p + 1) (by omega)).1 h0.symm)
    have h1 := congrArg (eval (1 : K)) h
    simp only [P, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, hα, sub_zero] at h1
    exact zero_ne_one h1

end CharPAux

theorem casas_alvero.positive_char_counterexample {p : ℕ} (hp : p.Prime) :
    ∃ (K : Type*) (_ : Field K) (_ : CharP K p),
      let P := X ^ (p + 1) - X ^ p
      Monic P ∧ HasCasasAlveroProp P ∧
      ¬∃ α : K, P = (X - C α) ^ P.natDegree := by
  have := Fact.mk hp
  exact ⟨ULift (ZMod p), inferInstance, inferInstance, CharPAux.generic hp⟩

end CasasAlvero

#print axioms CasasAlvero.casas_alvero.positive_char_counterexample
