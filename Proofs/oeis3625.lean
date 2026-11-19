import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

namespace OeisA3625

/-- A prime $p$ is in A003625 if $p \equiv 3, 5, \text{ or } 6 \pmod 7$. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6)

open Polynomial

namespace P

lemma irr_iff (F : Type*) [Field F] :
    Irreducible (X ^ 2 + X + 2 : F[X]) ↔ ∀ x : F, x ^ 2 + x + 2 ≠ 0 := by
  have hd : (X ^ 2 + X + 2 : F[X]).natDegree = 2 := by compute_degree!
  have h0 : (X ^ 2 + X + 2 : F[X]) ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  simp [mem_roots h0]

lemma root_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    (∃ x : F, x ^ 2 + x + 2 = 0) ↔ IsSquare (-7 : F) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * x + 1, by linear_combination (-4) * hx⟩
  · rintro ⟨r, hr⟩
    have hi : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
    refine ⟨(r - 1) * (2 : F)⁻¹, ?_⟩
    linear_combination (-((2 : F)⁻¹) ^ 2) * hr + ((-r - 3) * (2 : F)⁻¹ - 2) * hi

lemma sq7 : ∀ r : ℕ, r < 7 → r ≠ 0 →
    ((r = 3 ∨ r = 5 ∨ r = 6) ↔ ¬ IsSquare ((r : ℕ) : ZMod 7)) := by
  intro r hr h0
  unfold IsSquare
  interval_cases r <;> decide

instance fact7 : Fact (Nat.Prime 7) := ⟨by decide⟩

lemma legendre_neg_seven (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) (_h7 : p ≠ 7) :
    legendreSym p (-7) = legendreSym 7 p := by
  have hqr := legendreSym.quadratic_reciprocity' (p := 7) (q := p) (by decide) h2
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two h2)
  rw [show (-7 : ℤ) = (-1) * 7 by norm_num, legendreSym.mul, legendreSym.at_neg_one h2]
  push_cast at hqr
  rw [hqr, ZMod.χ₄_eq_neg_one_pow hodd, ← mul_assoc]
  rw [← pow_add, show p / 2 + 3 * (p / 2) = 2 * (2 * (p / 2)) by omega, pow_mul]
  norm_num

end P

theorem conjecture (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  have := Fact.mk hp
  rw [P.irr_iff]
  by_cases h2 : p = 2
  · subst h2
    constructor
    · rintro ⟨_, h⟩; omega
    · intro h; exact (h 0 (by rfl)).elim
  by_cases h7 : p = 7
  · subst h7
    constructor
    · rintro ⟨_, h⟩; omega
    · intro h; exact (h 3 (by rfl)).elim
  have h2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hall : (∀ x : ZMod p, x ^ 2 + x + 2 ≠ 0) ↔ ¬ IsSquare (-7 : ZMod p) := by
    rw [← P.root_iff _ h2']; simp
  rw [hall]
  have h7z : (((-7 : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h' : p ∣ 7 := by
      have := Int.natCast_dvd.mp h
      simpa using this
    exact h7 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h')
  have hsq : IsSquare (-7 : ZMod p) ↔ legendreSym 7 p = 1 := by
    rw [← P.legendre_neg_seven p h2 h7, legendreSym.eq_one_iff p h7z]
    push_cast; rfl
  have hr7 : p % 7 ≠ 0 := by
    intro h
    have : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact h7 ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp this).symm
  have hpz : (((p : ℤ)) : ZMod 7) ≠ 0 := by
    rw [Int.cast_natCast, ← ZMod.natCast_mod, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hr7) h
    have := Nat.mod_lt p (show 7 > 0 by decide)
    omega
  rw [hsq, legendreSym.eq_one_iff 7 hpz, Int.cast_natCast, ← ZMod.natCast_mod,
    ← P.sq7 (p % 7) (Nat.mod_lt p (by decide)) hr7]
  unfold A
  simp [hp]

end OeisA3625

#print axioms OeisA3625.conjecture
