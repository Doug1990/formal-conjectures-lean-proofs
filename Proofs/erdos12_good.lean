import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.Basic

open Filter Set

namespace Erdos12

abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

lemma key {p q r : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (h : p ∣ q ^ 2 + r ^ 2) : p ∣ q := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast at h
  by_contra hq
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq hq (eq_neg_of_add_eq_zero_left h) h3

theorem isGood_example :
    IsGood {p ^ 2 | (p : ℕ) (_ : p ≡ 3 [MOD 4]) (_ : p.Prime)} := by
  refine ⟨?_, ?_⟩
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
    obtain ⟨p, hpM, hp, hp3⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu M
    have h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hp3
    have hmem : p ^ 2 ∈ {p ^ 2 | (p : ℕ) (_ : p ≡ 3 [MOD 4]) (_ : p.Prime)} :=
      ⟨p, (ZMod.natCast_eq_natCast_iff _ _ _).1 h3, hp, rfl⟩
    have h1 := hM hmem
    have h2 : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    omega
  · rintro a ⟨p, hp3, hp, rfl⟩ b ⟨q, -, hq, rfl⟩ c ⟨r, -, hr, rfl⟩ hdvd hab hac
    exfalso
    have hpq : p ∣ q := key hp hp3 (dvd_trans (dvd_pow_self p two_ne_zero) hdvd)
    have := (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
    subst this
    exact lt_irrefl _ hab

end Erdos12

#print axioms Erdos12.isGood_example
