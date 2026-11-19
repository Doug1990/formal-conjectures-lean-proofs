import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

namespace Erdos443

def A (m : ℕ) : Finset ℕ := (Finset.Icc 1 (m / 2)).image fun k => k * (m - k)

namespace H

lemma mem (p q D : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hD : (2*p+1)*(2*q+1) = D) :
    4*p*q*(p+1)*(q+1) ∈ A (D-1) ∩ A (D+1) := by
  have hD' : 4*(p*q) + 2*p + 2*q + 1 = D := by rw [← hD]; ring
  have ht : 1 ≤ p*q := by
    have := Nat.mul_le_mul hp (le_trans hp hpq); simpa using this
  simp only [A, Finset.mem_inter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · refine ⟨2*(p*q)+2*p, ⟨by omega, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    · have e : D - 1 - (2*(p*q)+2*p) = 2*(p*q)+2*q := by omega
      rw [e]; ring
  · refine ⟨2*(p*q), ⟨by omega, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    · have e : D + 1 - 2*(p*q) = 2*(p*q)+2*p+2*q+2 := by omega
      rw [e]; ring

lemma injZ (p q p' q' : ℤ) (hp : 0 ≤ p) (hp' : 0 ≤ p') (h1 : p ≤ q) (h2 : p' ≤ q')
    (hD : 2*(p*q) + p + q = 2*(p'*q') + p' + q')
    (hV : 4*p*q*(p+1)*(q+1) = 4*p'*q'*(p'+1)*(q'+1)) : p = p' := by
  have h4 : 4*((p*q - p'*q') * (p*q - p'*q' - (p'+q') - 1)) = 0 := by
    linear_combination (-1)*hV + 4*(p*q)*hD
  have h0 : (p*q - p'*q') * (p*q - p'*q' - (p'+q') - 1) = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · norm_num at h
    · exact h
  have hpq : 0 ≤ p*q := mul_nonneg hp (le_trans hp h1)
  have hpq' : 0 ≤ p'*q' := mul_nonneg hp' (le_trans hp' h2)
  have ht : p*q = p'*q' := by
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exfalso; linarith
  have hr : p + q = p' + q' := by linarith
  have h3 : (p - p') * (p - q') = 0 := by linear_combination p*hr - ht
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith

lemma injN (p q p' q' : ℕ) (h1 : p ≤ q) (h2 : p' ≤ q')
    (hD : (2*p+1)*(2*q+1) = (2*p'+1)*(2*q'+1))
    (hV : 4*p*q*(p+1)*(q+1) = 4*p'*q'*(p'+1)*(q'+1)) : p = p' := by
  have e1 : (2*p+1)*(2*q+1) = 2*(2*(p*q)+p+q) + 1 := by ring
  have e2 : (2*p'+1)*(2*q'+1) = 2*(2*(p'*q')+p'+q') + 1 := by ring
  have hDn : 2*(p*q)+p+q = 2*(p'*q')+p'+q' := by omega
  have hDz : (2*(p*q)+p+q : ℤ) = 2*(p'*q')+p'+q' := by exact_mod_cast hDn
  have hVz : (4*p*q*(p+1)*(q+1) : ℤ) = 4*p'*q'*(p'+1)*(q'+1) := by exact_mod_cast hV
  have := injZ (p : ℤ) q p' q' (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast h1) (by exact_mod_cast h2) hDz hVz
  exact_mod_cast this

end H

theorem erdos_443.parts.i :
    ∀ s : ℕ, ∃ m n : ℕ, n < m ∧ s ≤ (A n ∩ A m).card := by
  intro s
  have hD1 : 1 ≤ 3^(2*s+1) := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨3^(2*s+1)+1, 3^(2*s+1)-1, by omega, ?_⟩
  set P : ℕ → ℕ := fun i => 3^i / 2 with hP
  set Q : ℕ → ℕ := fun i => 3^(2*s+1-i) / 2 with hQ
  have facts : ∀ i ∈ Finset.Icc 1 s, 1 ≤ P i ∧ P i ≤ Q i ∧
      (2*P i+1)*(2*Q i+1) = 3^(2*s+1) ∧ 2*P i + 1 = 3^i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have eP : 2*P i + 1 = 3^i :=
      Nat.two_mul_div_two_add_one_of_odd (Odd.pow (by decide))
    have eQ : 2*Q i + 1 = 3^(2*s+1-i) :=
      Nat.two_mul_div_two_add_one_of_odd (Odd.pow (by decide))
    have l1 : 3^1 ≤ 3^i := Nat.pow_le_pow_right (by norm_num) hi.1
    have l2 : 3^i ≤ 3^(2*s+1-i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, by omega, ?_, eP⟩
    rw [eP, eQ, ← pow_add]
    congr 1; omega
  let V : ℕ → ℕ := fun i => 4*P i*Q i*(P i+1)*(Q i+1)
  have hinj : Set.InjOn V (Finset.Icc 1 s : Set ℕ) := by
    intro i hi j hj hij
    obtain ⟨-, a1, a2, a3⟩ := facts i hi
    obtain ⟨-, b1, b2, b3⟩ := facts j hj
    have := H.injN (P i) (Q i) (P j) (Q j) a1 b1 (a2.trans b2.symm) hij
    have e : 3^i = 3^j := by rw [← a3, ← b3, this]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) e
  have hsub : (Finset.Icc 1 s).image V ⊆ A (3^(2*s+1)-1) ∩ A (3^(2*s+1)+1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨a0, a1, a2, -⟩ := facts i hi
    exact H.mem (P i) (Q i) _ a0 a1 a2
  calc s = (Finset.Icc 1 s).card := by simp
    _ = ((Finset.Icc 1 s).image V).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

end Erdos443

#print axioms Erdos443.erdos_443.parts.i
