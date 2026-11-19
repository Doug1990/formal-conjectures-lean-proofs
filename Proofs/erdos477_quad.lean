import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Polynomial Set

namespace Erdos477

/-- Core argument for a generic function `g k = a k² + b k + c` with `a ∣ b`, `a ≠ 0`. -/
theorem quad_core {a b c : ℤ} (ha : a ≠ 0) (hab : a ∣ b) (g : ℤ → ℤ)
    (hg : ∀ k, g k = a * k ^ 2 + b * k + c) (A : Set ℤ)
    (h : ∀ z, ∃! p ∈ A ×ˢ (Set.range g), z = p.1 + p.2) : False := by
  obtain ⟨m, rfl⟩ := hab
  have key : ∀ x ∈ A, ∀ y ∈ A, ∀ k k' : ℤ, x + g k = y + g k' → x = y := by
    intro x hx y hy k k' e
    have := (h (x + g k)).unique ⟨Set.mk_mem_prod hx ⟨k, rfl⟩, rfl⟩
      ⟨Set.mk_mem_prod hy ⟨k', rfl⟩, e⟩
    exact congrArg Prod.fst this
  have noncong : ∀ x ∈ A, ∀ y ∈ A, ∀ s : ℤ, x - y = 4 * a * s → x = y := by
    intro x hx y hy s hs
    rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · apply key x hx y hy (s - 1 - j) (1 + s - j)
      rw [hg, hg, hj]; linear_combination hs
    · apply key x hx y hy (-2 * s - j) (2 * s - j)
      rw [hg, hg, hj]; linear_combination hs
  have ha2 : 1 ≤ a ^ 2 := by
    rcases lt_or_gt_of_ne ha with h' | h' <;> nlinarith
  have hlow : ∀ z, ∃ x ∈ A, a * x ≤ a * z := by
    intro z
    obtain ⟨p, ⟨hp, hpz⟩, -⟩ := h (z + c - a * (a * m) ^ 2)
    obtain ⟨k, hk⟩ := hp.2
    refine ⟨p.1, hp.1, ?_⟩
    rw [hg] at hk
    have e1 : a * p.1 = a * (z + c - a * (a * m) ^ 2) - a * p.2 := by rw [hpz]; ring
    rw [← hk] at e1
    have e : 4 * (a * (a * k ^ 2 + a * m * k + c)) - 4 * a * c + (a * m) ^ 2
        = (2 * a * k + a * m) ^ 2 := by ring
    nlinarith [sq_nonneg (2 * a * k + a * m), sq_nonneg (a * m),
      mul_nonneg (sq_nonneg (a * m)) (sub_nonneg.mpr ha2)]
  have hseq : ∀ n : ℕ, ∀ z, ∃ s : Finset ℤ, (↑s : Set ℤ) ⊆ A ∧ s.card = n ∧
      ∀ x ∈ s, a * x ≤ a * z := by
    intro n
    induction n with
    | zero => intro z; exact ⟨∅, by simp, rfl, by simp⟩
    | succ n ih =>
      intro z
      obtain ⟨x, hx, hxz⟩ := hlow z
      obtain ⟨s, hsA, hsc, hsz⟩ := ih (x - a)
      have hxs : x ∉ s := fun hm => by have := hsz x hm; nlinarith
      refine ⟨insert x s, ?_, by rw [Finset.card_insert_of_notMem hxs, hsc], ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hsA hy
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxz
        · have := hsz y hy; nlinarith
  have hNeq : ((4 * a.natAbs : ℕ) : ℤ) = 4 * |a| := by
    push_cast; rfl
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hNpos : (0 : ℤ) < ((4 * a.natAbs : ℕ) : ℤ) := by rw [hNeq]; linarith
  obtain ⟨s, hsA, hsc, -⟩ := hseq (4 * a.natAbs + 1) 0
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := Finset.range (4 * a.natAbs)) (by rw [hsc, Finset.card_range]; omega)
    (f := fun x : ℤ => (x % ((4 * a.natAbs : ℕ) : ℤ)).toNat)
    (by
      intro x _
      simp only [Finset.coe_range, Set.mem_Iio]
      have h0 := Int.emod_nonneg x hNpos.ne'
      have h1 := Int.emod_lt_of_pos x hNpos
      have h2 := Int.toNat_of_nonneg h0
      omega)
  have hmod : x % ((4 * a.natAbs : ℕ) : ℤ) = y % ((4 * a.natAbs : ℕ) : ℤ) := by
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg x hNpos.ne')
    have h3 := Int.toNat_of_nonneg (Int.emod_nonneg y hNpos.ne')
    omega
  obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  rw [hNeq] at ht
  apply hne
  rcases abs_choice a with hc | hc
  · exact noncong x (hsA hx) y (hsA hy) t (by rw [ht, hc])
  · exact noncong x (hsA hx) y (hsA hy) (-t) (by rw [ht, hc]; ring)

theorem erdos_477.variants.degree_two_dvd_condition_b_ne_zero {a b c : ℤ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a ∣ b) :
    let f := a • X ^ 2 + b • X + C c
    ∀ A : Set ℤ, ∃ z, ¬ ∃! a ∈ A ×ˢ (Set.range f.eval), z = a.1 + a.2 := by
  intro f A
  by_contra h
  have h' : ∀ z, ∃! p ∈ A ×ˢ (Set.range f.eval), z = p.1 + p.2 := fun z => by
    by_contra hz; exact h ⟨z, hz⟩
  exact quad_core (a := a) (b := b) (c := c) ha hab f.eval
    (fun k => by simp [f]) A h'

end Erdos477

#print axioms Erdos477.erdos_477.variants.degree_two_dvd_condition_b_ne_zero
