import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.NormNum.Prime

open Filter

namespace Erdos436

def IsPowerResidue (k p a : ℕ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = a

noncomputable def r (k m p : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ∀ i < m, IsPowerResidue k p (n + i)), (n : ℕ∞)

noncomputable def runLimsup (k m : ℕ) : ℕ∞ :=
  limsup (r k m) (atTop ⊓ 𝓟 {p | p.Prime})

local notation "Λ" => runLimsup

namespace T22

lemma ne_zero_of_lt {p a : ℕ} [hp : Fact p.Prime] (h0 : 0 < a) (ha : a < p) :
    ((a : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma sq_iff {p : ℕ} (a : ZMod p) : (∃ x : ZMod p, x ^ 2 = a) ↔ IsSquare a := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx, sq]⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [hx, sq]⟩

lemma res_of {p a : ℕ} [Fact p.Prime] (h0 : 0 < a) (ha : a < p)
    (hs : IsSquare ((a : ℕ) : ZMod p)) : IsPowerResidue 2 p a :=
  ⟨ne_zero_of_lt h0 ha, (sq_iff _).2 hs⟩

lemma r_le {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) (hp : n + 1 < p)
    (h1 : IsSquare ((n : ℕ) : ZMod p)) (h2 : IsSquare ((n + 1 : ℕ) : ZMod p)) :
    r 2 2 p ≤ n := by
  refine iInf₂_le n ⟨hn, ?_⟩
  intro i hi
  interval_cases i
  · exact res_of (by omega) (by omega) (by simpa using h1)
  · exact res_of (by omega) (by omega) h2

lemma upper (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) : r 2 2 p ≤ 9 := by
  have := Fact.mk hp
  have hz : ∀ a : ℕ, 0 < a → a < p → ((a : ℕ) : ZMod p) ≠ 0 := fun a h0 ha =>
    ne_zero_of_lt h0 ha
  by_cases h2 : IsSquare ((2 : ℕ) : ZMod p)
  · exact (r_le (n := 1) le_rfl (by omega) ⟨1, by simp⟩ h2).trans (by norm_num)
  by_cases h5 : IsSquare ((5 : ℕ) : ZMod p)
  · exact (r_le (n := 4) (by norm_num) (by omega) ⟨2, by push_cast; norm_num⟩ h5).trans
      (by norm_num)
  have e2 := (ZMod.euler_criterion p (hz 2 (by norm_num) (by omega))).not.1 h2
  have e5 := (ZMod.euler_criterion p (hz 5 (by norm_num) (by omega))).not.1 h5
  have f2 := (ZMod.pow_div_two_eq_neg_one_or_one p (hz 2 (by norm_num) (by omega))).resolve_left e2
  have f5 := (ZMod.pow_div_two_eq_neg_one_or_one p (hz 5 (by norm_num) (by omega))).resolve_left e5
  have h10 : IsSquare ((10 : ℕ) : ZMod p) := by
    rw [ZMod.euler_criterion p (hz 10 (by norm_num) (by omega))]
    have : ((10 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) * ((5 : ℕ) : ZMod p) := by
      push_cast; norm_num
    rw [this, mul_pow, f2, f5]; norm_num
  exact r_le (n := 9) (by norm_num) (by omega) ⟨3, by push_cast; norm_num⟩ h10

lemma unit547 : IsUnit (547 : ZMod 840) :=
  ⟨⟨547, 43, by decide, by decide⟩, rfl⟩

lemma two_ns5 : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by decide

lemma lower (p : ℕ) (hp : p.Prime) (hmod : p % 840 = 547) : 9 ≤ r 2 2 p := by
  have := Fact.mk hp
  have h8 : p % 8 = 3 := by omega
  have h4 : p % 4 = 3 := by omega
  have p2 : p ≠ 2 := by omega
  -- 2 is a nonsquare
  have n2 : ¬ IsSquare ((2 : ℕ) : ZMod p) := by
    rw [Nat.cast_ofNat, ZMod.exists_sq_eq_two_iff p2]; omega
  -- 3 is a nonsquare
  have n3 : ¬ IsSquare ((3 : ℕ) : ZMod p) := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 (by norm_num) (by omega)]
    rw [not_not, ← ZMod.natCast_mod, show p % 3 = 1 by omega]
    exact ⟨1, by simp⟩
  -- 5 is a nonsquare
  have n5 : ¬ IsSquare ((5 : ℕ) : ZMod p) := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) p2]
    rw [← ZMod.natCast_mod, show p % 5 = 2 by omega]
    exact two_ns5
  -- 7 is a nonsquare
  have n7 : ¬ IsSquare ((7 : ℕ) : ZMod p) := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 (by norm_num) (by omega)]
    rw [not_not, ← ZMod.natCast_mod, show p % 7 = 1 by omega]
    exact ⟨1, by simp⟩
  -- 8 is a nonsquare
  have n8 : ¬ IsSquare ((8 : ℕ) : ZMod p) := by
    rintro ⟨x, hx⟩
    apply n2
    have h2z : ((2 : ℕ) : ZMod p) ≠ 0 := ne_zero_of_lt (by norm_num) (by omega)
    refine ⟨x * (2 : ZMod p)⁻¹, ?_⟩
    have h2z' : (2 : ZMod p) ≠ 0 := by simpa using h2z
    have : ((8 : ℕ) : ZMod p) = 2 * 2 * 2 := by push_cast; norm_num
    rw [this] at hx
    calc ((2 : ℕ) : ZMod p) = 2 * 2 * 2 * (2⁻¹ * 2⁻¹) := by
          push_cast; field_simp
      _ = x * 2⁻¹ * (x * 2⁻¹) := by rw [hx]; ring
  have nres : ∀ a : ℕ, ¬ IsSquare ((a : ℕ) : ZMod p) → ¬ IsPowerResidue 2 p a := by
    intro a ha h
    exact ha ((sq_iff _).1 h.2)
  refine le_iInf₂ ?_
  rintro n ⟨hn, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  simp only [Nat.add_zero] at h0
  by_contra hlt
  have : n ≤ 8 := by
    by_contra h'
    exact hlt (by exact_mod_cast (show 9 ≤ n by omega))
  interval_cases n
  · exact nres 2 n2 h1
  · exact nres 2 n2 h0
  · exact nres 3 n3 h0
  · exact nres 5 n5 h1
  · exact nres 5 n5 h0
  · exact nres 7 n7 h1
  · exact nres 7 n7 h0
  · exact nres 8 n8 h0

end T22

theorem erdos_436.variants.two_two : Λ 2 2 = 9 := by
  apply le_antisymm
  · refine limsup_le_of_le (h := ?_)
    rw [eventually_inf_principal, eventually_atTop]
    exact ⟨11, fun p hp hpr => T22.upper p hpr hp⟩
  · apply le_limsup_of_frequently_le'
    intro h
    rw [eventually_inf_principal, eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod T22.unit547 N
    have hmod : p % 840 = 547 := by
      have := (ZMod.natCast_eq_natCast_iff' p 547 840).1 (by simpa using hpa)
      simpa using this
    exact hN p hpN.le hp (T22.lower p hp hmod)

end Erdos436

#print axioms Erdos436.erdos_436.variants.two_two
