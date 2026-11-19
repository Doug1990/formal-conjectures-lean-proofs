import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

namespace Erdos338

open Filter

def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

namespace Bat

/-- Every multiset of elements of `A` splits into ones and a multiple of `h`. -/
lemma split (h : ℕ) (hh : 0 < h) (S : Multiset ℕ) (hS : ∀ x ∈ S, x ∈ insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) :
    ∃ n1 e c : ℕ, S.sum = n1 + h * e ∧ S.card = n1 + c ∧ (e ≠ 0 → 1 ≤ c) := by
  set F1 := S.filter (· = 1)
  set F2 := S.filter (fun x => ¬ x = 1)
  have hS' : F1 + F2 = S := Multiset.filter_add_not _ S
  have h1 : F1 = Multiset.replicate (Multiset.card F1) 1 := by
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun b hb => (Multiset.mem_filter.mp hb).2⟩
  have h2 : h ∣ F2.sum := by
    apply Multiset.dvd_sum
    intro x hx
    obtain ⟨hxS, hx1⟩ := Multiset.mem_filter.mp hx
    rcases hS x hxS with h' | h'
    · exact absurd h' hx1
    · exact h'.2
  obtain ⟨e, he⟩ := h2
  refine ⟨Multiset.card F1, e, Multiset.card F2, ?_, ?_, ?_⟩
  · rw [← hS', Multiset.sum_add, ← he]
    conv_lhs => rw [h1]
    simp
  · rw [← hS', Multiset.card_add]
  · intro he0
    by_contra hc
    have : F2 = 0 := by
      rw [← Multiset.card_eq_zero]; omega
    rw [this, Multiset.sum_zero] at he
    rcases Nat.mul_eq_zero.mp he.symm with h0 | h0
    · omega
    · exact he0 h0

/-- Lower bound for the order. -/
lemma lower (h : ℕ) (hh : 3 ≤ h) (k : ℕ)
    (hk : HasOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) k) : h ≤ k := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hk
  have hhM : M ≤ h * (M + 1) := by
    calc M ≤ M + 1 := Nat.le_succ M
      _ ≤ h * (M + 1) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨S, hSA, hSc, hSs⟩ := hM (h * (M + 1) + (h - 1)) (by omega)
  obtain ⟨n1, e, c, hs, hc, hec⟩ := split h (by omega) S hSA
  rw [hSs] at hs
  have hN : h * (M + 1 + 1) = h * (M + 1) + h := by ring
  have heN : e ≤ M + 1 := by
    by_contra hcon
    have : h * (M + 1 + 1) ≤ h * e := Nat.mul_le_mul_left _ (by omega)
    omega
  have h3 : h * e ≤ h * (M + 1) := Nat.mul_le_mul_left _ heN
  have h4 : h ≤ h * (M + 1) := Nat.le_mul_of_pos_right _ (by omega)
  by_cases he0 : e = 0
  · subst he0
    simp at hs
    omega
  · have := hec he0
    omega

lemma upper (h : ℕ) (hh : 3 ≤ h) : HasOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) h := by
  refine Filter.Eventually.of_forall fun m => ?_
  have hdm := Nat.div_add_mod m h
  have hlt : m % h < h := Nat.mod_lt _ (by omega)
  by_cases hq : m / h = 0
  · refine ⟨Multiset.replicate (m % h) 1, ?_, ?_, ?_⟩
    · intro x hx
      rw [Multiset.eq_of_mem_replicate hx]
      exact Set.mem_insert _ _
    · simp; omega
    · rw [hq] at hdm; simp; omega
  · refine ⟨(h * (m / h)) ::ₘ Multiset.replicate (m % h) 1, ?_, ?_, ?_⟩
    · intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · right
        exact ⟨Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hq), dvd_mul_right _ _⟩
      · rw [Multiset.eq_of_mem_replicate hx]
        exact Set.mem_insert _ _
    · simp; omega
    · simp; omega

lemma no_restricted (h : ℕ) (hh : 3 ≤ h) (t : ℕ) :
    ¬ HasRestrictedOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) t := by
  intro ht
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp ht
  have hhM : M ≤ h * (M + 1) := by
    calc M ≤ M + 1 := Nat.le_succ M
      _ ≤ h * (M + 1) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨S, hSA, -, hSs⟩ := hM (h * (M + 1) + 2) (by omega)
  have hdvd : h ∣ ∑ x ∈ S.erase 1, x := by
    apply Finset.dvd_sum
    intro x hx
    obtain ⟨hx1, hxS⟩ := Finset.mem_erase.mp hx
    rcases hSA x hxS with h' | h'
    · exact absurd h' hx1
    · exact h'.2
  obtain ⟨e, he⟩ := hdvd
  have hmod : (h * (M + 1) + 2) % h = 2 := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h1 : 1 ∈ S
  · rw [← Finset.add_sum_erase S _ h1, he] at hSs
    have : (1 + h * e) % h = 1 := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    rw [hSs] at this
    omega
  · rw [Finset.erase_eq_of_notMem h1] at he
    rw [he] at hSs
    have : (h * e) % h = 0 := Nat.mul_mod_right _ _
    rw [hSs] at this
    omega

end Bat

theorem erdos_338.variants.bateman (h : ℕ) (hh : 3 ≤ h) :
    basisOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) = h ∧
      ¬ ∃ t, HasRestrictedOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) t := by
  refine ⟨le_antisymm (iInf₂_le h (Bat.upper h hh)) (le_iInf₂ fun k hk => ?_), ?_⟩
  · exact_mod_cast Bat.lower h hh k hk
  · rintro ⟨t, ht⟩
    exact Bat.no_restricted h hh t ht

end Erdos338

#print axioms Erdos338.erdos_338.variants.bateman
