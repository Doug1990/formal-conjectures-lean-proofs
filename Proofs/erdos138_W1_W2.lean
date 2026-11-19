import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Nat

variable {α : Type*} [AddCommMonoid α]

def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

namespace Erdos138

def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

lemma single_isAP (a : ℕ) : Set.IsAPOfLength ({a} : Set ℕ) 1 := by
  refine ⟨a, 0, ?_, ?_⟩
  · have h : ({a} : Set ℕ).encard = 1 := Set.encard_singleton a
    exact h
  · ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul, mul_zero, add_zero]
    constructor
    · rintro rfl; exact ⟨0, by norm_num, rfl⟩
    · rintro ⟨n, _, rfl⟩; rfl

lemma one_point {M : Set ℕ} {ap : Set M} (h : ((·.1) '' ap).IsAPOfLength (1 : ℕ)) :
    ∃ m, m ∈ ap := by
  obtain ⟨a, d, hc, -⟩ := h
  have h1 : ((·.1) '' ap).encard = 1 := by exact_mod_cast hc
  obtain ⟨x, hs⟩ := Set.encard_eq_one.1 h1
  have hx : x ∈ (·.1) '' ap := by rw [hs]; simp
  obtain ⟨m, hm, -⟩ := hx
  exact ⟨m, hm⟩

lemma mono_single {M : Set ℕ} {κ : Type} [Finite κ] (col : M → κ) (p : M) :
    ContainsMonoAPofLength col 1 := by
  refine ⟨col p, {p}, ?_, ?_⟩
  · rw [Set.image_singleton]
    have h := single_isAP p.1
    exact_mod_cast h
  · intro x hx
    rw [Set.mem_singleton_iff.1 hx]

theorem monoAPNumber_two_one : W 1 = 1 := by
  have h1 : 1 ∈ monoAP_guarantee_set 2 1 := fun coloring =>
    mono_single coloring ⟨1, by simp⟩
  apply le_antisymm (Nat.sInf_le h1)
  refine le_csInf ⟨1, h1⟩ fun N hN => ?_
  by_contra hlt
  have hN0 : N = 0 := by omega
  subst hN0
  obtain ⟨c, ap, hap, -⟩ := hN (fun _ => 0)
  obtain ⟨m, -⟩ := one_point hap
  have := m.2
  simp at this

lemma pair_isAP {a b : ℕ} (hab : a < b) : Set.IsAPOfLength ({a, b} : Set ℕ) 2 := by
  refine ⟨a, b - a, ?_, ?_⟩
  · have h : ({a, b} : Set ℕ).encard = 2 := Set.encard_pair hab.ne
    exact h
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by rw [zero_mul, add_zero]⟩
      · exact ⟨1, by norm_num, by rw [one_mul]; omega⟩
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < 2 := by exact_mod_cast hn
      interval_cases n
      · left; rw [zero_mul, add_zero]
      · right; rw [one_mul]; omega

lemma two_points {M : Set ℕ} {ap : Set M} (h : ((·.1) '' ap).IsAPOfLength (2 : ℕ)) :
    ∃ m₁ ∈ ap, ∃ m₂ ∈ ap, m₁.1 ≠ m₂.1 := by
  obtain ⟨a, d, hc, -⟩ := h
  have h2 : ((·.1) '' ap).encard = 2 := by exact_mod_cast hc
  obtain ⟨x, y, hxy, hs⟩ := Set.encard_eq_two.1 h2
  have hx : x ∈ (·.1) '' ap := by rw [hs]; simp
  have hy : y ∈ (·.1) '' ap := by rw [hs]; simp
  obtain ⟨m₁, h₁, rfl⟩ := hx
  obtain ⟨m₂, h₂, rfl⟩ := hy
  exact ⟨m₁, h₁, m₂, h₂, hxy⟩

lemma mono_pair {M : Set ℕ} {κ : Type} [Finite κ] (col : M → κ) (p q : M)
    (hpq : p.1 < q.1) (h : col p = col q) : ContainsMonoAPofLength col 2 := by
  refine ⟨col p, {p, q}, ?_, ?_⟩
  · rw [Set.image_pair]
    have h := pair_isAP hpq
    exact_mod_cast h
  · rintro x (rfl | rfl)
    · rfl
    · exact h.symm

lemma three_mem : 3 ∈ monoAP_guarantee_set 2 2 := by
  intro coloring
  have key : ∀ x y z : Fin 2, x ≠ y → x ≠ z → y = z := by decide
  have m1 : (1 : ℕ) ∈ Finset.Icc 1 3 := by simp
  have m2 : (2 : ℕ) ∈ Finset.Icc 1 3 := by simp
  have m3 : (3 : ℕ) ∈ Finset.Icc 1 3 := by simp
  by_cases h12 : coloring ⟨1, m1⟩ = coloring ⟨2, m2⟩
  · exact mono_pair coloring ⟨1, m1⟩ ⟨2, m2⟩ (by norm_num) h12
  by_cases h13 : coloring ⟨1, m1⟩ = coloring ⟨3, m3⟩
  · exact mono_pair coloring ⟨1, m1⟩ ⟨3, m3⟩ (by norm_num) h13
  exact mono_pair coloring ⟨2, m2⟩ ⟨3, m3⟩ (by norm_num) (key _ _ _ h12 h13)

lemma not_mem_of_le_two {N : ℕ} (hN : N ≤ 2) : N ∉ monoAP_guarantee_set 2 2 := by
  intro hmem
  obtain ⟨c, ap, hap, hcol⟩ :=
    hmem (fun x => if x.1 = 1 then (0 : Fin 2) else 1)
  obtain ⟨p, hp, q, hq, hpq⟩ := two_points hap
  have hp' := Finset.mem_Icc.1 (Finset.mem_coe.1 p.2)
  have hq' := Finset.mem_Icc.1 (Finset.mem_coe.1 q.2)
  have cp := hcol p hp
  have cq := hcol q hq
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  dsimp only at cp cq
  by_cases e1 : p.1 = 1 <;> by_cases e2 : q.1 = 1
  · exact hpq (e1.trans e2.symm)
  · rw [if_pos e1] at cp
    rw [if_neg e2] at cq
    exact h01 (cp.trans cq.symm)
  · rw [if_neg e1] at cp
    rw [if_pos e2] at cq
    exact h01 (cq.trans cp.symm)
  · exact hpq (by omega)

theorem monoAPNumber_two_two : W 2 = 3 := by
  apply le_antisymm (Nat.sInf_le three_mem)
  refine le_csInf ⟨3, three_mem⟩ fun N hN => ?_
  by_contra hlt
  exact not_mem_of_le_two (by omega) hN

end Erdos138

#print axioms Erdos138.monoAPNumber_two_one
#print axioms Erdos138.monoAPNumber_two_two
