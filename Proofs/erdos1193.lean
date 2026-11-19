import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Group.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Topology

/-! Definitions restated from FormalConjecturesForMathlib (Data/Set/Density.lean,
Algebra/Group/Indicator.lean, Combinatorics/Additive/Convolution.lean). -/
namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

variable {α R : Type*} [One R] [Zero R] (A : Set α)

noncomputable def indicatorOne : α → R := indicator A (fun _ ↦ 1)

scoped notation "𝟙_" A:max => indicatorOne A

end Set

namespace AdditiveCombinatorics

open Finset Set

variable {R : Type*} [Semiring R]

def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2

infixl:70 " ∗ " => sumConv

noncomputable def sumRep (A : Set ℕ) : ℕ → ℕ := (𝟙_A ∗ 𝟙_A)

end AdditiveCombinatorics

open AdditiveCombinatorics Set

namespace Erdos1193

namespace U

lemma ncard_Iio' (N : ℕ) : (Set.Iio N).ncard = N := by
  rw [show Set.Iio N = ((Finset.range N : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

lemma sumRep_univ' (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  unfold sumRep sumConv Set.indicatorOne
  simp

lemma set_eq : {n : ℕ | sumRep Set.univ n = n + 1} = Set.univ :=
  Set.eq_univ_of_forall (fun n => sumRep_univ' n)

lemma tend : Tendsto (fun b : ℕ => (Set.univ : Set ℕ).partialDensity Set.univ b)
    atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with b hb
  simp only [Set.partialDensity, Set.univ_inter, ncard_Iio']
  have : (b : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  rw [div_self this]

lemma lower : {n : ℕ | sumRep Set.univ n = n + 1}.lowerDensity = 1 := by
  rw [set_eq, Set.lowerDensity]; exact tend.liminf_eq

lemma upper : {n : ℕ | sumRep Set.univ n = n + 1}.upperDensity = 1 := by
  rw [set_eq, Set.upperDensity]; exact tend.limsup_eq

lemma mono : Monotone (fun n : ℕ => n + 1) := fun _ _ h => Nat.add_le_add_right h 1

end U

theorem erdos_1193.parts.i :
    ¬ ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.lowerDensity = 0 := by
  intro h
  have := h Set.univ (fun n => n + 1) U.mono (fun n => Nat.succ_pos n)
  rw [U.lower] at this
  norm_num at this

theorem erdos_1193.parts.ii :
    ¬ ∃ c < (1 : ℝ), ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.upperDensity < c := by
  rintro ⟨c, hc, h⟩
  have := h Set.univ (fun n => n + 1) U.mono (fun n => Nat.succ_pos n)
  rw [U.upper] at this
  linarith

theorem erdos_1193.variants.sumRep_univ (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 :=
  U.sumRep_univ' n

theorem erdos_1193.variants.upper_density_pos :
    ∃ (A : Set ℕ) (g : ℕ → ℕ), Monotone g ∧ (∀ n, 0 < g n) ∧
      0 < {n : ℕ | sumRep A n = g n}.upperDensity :=
  ⟨Set.univ, fun n => n + 1, U.mono, fun n => Nat.succ_pos n, by rw [U.upper]; norm_num⟩

end Erdos1193

#print axioms Erdos1193.erdos_1193.parts.i
#print axioms Erdos1193.erdos_1193.parts.ii
#print axioms Erdos1193.erdos_1193.variants.sumRep_univ
#print axioms Erdos1193.erdos_1193.variants.upper_density_pos
