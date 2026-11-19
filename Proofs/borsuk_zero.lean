import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.EMetricSpace.Diam

open Metric Bornology

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open scoped EuclideanGeometry

namespace Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

theorem borsuk_conjecture.zero : BorsukConjecture 0 := by
  intro s _ hs
  exfalso
  obtain ⟨x, -, y, -, hne⟩ := hs
  exact hne (PiLp.ext fun i => i.elim0)

end Borsuk

#print axioms Borsuk.borsuk_conjecture.zero
