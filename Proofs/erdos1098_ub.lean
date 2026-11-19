import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Group

namespace Erdos1098

/-- The non-commuting graph (restated from the checkout). -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm.symm := fun _ _ h => h.symm

theorem erdos_1098.variants.upper_bound (G : Type*) [Group G]
    [(Subgroup.center G).FiniteIndex] :
    (nonCommutingGraph G).CliqueFree ((Subgroup.center G).index + 1) := by
  intro t ht
  classical
  have hfin : Finite (G ⧸ Subgroup.center G) := Subgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (G ⧸ Subgroup.center G)
  have hinj : Set.InjOn (fun x : G => (x : G ⧸ Subgroup.center G)) (t : Set G) := by
    intro x hx y hy hxy
    by_contra hne
    have hadj := ht.isClique hx hy hne
    apply hadj
    have hmem : x⁻¹ * y ∈ Subgroup.center G := QuotientGroup.eq.mp hxy
    have hc := Subgroup.mem_center_iff.mp hmem x
    calc x * y = x * (x * (x⁻¹ * y)) := by group
      _ = x * ((x⁻¹ * y) * x) := by rw [hc]
      _ = y * x := by group
  have h1 : t.card ≤ (Finset.univ : Finset (G ⧸ Subgroup.center G)).card :=
    Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
  have h2 : Fintype.card (G ⧸ Subgroup.center G) = (Subgroup.center G).index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [Finset.card_univ, h2, ht.card_eq] at h1
  omega

end Erdos1098

#print axioms Erdos1098.erdos_1098.variants.upper_bound
