import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset
import Mathlib.SetTheory.Cardinal.Arithmetic

open Cardinal Order
open scoped Cardinal

namespace Erdos1119

namespace WZ

open Filter Topology

/-- Two distinct entire functions agree only on a countable set. -/
theorem eqset_countable (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : f ≠ g) : {z : ℂ | f z = g z}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  rw [isDiscrete_iff_nhdsNE]
  intro x _
  by_contra hne
  have hfr : ∃ᶠ z in 𝓝[≠] x, f z = g z :=
    Filter.frequently_iff_neBot.mpr ⟨hne⟩
  exact hfg (AnalyticOnNhd.eq_of_frequently_eq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) hfr)

theorem core (m : Cardinal.{0}) (hm : ℵ₀ ≤ m) (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z₀ : ℂ, #{y : ℂ | ∃ f ∈ F, f z₀ = y} ≤ m) :
    #F ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨G, hGF, hG⟩ := le_mk_iff_exists_subset.mp (Order.succ_le_of_lt hlt)
  have hs0 : ℵ₀ ≤ succ m := hm.trans (Order.le_succ m)
  let ι := {p : G × G // p.1 ≠ p.2}
  let S : ι → Set ℂ := fun p => {z | (p.1.1 : ℂ → ℂ) z = (p.1.2 : ℂ → ℂ) z}
  have hS : ∀ p, #(S p) ≤ ℵ₀ := by
    intro p
    rw [le_aleph0_iff_set_countable]
    apply eqset_countable _ _ (hF _ (hGF p.1.1.2)) (hF _ (hGF p.1.2.2))
    intro h
    exact p.2 (Subtype.ext h)
  have hι : #ι ≤ succ m := by
    calc #ι ≤ #(G × G) := mk_subtype_le _
      _ = succ m := by rw [mk_prod, lift_id, hG, mul_eq_self hs0]
  have hE : #(⋃ p, S p) < 𝔠 := by
    calc #(⋃ p, S p) ≤ #ι * ⨆ p, #(S p) := mk_iUnion_le S
      _ ≤ succ m * succ m := mul_le_mul' hι ((ciSup_le' hS).trans hs0)
      _ = succ m := mul_eq_self hs0
      _ < 𝔠 := hsucc
  have hex : ∃ z₀ : ℂ, z₀ ∉ ⋃ p, S p := by
    by_contra h
    have h' : ∀ z : ℂ, z ∈ ⋃ p, S p := fun z => by
      by_contra hz
      exact h ⟨z, hz⟩
    have hle : #(Set.univ : Set ℂ) ≤ #(⋃ p, S p) := mk_le_mk_of_subset (fun z _ => h' z)
    rw [mk_univ_complex] at hle
    exact absurd hE (not_lt.mpr hle)
  obtain ⟨z₀, hz₀⟩ := hex
  have hinj : Function.Injective (fun g : G =>
      (⟨g.1 z₀, g.1, hGF g.2, rfl⟩ : {y : ℂ | ∃ f ∈ F, f z₀ = y})) := by
    intro a b hab
    by_contra hne
    apply hz₀
    rw [Set.mem_iUnion]
    exact ⟨⟨(a, b), hne⟩, congrArg Subtype.val hab⟩
  have hfin := (mk_le_of_injective hinj).trans (hval z₀)
  rw [hG] at hfin
  exact absurd hfin (not_le.mpr (Order.lt_succ m))

end WZ

theorem erdos_1119.variants.easy_case (m : Cardinal.{0}) (hm : ℵ₀ < m)
    (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z₀ : ℂ, #{y : ℂ | ∃ f ∈ F, f z₀ = y} ≤ m) :
    #F ≤ m :=
  WZ.core m hm.le hsucc F hF hval

theorem erdos_1119.variants.erdos_wetzel (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    F.Countable := by
  rw [← le_aleph0_iff_set_countable]
  have h0 : (ℵ_ 1 : Cardinal.{0}) < 𝔠 := by
    rw [← lift_lt.{0, u_1}, lift_continuum, lift_aleph, Ordinal.lift_one]
    exact h
  apply WZ.core ℵ₀ le_rfl (by rw [succ_aleph0]; exact h0) F hF
  intro z₀
  rw [le_aleph0_iff_set_countable]
  exact hval z₀

#print axioms erdos_1119.variants.easy_case
#print axioms erdos_1119.variants.erdos_wetzel

end Erdos1119
