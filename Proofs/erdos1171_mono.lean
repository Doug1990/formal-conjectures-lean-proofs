import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Exponential

open Cardinal Ordinal

universe u

/-- Restated from FormalConjecturesForMathlib/SetTheory/Ordinal/PartitionRelation.lean. -/
def OrdinalMultiColorRamsey (α β : Ordinal.{u}) (γ : Cardinal.{u}) (k : ℕ) : Prop :=
  ∀ col : Sym2 α.ToType → Fin (k + 1),
    (∃ A : Set α.ToType,
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = 0) ∧
      typeLT A = β) ∨
    (∃ (i : Fin k) (A : Set α.ToType),
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = i.succ) ∧
      #A = γ)

namespace Erdos1171

/-- Generic monotonicity in the number of small colours. -/
theorem mono_gen {α β : Ordinal.{u}} {γ : Cardinal.{u}} {j k : ℕ} (hγ : 1 < γ) (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey α β γ k) : OrdinalMultiColorRamsey α β γ j := by
  intro col
  have hle : j + 1 ≤ k + 1 := Nat.succ_le_succ hjk
  rcases hk (fun e => Fin.castLE hle (col e)) with ⟨A, hA, ht⟩ | ⟨i, A, hA, hc⟩
  · refine Or.inl ⟨A, fun x hx y hy hne => ?_, ht⟩
    have h := hA x hx y hy hne
    apply Fin.ext
    have h' := congrArg Fin.val h
    simpa using h'
  · -- the colour i.succ is the image of a colour of `col`, so i < j
    by_cases hA0 : ∃ x ∈ A, ∃ y ∈ A, x ≠ y
    · obtain ⟨x, hx, y, hy, hne⟩ := hA0
      have h := congrArg Fin.val (hA x hx y hy hne)
      simp only [Fin.val_castLE, Fin.val_succ] at h
      have hlt : (i : ℕ) < j := by
        have := (col s(x, y)).isLt
        omega
      refine Or.inr ⟨⟨i, hlt⟩, A, fun x' hx' y' hy' hne' => ?_, hc⟩
      have h2 := congrArg Fin.val (hA x' hx' y' hy' hne')
      simp only [Fin.val_castLE, Fin.val_succ] at h2
      apply Fin.ext
      simp only [Fin.val_succ]
      exact h2
    · -- A has at most one element, contradicting #A = γ > 1
      exfalso
      have hsub : A.Subsingleton := by
        intro x hx y hy
        by_contra hne
        exact hA0 ⟨x, hx, y, hy, hne⟩
      have h1 : #A ≤ 1 := Cardinal.mk_le_one_iff_set_subsingleton.mpr hsub
      rw [hc] at h1
      exact absurd h1 (not_le.mpr hγ)

universe v

/-- Order types are invariant under images along an order isomorphism, across universes. -/
theorem typeLT_image {X : Type u} {Y : Type v} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (e : X ≃o Y) (A : Set X) :
    Ordinal.lift.{v} (typeLT A) = Ordinal.lift.{u} (typeLT (e '' A)) := by
  let f : A ≃ (e '' A) := e.toEquiv.image A
  have g : ((· < ·) : A → A → Prop) ≃r ((· < ·) : (e '' A) → (e '' A) → Prop) :=
    ⟨f, fun {a b} => by
      show e a.1 < e b.1 ↔ a.1 < b.1
      exact e.lt_iff_lt⟩
  exact g.ordinal_lift_type_eq

/-- Universe transfer of `OrdinalMultiColorRamsey`. -/
theorem transfer {α β : Ordinal.{u}} {α' β' : Ordinal.{v}} {γ : Cardinal.{u}}
    {γ' : Cardinal.{v}} {k : ℕ}
    (hα : Ordinal.lift.{v} α = Ordinal.lift.{u} α')
    (hβ : Ordinal.lift.{v} β = Ordinal.lift.{u} β')
    (hγ : Cardinal.lift.{v} γ = Cardinal.lift.{u} γ')
    (h : OrdinalMultiColorRamsey α β γ k) : OrdinalMultiColorRamsey α' β' γ' k := by
  have key : Ordinal.lift.{v} (typeLT α.ToType) = Ordinal.lift.{u} (typeLT α'.ToType) := by
    rw [Ordinal.type_toType, Ordinal.type_toType]; exact hα
  obtain ⟨e₀⟩ := Ordinal.lift_type_eq.{u, v, 0}.mp key
  let e : α.ToType ≃o α'.ToType := OrderIso.ofRelIsoLT e₀
  intro col
  rcases h (fun s => col (s.map e)) with ⟨A, hA, ht⟩ | ⟨i, A, hA, hc⟩
  · refine Or.inl ⟨e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
      have := hA x hx y hy (fun h => hne (h ▸ rfl))
      simpa using this
    · have h1 := typeLT_image e A
      rw [ht, hβ] at h1
      exact (Ordinal.lift_inj.mp h1).symm
  · refine Or.inr ⟨i, e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
      have := hA x hx y hy (fun h => hne (h ▸ rfl))
      simpa using this
    · have h1 : Cardinal.lift.{v} #A = Cardinal.lift.{u} #(e '' A) :=
        Cardinal.lift_mk_eq'.mpr ⟨e.toEquiv.image A⟩
      rw [hc, hγ] at h1
      exact (Cardinal.lift_inj.mp h1).symm

namespace erdos_1171.variants

/--
`OrdinalMultiColorRamsey` is monotone in the number of non-zero colors:
a witness for the `k`-color version yields one for any `j ≤ k`.
-/
theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  refine mono_gen ?_ hjk (transfer ?_ ?_ ?_ hk)
  · exact_mod_cast (by decide : (1 : ℕ) < 3)
  · simp [pow_two, Ordinal.lift_omega]
  · simp [Ordinal.lift_omega]
  · simp

end erdos_1171.variants

end Erdos1171

#print axioms Erdos1171.erdos_1171.variants.mono_k
