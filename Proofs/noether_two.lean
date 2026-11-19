import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.ComputeDegree

namespace NoetherProblem

class IsRationalExtension (K L ι : Type*)
    [Field K] [Field L] [Algebra K L] where
  pure_transcendental :
    Nonempty (L ≃ₐ[K] ((FractionRing (MvPolynomial ι K))))

def HasNoetherProperty (K L ι : Type) [Field K] [Field L] [Fintype ι]
    [Algebra K L] [IsRationalExtension K L ι] : Prop :=
  ∀ (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K)) (H : Subgroup (L ≃ₐ[K] L)),
    (∀ h ∈ H, ∃ σ : Equiv.Perm ι, h = (AlgEquiv.autCongr e).symm
      (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ))) →
    ∃ ι' : Type, IsRationalExtension K (IntermediateField.fixedField H) ι'

namespace NP2

open MvPolynomial IntermediateField

variable {K L ι : Type} [Field K] [Field L] [Algebra K L]
  (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K))

noncomputable def gH : MvPolynomial ι K →ₐ[K] L :=
  (e.symm : FractionRing (MvPolynomial ι K) →ₐ[K] L).comp
    (IsScalarTower.toAlgHom K (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)))

lemma gH_apply (q : MvPolynomial ι K) : gH e q = e.symm (algebraMap _ _ q) := rfl

lemma gH_injective : Function.Injective (gH e) := by
  intro a b h
  rw [gH_apply, gH_apply] at h
  exact IsFractionRing.injective (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
    (e.symm.injective h)

noncomputable def conj (σ : Equiv.Perm ι) : L ≃ₐ[K] L :=
  (AlgEquiv.autCongr e).symm (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ))

lemma conj_apply (σ : Equiv.Perm ι) (w : FractionRing (MvPolynomial ι K)) :
    conj e σ (e.symm w) =
      e.symm (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ) w) := by
  change e.symm (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ)
    (e (e.symm w))) = _
  rw [AlgEquiv.apply_symm_apply]

lemma conj_gH (σ : Equiv.Perm ι) (q : MvPolynomial ι K) :
    conj e σ (gH e q) = gH e (rename σ q) := by
  rw [gH_apply, conj_apply, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

lemma gen (M : IntermediateField K L) (hM : ∀ i, gH e (X i) ∈ M) : M = ⊤ := by
  have hpoly : ∀ q : MvPolynomial ι K, gH e q ∈ M := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have : (C c : MvPolynomial ι K) = algebraMap K _ c := rfl
      rw [this, AlgHom.commutes]
      exact M.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact M.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact M.mul_mem hp (hM i)
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι K) (e z)
  have : z = gH e a / gH e b := by
    rw [gH_apply, gH_apply, ← map_div₀, hab, AlgEquiv.symm_apply_apply]
  rw [this]
  exact M.div_mem (hpoly a) (hpoly b)

lemma ext_gen (f₁ f₂ : L ≃ₐ[K] L) (h : ∀ i, f₁ (gH e (X i)) = f₂ (gH e (X i))) :
    f₁ = f₂ := by
  let S : Subalgebra K L := AlgHom.equalizer (f₁ : L →ₐ[K] L) (f₂ : L →ₐ[K] L)
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    change f₁ x⁻¹ = f₂ x⁻¹
    rw [map_inv₀, map_inv₀]
    exact congrArg _ hx
  have htop := gen e (S.toIntermediateField hinv) (fun i => h i)
  ext z
  have hz : z ∈ S.toIntermediateField hinv := by rw [htop]; trivial
  exact hz

variable [Fintype ι]

lemma indep_esymm (h2 : Fintype.card ι = 2) :
    AlgebraicIndependent K (fun k : Fin 2 => (esymm ι K ((k : ℕ) + 1) : MvPolynomial ι K)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have : (aeval fun k : Fin 2 => (esymm ι K ((k : ℕ) + 1) : MvPolynomial ι K)) =
      (symmetricSubalgebra ι K).val.comp (esymmAlgHom ι K 2) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [esymmAlgHom]
  rw [this, AlgHom.coe_comp]
  exact Subtype.val_injective.comp (esymmAlgHom_injective K h2.ge)

lemma esymm_one_eq [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (hu : (Finset.univ : Finset ι) = {a, b}) :
    esymm ι K 1 = X a + X b := by
  rw [esymm_one, hu, Finset.sum_pair hab]

lemma esymm_two_eq [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (hu : (Finset.univ : Finset ι) = {a, b}) :
    esymm ι K 2 = X a * X b := by
  rw [esymm, hu, show (2 : ℕ) = ({a, b} : Finset ι).card from (Finset.card_pair hab).symm,
    Finset.powersetCard_self, Finset.sum_singleton, Finset.prod_pair hab]

theorem main (h2 : Fintype.card ι = 2) (H : Subgroup (L ≃ₐ[K] L))
    (hH : ∀ h ∈ H, ∃ σ : Equiv.Perm ι, h = conj e σ) :
    ∃ ι' : Type, IsRationalExtension K (fixedField H) ι' := by
  classical
  obtain ⟨a, b, hab, hu⟩ := (Finset.card_eq_two (s := (Finset.univ : Finset ι))).1
    (by rw [Finset.card_univ]; exact h2)
  have hmem : ∀ k : ι, k = a ∨ k = b := by
    intro k
    have : k ∈ (Finset.univ : Finset ι) := Finset.mem_univ k
    rw [hu] at this
    simpa using this
  by_cases htriv : ∀ h ∈ H, h = 1
  · have htop : fixedField H = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [mem_fixedField_iff]
      intro f hf
      rw [htriv f hf]
      rfl
    exact ⟨ι, ⟨⟨((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).trans e⟩⟩⟩
  simp only [not_forall] at htriv
  obtain ⟨τ, hτH, hτ1⟩ := htriv
  obtain ⟨σ, rfl⟩ := hH τ hτH
  have hσa : σ a = b := by
    by_contra hne
    have hfa : σ a = a := (hmem (σ a)).resolve_right hne
    have hfb : σ b = b := by
      rcases hmem (σ b) with h | h
      · exact absurd (σ.injective (h.trans hfa.symm)) hab.symm
      · exact h
    apply hτ1
    apply ext_gen e
    intro i
    rw [conj_gH, rename_X]
    rcases hmem i with h | h
    · rw [h, hfa]; rfl
    · rw [h, hfb]; rfl
  have hσb : σ b = a := by
    rcases hmem (σ b) with h | h
    · exact h
    · exact absurd (σ.injective (h.trans hσa.symm)) hab.symm
  have hτ2 : conj e σ ^ 2 = 1 := by
    apply ext_gen e
    intro i
    rw [pow_two, AlgEquiv.mul_apply, conj_gH, conj_gH, rename_X, rename_X]
    rcases hmem i with h | h
    · rw [h, hσa, hσb]; rfl
    · rw [h, hσb, hσa]; rfl
  have hord : orderOf (conj e σ) = 2 := orderOf_eq_prime hτ2 hτ1
  have hGcard : Nat.card (Subgroup.zpowers (conj e σ)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have : Finite (Subgroup.zpowers (conj e σ)) :=
    Nat.finite_of_card_ne_zero (by rw [hGcard]; norm_num)
  have := Fintype.ofFinite (Subgroup.zpowers (conj e σ))
  have hE : Module.finrank (fixedField (Subgroup.zpowers (conj e σ))) L = 2 := by
    rw [← hGcard, Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers (conj e σ)) L
  let v : Fin 2 → L := fun k => gH e (esymm ι K ((k : ℕ) + 1))
  have hind : AlgebraicIndependent K v := (indep_esymm h2).map' (gH_injective e)
  have hv0 : v 0 = gH e (X a) + gH e (X b) := by
    show gH e (esymm ι K 1) = _
    rw [esymm_one_eq hab hu, map_add]
  have hv1 : v 1 = gH e (X a) * gH e (X b) := by
    show gH e (esymm ι K 2) = _
    rw [esymm_two_eq hab hu, map_mul]
  have hfixv : ∀ σ' : Equiv.Perm ι, ∀ k, conj e σ' (v k) = v k := by
    intro σ' k
    show conj e σ' (gH e _) = gH e _
    rw [conj_gH]
    congr 1
    exact (esymm_isSymmetric ι K _) σ'
  have hSH : IntermediateField.adjoin K (Set.range v) ≤ fixedField H := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_fixedField_iff]
    intro f hf
    obtain ⟨σ', rfl⟩ := hH f hf
    exact hfixv σ' k
  have hHG : fixedField H ≤ fixedField (Subgroup.zpowers (conj e σ)) := by
    intro z hz
    rw [mem_fixedField_iff] at hz ⊢
    intro f hf
    exact hz f (Subgroup.zpowers_le.2 hτH hf)
  set S := IntermediateField.adjoin K (Set.range v) with hSdef
  have hv0S : v 0 ∈ S := IntermediateField.subset_adjoin K _ ⟨0, rfl⟩
  have hv1S : v 1 ∈ S := IntermediateField.subset_adjoin K _ ⟨1, rfl⟩
  have hadj : IntermediateField.adjoin S {gH e (X a)} = ⊤ := by
    have hx : gH e (X a) ∈ IntermediateField.adjoin S {gH e (X a)} :=
      IntermediateField.mem_adjoin_simple_self S _
    have hs : v 0 ∈ IntermediateField.adjoin S {gH e (X a)} :=
      (IntermediateField.adjoin S {gH e (X a)}).algebraMap_mem ⟨v 0, hv0S⟩
    have hy : gH e (X b) ∈ IntermediateField.adjoin S {gH e (X a)} := by
      have : gH e (X b) = v 0 - gH e (X a) := by rw [hv0]; ring
      rw [this]
      exact sub_mem hs hx
    have htop := gen e ((IntermediateField.adjoin S {gH e (X a)}).restrictScalars K) (by
      intro i
      rw [IntermediateField.mem_restrictScalars]
      rcases hmem i with h | h
      · rw [h]; exact hx
      · rw [h]; exact hy)
    rw [eq_top_iff]
    intro z _
    have : z ∈ (IntermediateField.adjoin S {gH e (X a)}).restrictScalars K := by
      rw [htop]; trivial
    exact (IntermediateField.mem_restrictScalars K).1 this
  let s0 : S := ⟨v 0, hv0S⟩
  let s1 : S := ⟨v 1, hv1S⟩
  let p : Polynomial S := Polynomial.X ^ 2 - Polynomial.C s0 * Polynomial.X + Polynomial.C s1
  have hp : Polynomial.aeval (gH e (X a)) p = 0 := by
    simp only [p, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show gH e (X a) ^ 2 - v 0 * gH e (X a) + v 1 = 0
    rw [hv0, hv1]
    ring
  have hpm : p.Monic := by
    simp only [p]
    monicity!
  have hpd : p.natDegree ≤ 2 := by
    simp only [p]
    compute_degree
  have hint : IsIntegral S (gH e (X a)) :=
    ⟨p, hpm, (Polynomial.aeval_def _ _).symm.trans hp⟩
  have hdeg : (minpoly S (gH e (X a))).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_natDegree (minpoly.min S _ hpm hp)).trans hpd
  have hfd : FiniteDimensional S L := by
    have h1 := IntermediateField.adjoin.finiteDimensional hint
    rw [hadj] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have hfr : Module.finrank S L ≤ 2 := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [hadj, IntermediateField.finrank_top'] at h1
    rw [h1]
    exact hdeg
  have hSG : S = fixedField (Subgroup.zpowers (conj e σ)) :=
    IntermediateField.eq_of_le_of_finrank_le' (hSH.trans hHG) (by rw [hE]; exact hfr)
  have hfinal : fixedField H = S := le_antisymm (hHG.trans hSG.ge) hSH
  exact ⟨Fin 2, ⟨⟨(IntermediateField.equivOfEq hfinal).trans hind.aevalEquivField.symm⟩⟩⟩

end NP2

theorem noether_problem.variants.two {K L ι : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 2) :
    HasNoetherProperty K L ι := by
  intro e H hH
  exact NP2.main e hι H hH

end NoetherProblem

#print axioms NoetherProblem.noether_problem.variants.two
