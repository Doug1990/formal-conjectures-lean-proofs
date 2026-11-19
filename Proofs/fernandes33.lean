import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.QuotientGroup

namespace Arxiv.«2605.12342»

open Equiv Equiv.Perm

noncomputable def signDiffHom (m n : ℕ) : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)) * (sign.comp (MonoidHom.snd _ _))⁻¹

noncomputable def gammaSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) :=
  (signDiffHom m n).ker

section Generic
variable {G : Type*} [Group G]

lemma conj_mem (a t : G) (ht : t * t = 1) (hc : t * a * t = a⁻¹) {y : G}
    (hy : y ∈ Subgroup.zpowers a) : t * y * t ∈ Subgroup.zpowers a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h := map_zpow (MulAut.conj t) a k
  rw [MulAut.conj_apply, MulAut.conj_apply, hti] at h
  rw [h, hc]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) k

def dih (a t : G) (ht : t * t = 1) (hc : t * a * t = a⁻¹) : Subgroup G where
  carrier := {x | x ∈ Subgroup.zpowers a ∨ t * x ∈ Subgroup.zpowers a}
  one_mem' := Or.inl (Subgroup.one_mem _)
  mul_mem' := by
    have e : ∀ u v : G, u * v = u * t * (t * v) := fun u v => by
      rw [mul_assoc u t, ← mul_assoc t t, ht, one_mul]
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (Subgroup.mul_mem _ hx hy)
    · refine Or.inr ?_
      rw [← mul_assoc, e (t * x) y]
      exact Subgroup.mul_mem _ (conj_mem a t ht hc hx) hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact Subgroup.mul_mem _ hx hy
    · refine Or.inl ?_
      have : x * y = t * (t * x) * t * (t * y) := by
        rw [← e]; simp only [← mul_assoc, ht, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ (conj_mem a t ht hc hx) hy
  inv_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rintro x (hx | hx)
    · exact Or.inl (Subgroup.inv_mem _ hx)
    · refine Or.inr ?_
      have : t * x⁻¹ = t * (t * x)⁻¹ * t := by
        rw [mul_inv_rev, hti]; simp only [mul_assoc, ht, mul_one]
      rw [this]
      exact conj_mem a t ht hc (Subgroup.inv_mem _ hx)

lemma mem_dih (a t : G) (ht : t * t = 1) (hc : t * a * t = a⁻¹) (x : G) :
    x ∈ dih a t ht hc ↔ x ∈ Subgroup.zpowers a ∨ t * x ∈ Subgroup.zpowers a := Iff.rfl

lemma dih_card [Finite G] (a t : G) (ha : a ^ 3 = 1) (ht : t * t = 1) (hc : t * a * t = a⁻¹) :
    Nat.card (dih a t ht hc) ≤ 6 := by
  have hsub : (dih a t ht hc : Set G) ⊆
      (Subgroup.zpowers a : Set G) ∪ (fun x => t * x) '' (Subgroup.zpowers a : Set G) := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨t * x, hx, by simp only [← mul_assoc, ht, one_mul]⟩
  have hZ : (Subgroup.zpowers a : Set G).ncard ≤ 3 := by
    calc (Subgroup.zpowers a : Set G).ncard = Nat.card (Subgroup.zpowers a) :=
          (Nat.card_coe_set_eq _).symm
      _ = orderOf a := Nat.card_zpowers a
      _ ≤ 3 := orderOf_le_of_pow_eq_one (by omega) ha
  calc Nat.card (dih a t ht hc) = (dih a t ht hc : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ((Subgroup.zpowers a : Set G) ∪ (fun x => t * x) '' (Subgroup.zpowers a : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Subgroup.zpowers a : Set G).ncard
          + ((fun x => t * x) '' (Subgroup.zpowers a : Set G)).ncard := Set.ncard_union_le _ _
    _ ≤ 3 + 3 := add_le_add hZ ((Set.ncard_image_le (Set.toFinite _)).trans hZ)

theorem not_two_gen [Finite G] (N : Subgroup G)
    (h3 : ∀ a ∈ N, a ^ 3 = 1) (h2 : ∀ t ∉ N, t * t = 1)
    (hc : ∀ t ∉ N, ∀ a ∈ N, t * a * t = a⁻¹)
    (hi : ∀ s ∉ N, ∀ t ∉ N, s * t ∈ N)
    (hN : N ≠ ⊤) (hG : 6 < Nat.card G) (h₁ h₂ : G) :
    Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  intro htop
  have key : ∀ a t (ha : a ∈ N) (htN : t ∉ N), h₁ ∈ dih a t (h2 t htN) (hc t htN a ha) →
      h₂ ∈ dih a t (h2 t htN) (hc t htN a ha) → False := by
    intro a t ha htN m1 m2
    have hle : Subgroup.closure {h₁, h₂} ≤ dih a t (h2 t htN) (hc t htN a ha) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact m1
      · exact m2
    rw [htop, top_le_iff] at hle
    have := dih_card a t (h3 a ha) (h2 t htN) (hc t htN a ha)
    rw [hle, Subgroup.card_top] at this
    omega
  by_cases m1 : h₁ ∈ N <;> by_cases m2 : h₂ ∈ N
  · apply hN
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact m1
    · exact m2
  · exact key h₁ h₂ m1 m2 ((mem_dih _ _ _ _ _).2 (Or.inl (Subgroup.mem_zpowers _)))
      ((mem_dih _ _ _ _ _).2 (Or.inr (by rw [h2 h₂ m2]; exact Subgroup.one_mem _)))
  · exact key h₂ h₁ m2 m1
      ((mem_dih _ _ _ _ _).2 (Or.inr (by rw [h2 h₁ m1]; exact Subgroup.one_mem _)))
      ((mem_dih _ _ _ _ _).2 (Or.inl (Subgroup.mem_zpowers _)))
  · exact key (h₁ * h₂) h₁ (hi h₁ m1 h₂ m2) m1
      ((mem_dih _ _ _ _ _).2 (Or.inr (by rw [h2 h₁ m1]; exact Subgroup.one_mem _)))
      ((mem_dih _ _ _ _ _).2 (Or.inr (Subgroup.mem_zpowers _)))

end Generic

abbrev c3 : Perm (Fin 3) := swap 0 1 * swap 1 2
abbrev d3 : Perm (Fin 3) := swap 1 2 * swap 0 1

lemma perm3 : ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = c3 ∨ σ = d3 ∨ σ = swap 0 1 ∨ σ = swap 0 2 ∨
    σ = swap 1 2 := by decide

lemma sign_c3 : Equiv.Perm.sign c3 = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

lemma sign_d3 : Equiv.Perm.sign d3 = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

lemma even3 (σ : Perm (Fin 3)) (h : Equiv.Perm.sign σ = 1) : σ = 1 ∨ σ = c3 ∨ σ = d3 := by
  rcases perm3 σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  all_goals (rw [Equiv.Perm.sign_swap (by decide)] at h; exact absurd h (by decide))

lemma odd3 (σ : Perm (Fin 3)) (h : Equiv.Perm.sign σ ≠ 1) :
    σ = swap 0 1 ∨ σ = swap 0 2 ∨ σ = swap 1 2 := by
  rcases perm3 σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd Equiv.Perm.sign_one h
  · exact absurd sign_c3 h
  · exact absurd sign_d3 h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma P3 (σ : Perm (Fin 3)) (h : Equiv.Perm.sign σ = 1) : σ ^ 3 = 1 := by
  rcases even3 σ h with rfl | rfl | rfl <;> decide

lemma P2 (σ : Perm (Fin 3)) (h : Equiv.Perm.sign σ ≠ 1) : σ * σ = 1 := by
  rcases odd3 σ h with rfl | rfl | rfl <;> decide

lemma Pc (σ α : Perm (Fin 3)) (h : Equiv.Perm.sign σ ≠ 1) (h' : Equiv.Perm.sign α = 1) :
    σ * α * σ = α⁻¹ := by
  rcases odd3 σ h with rfl | rfl | rfl <;> rcases even3 α h' with rfl | rfl | rfl <;> decide

lemma memΓ (x : Perm (Fin 3) × Perm (Fin 3)) :
    x ∈ gammaSubgroup 3 3 ↔ Equiv.Perm.sign x.1 = Equiv.Perm.sign x.2 := by
  simp only [gammaSubgroup, signDiffHom, MonoidHom.mem_ker, MonoidHom.mul_apply,
    MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    mul_inv_eq_one]

noncomputable def N3 : Subgroup (gammaSubgroup 3 3) :=
  (Equiv.Perm.sign.comp ((MonoidHom.fst _ _).comp (gammaSubgroup 3 3).subtype)).ker

lemma memN (g : gammaSubgroup 3 3) : g ∈ N3 ↔ Equiv.Perm.sign g.1.1 = 1 := by
  rw [N3, MonoidHom.mem_ker]; rfl

lemma g3 : ∀ a ∈ N3, a ^ 3 = 1 := by
  intro a ha
  have hs : Equiv.Perm.sign a.1.1 = 1 := (memN a).1 ha
  have ht : Equiv.Perm.sign a.1.2 = 1 := by rw [← ((memΓ a.1).1 a.2)]; exact hs
  apply Subtype.ext; apply Prod.ext
  · simp [P3 _ hs]
  · simp [P3 _ ht]

lemma g2 : ∀ t ∉ N3, t * t = 1 := by
  intro t htN
  have hs : Equiv.Perm.sign t.1.1 ≠ 1 := fun h => htN ((memN t).2 h)
  have ht : Equiv.Perm.sign t.1.2 ≠ 1 := by rw [← ((memΓ t.1).1 t.2)]; exact hs
  apply Subtype.ext; apply Prod.ext
  · simp [P2 _ hs]
  · simp [P2 _ ht]

lemma gc : ∀ t ∉ N3, ∀ a ∈ N3, t * a * t = a⁻¹ := by
  intro t htN a ha
  have hs : Equiv.Perm.sign t.1.1 ≠ 1 := fun h => htN ((memN t).2 h)
  have ht : Equiv.Perm.sign t.1.2 ≠ 1 := by rw [← ((memΓ t.1).1 t.2)]; exact hs
  have as : Equiv.Perm.sign a.1.1 = 1 := (memN a).1 ha
  have at' : Equiv.Perm.sign a.1.2 = 1 := by rw [← ((memΓ a.1).1 a.2)]; exact as
  apply Subtype.ext; apply Prod.ext
  · simp [Pc _ _ hs as]
  · simp [Pc _ _ ht at']

lemma gi : ∀ s ∉ N3, ∀ t ∉ N3, s * t ∈ N3 := by
  intro s hsN t htN
  have hs : Equiv.Perm.sign s.1.1 ≠ 1 := fun h => hsN ((memN s).2 h)
  have ht : Equiv.Perm.sign t.1.1 ≠ 1 := fun h => htN ((memN t).2 h)
  rw [memN]
  show Equiv.Perm.sign (s.1.1 * t.1.1) = 1
  rw [Equiv.Perm.sign_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign s.1.1) with h | h
  · exact absurd h hs
  rcases Int.units_eq_one_or (Equiv.Perm.sign t.1.1) with h' | h'
  · exact absurd h' ht
  rw [h, h']; decide

lemma hN3 : N3 ≠ ⊤ := by
  intro h
  have hm : ((swap 0 1, swap 0 1) : Perm (Fin 3) × Perm (Fin 3)) ∈ gammaSubgroup 3 3 :=
    (memΓ _).2 rfl
  have hmem : (⟨_, hm⟩ : gammaSubgroup 3 3) ∈ N3 := by rw [h]; exact Subgroup.mem_top _
  have h2 : Equiv.Perm.sign (swap (0 : Fin 3) 1) = 1 := (memN _).1 hmem
  rw [Equiv.Perm.sign_swap (by decide)] at h2
  exact absurd h2 (by decide)

def emb (p : Perm (Fin 3) × Bool) : gammaSubgroup 3 3 :=
  ⟨(p.1, p.1 * (if p.2 then 1 else c3)), by
    rw [memΓ]
    show Equiv.Perm.sign p.1 = Equiv.Perm.sign (p.1 * _)
    rw [Equiv.Perm.sign_mul]
    split
    · simp
    · rw [sign_c3, mul_one]⟩

lemma emb_inj : Function.Injective emb := by
  rintro ⟨σ, b⟩ ⟨σ', b'⟩ h
  have h1 : σ = σ' := congrArg (fun g : gammaSubgroup 3 3 => g.1.1) h
  have h2 : σ * (if b then 1 else c3) = σ' * (if b' then 1 else c3) :=
    congrArg (fun g : gammaSubgroup 3 3 => g.1.2) h
  subst h1
  have h3 := mul_left_cancel h2
  cases b <;> cases b' <;> first | rfl | exact absurd h3 (by decide)

lemma card_gt : 6 < Nat.card (gammaSubgroup 3 3) := by
  have := Nat.card_le_card_of_injective emb emb_inj
  rw [Nat.card_eq_fintype_card (α := Perm (Fin 3) × Bool), Fintype.card_prod,
    Fintype.card_perm, Fintype.card_fin, Fintype.card_bool] at this
  have h6 : Nat.factorial 3 = 6 := rfl
  rw [h6] at this
  omega

theorem conjecture_1.variants.rank_3_3 :
    ∀ h₁ h₂ : gammaSubgroup 3 3, Subgroup.closure {h₁, h₂} ≠ ⊤ :=
  fun h₁ h₂ => not_two_gen N3 g3 g2 gc gi hN3 card_gt h₁ h₂

end Arxiv.«2605.12342»

#print axioms Arxiv.«2605.12342».conjecture_1.variants.rank_3_3
