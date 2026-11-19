import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace LeinsterGroup

open DihedralGroup

open scoped Classical in
def IsLeinster (G : Type*) [Group G] [Fintype G] : Prop :=
  ∑ H : {H : Subgroup G // H.Normal}, Nat.card H = 2 * Fintype.card G

/-- In a finite cyclic group, two subgroups of the same order coincide. -/
lemma subgroup_eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (H K : Subgroup G) (h : Nat.card H = Nat.card K) : H = K := by
  classical
  have hdpos : 0 < Nat.card K := Nat.card_pos
  have hK : ∀ x : G, x ^ Nat.card K = 1 → x ∈ K := by
    intro x hx
    by_contra hxK
    have hsub : (insert x (Finset.univ.filter (fun y : G => y ∈ K))) ⊆
        Finset.univ.filter (fun y : G => y ^ Nat.card K = 1) := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · simpa using hx
      · rw [Finset.mem_filter] at hy ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 : ((⟨y, hy.2⟩ : K) ^ Nat.card K) = 1 := pow_card_eq_one'
        have h2 := congrArg Subtype.val h1
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have hcard := Finset.card_le_card hsub
    have hle := IsCyclic.card_pow_eq_one_le (α := G) hdpos
    rw [Finset.card_insert_of_notMem (by simpa using hxK)] at hcard
    have : (Finset.univ.filter (fun y : G => y ∈ K)).card = Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    omega
  have hle : H ≤ K := by
    intro x hx
    apply hK
    rw [← h]
    have h1 : ((⟨x, hx⟩ : H) ^ Nat.card H) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h])

variable {n : ℕ}

/-- Additive characters of `D_n` with values in `ZMod 2`. -/
def chiF (p : ZMod n →+ ZMod 2) (b : ZMod 2) : DihedralGroup n → ZMod 2
  | .r i => p i
  | .sr i => p i + b

lemma chiF_mul (p : ZMod n →+ ZMod 2) (b : ZMod 2) (g h : DihedralGroup n) :
    chiF p b (g * h) = chiF p b g + chiF p b h := by
  rcases g with i | i <;> rcases h with j | j <;>
    simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, chiF, map_add, map_sub] <;>
    (generalize p i = x; generalize p j = y; revert x y; revert b; decide)

def chi (p : ZMod n →+ ZMod 2) (b : ZMod 2) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (chiF p b g)
  map_one' := by rw [one_def]; simp [chiF]
  map_mul' g h := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [chiF_mul, ofAdd_add]

lemma mem_chi_ker (p : ZMod n →+ ZMod 2) (b : ZMod 2) (g : DihedralGroup n) :
    g ∈ (chi p b).ker ↔ chiF p b g = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

lemma card_ker {G : Type*} [Group G] [Finite G] (f : G →* Multiplicative (ZMod 2)) (g : G)
    (hg : f g = Multiplicative.ofAdd 1) : 2 * Nat.card f.ker = Nat.card G := by
  have hs : Function.Surjective f := by
    intro y
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h01 (Multiplicative.toAdd y) with h | h
    · exact ⟨1, by rw [map_one, ← ofAdd_toAdd y, h, ofAdd_zero]⟩
    · exact ⟨g, by rw [hg, ← h, ofAdd_toAdd]⟩
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hs,
    Subgroup.card_top, h2, mul_comm]

/-- The rotation subgroup. -/
abbrev R0 : Subgroup (DihedralGroup n) := (chi (0 : ZMod n →+ ZMod 2) 1).ker

lemma mem_R0_r (i : ZMod n) : r i ∈ (R0 : Subgroup (DihedralGroup n)) := by
  rw [mem_chi_ker]; simp [chiF]

lemma not_mem_R0_sr (i : ZMod n) : sr i ∉ (R0 : Subgroup (DihedralGroup n)) := by
  rw [mem_chi_ker]; simp [chiF]

lemma card_R0 [NeZero n] : Nat.card (R0 : Subgroup (DihedralGroup n)) = n := by
  have : 2 * Nat.card (R0 : Subgroup (DihedralGroup n)) = Nat.card (DihedralGroup n) :=
    card_ker (chi (0 : ZMod n →+ ZMod 2) 1) (sr 0) (by
    show Multiplicative.ofAdd (chiF _ _ _) = _
    simp [chiF])
  rw [nat_card] at this
  omega

lemma normal_of_le (H : Subgroup (DihedralGroup n)) (h : H ≤ R0) : H.Normal := by
  constructor
  intro x hx g
  cases x with
  | sr i => exact absurd (h hx) (not_mem_R0_sr i)
  | r i =>
    cases g with
    | r j =>
      have : r j * r i * (r j)⁻¹ = r i := by
        rw [inv_r, r_mul_r, r_mul_r]; congr 1; ring
      rw [this]; exact hx
    | sr j =>
      have : sr j * r i * (sr j)⁻¹ = (r i)⁻¹ := by
        rw [inv_sr, inv_r, sr_mul_r, sr_mul_sr]; congr 1; ring
      rw [this]; exact H.inv_mem hx

instance cyc_R0 [NeZero n] : IsCyclic (R0 : Subgroup (DihedralGroup n)) := by
  refine ⟨⟨⟨r 1, mem_R0_r 1⟩, fun x => ?_⟩⟩
  obtain ⟨x, hx⟩ := x
  cases x with
  | sr i => exact absurd hx (not_mem_R0_sr i)
  | r i =>
    refine ⟨(i.val : ℤ), ?_⟩
    apply Subtype.ext
    show (r 1 : DihedralGroup n) ^ (i.val : ℤ) = r i
    rw [r_one_zpow]
    congr 1
    simp

lemma eq_of_le [NeZero n] (H K : Subgroup (DihedralGroup n)) (hH : H ≤ R0) (hK : K ≤ R0)
    (h : Nat.card H = Nat.card K) : H = K := by
  classical
  have e1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have e2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have := subgroup_eq_of_card_eq (H.subgroupOf R0) (K.subgroupOf R0) (by rw [e1, e2, h])
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hH, inf_of_le_left hK] at this
  exact this

lemma top_of_sr (hodd : Odd n) (H : Subgroup (DihedralGroup n)) (hH : H.Normal) (i : ZMod n)
    (hi : sr i ∈ H) : H = ⊤ := by
  obtain ⟨m, hm⟩ := hodd
  have hu0 : (2 : ZMod n) * ((m + 1 : ℕ) : ZMod n) = 1 := by
    have h : ((2 * (m + 1) : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by congr 1; omega
    push_cast at h ⊢
    rw [h, ZMod.natCast_self, zero_add]
  obtain ⟨u, hu⟩ : ∃ u : ZMod n, 2 * u = 1 := ⟨_, hu0⟩
  have key : ∀ k : ZMod n, sr i * (r k * sr i * (r k)⁻¹) = r (-2 * k) := by
    intro k
    rw [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr]; congr 1; ring
  have hr : ∀ j : ZMod n, r j ∈ H := by
    intro j
    have h1 := H.mul_mem hi (hH.conj_mem _ hi (r (-(j * u))))
    rw [key] at h1
    have : r (-2 * -(j * u)) = (r j : DihedralGroup n) := by
      congr 1; linear_combination j * hu
    rwa [this] at h1
  rw [eq_top_iff]
  intro g _
  cases g with
  | r j => exact hr j
  | sr j =>
    have : r (i - j) * sr i = sr j := by rw [r_mul_sr]; congr 1; ring
    rw [← this]
    exact H.mul_mem (hr _) hi

open scoped Classical in
lemma sum_odd [NeZero n] (hodd : Odd n) :
    ∑ H : {H : Subgroup (DihedralGroup n) // H.Normal}, Nat.card H =
      2 * n + ∑ d ∈ n.divisors, d := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun H : {H : Subgroup (DihedralGroup n) // H.Normal} => H.1 ≤ R0)]
  have hnot : Finset.univ.filter
      (fun H : {H : Subgroup (DihedralGroup n) // H.Normal} => ¬ H.1 ≤ R0) =
      {⟨⊤, inferInstance⟩} := by
    ext ⟨H, hH⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Subtype.mk.injEq]
    constructor
    · intro h
      rw [SetLike.not_le_iff_exists] at h
      obtain ⟨g, hg, hgR⟩ := h
      cases g with
      | r i => exact absurd (mem_R0_r i) hgR
      | sr i => exact top_of_sr hodd H hH i hg
    · rintro rfl h
      exact not_mem_R0_sr 0 (h (Subgroup.mem_top _))
  rw [hnot, Finset.sum_singleton, Subgroup.card_top, nat_card, add_comm]
  congr 1
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H hH
    rw [Finset.mem_filter] at hH
    rw [Nat.mem_divisors]
    refine ⟨?_, NeZero.ne n⟩
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH.2).toEquiv
    rw [← e]
    conv_rhs => rw [← card_R0 (n := n)]
    exact Subgroup.card_subgroup_dvd_card _
  · intro H hH K hK h
    exact Subtype.ext (eq_of_le H.1 K.1 (Finset.mem_filter.1 hH).2 (Finset.mem_filter.1 hK).2 h)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨m, hm⟩, hne⟩ := hd
    have hmpos : m ≠ 0 := by rintro rfl; simp_all
    have hle : Subgroup.zpowers ((r 1 : DihedralGroup n) ^ m) ≤ R0 := by
      rw [Subgroup.zpowers_le, r_one_pow]; exact mem_R0_r _
    refine ⟨⟨Subgroup.zpowers ((r 1 : DihedralGroup n) ^ m), normal_of_le _ hle⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hle⟩, ?_⟩
    show Nat.card (Subgroup.zpowers _) = d
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hmpos
      (by rw [orderOf_r_one, hm]; exact Dvd.intro_left _ rfl), orderOf_r_one, hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
  · intro H _
    rfl

open scoped Classical in
lemma sum_even [NeZero n] (h2 : 2 ∣ n) :
    5 * n ≤ ∑ H : {H : Subgroup (DihedralGroup n) // H.Normal}, Nat.card H := by
  let p : ZMod n →+ ZMod 2 := (ZMod.castHom h2 (ZMod 2)).toAddMonoidHom
  have hp1 : p 1 = 1 := map_one (ZMod.castHom h2 (ZMod 2))
  have hp0 : p 0 = 0 := map_zero p
  let A : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨⊤, inferInstance⟩
  let B : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨R0, inferInstance⟩
  let C : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨(chi p 0).ker, inferInstance⟩
  let D : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨(chi p 1).ker, inferInstance⟩
  have cA : Nat.card A.1 = 2 * n := by
    show Nat.card (⊤ : Subgroup (DihedralGroup n)) = 2 * n
    rw [Subgroup.card_top, nat_card]
  have cB : Nat.card B.1 = n := card_R0
  have cC : 2 * Nat.card C.1 = 2 * n := by
    have := card_ker (chi p 0) (r 1) (by
      show Multiplicative.ofAdd (chiF _ _ _) = _
      simp [chiF, hp1])
    rw [nat_card] at this
    exact this
  have cD : 2 * Nat.card D.1 = 2 * n := by
    have := card_ker (chi p 1) (r 1) (by
      show Multiplicative.ofAdd (chiF _ _ _) = _
      simp [chiF, hp1])
    rw [nat_card] at this
    exact this
  have mA1 : r 1 ∈ A.1 := Subgroup.mem_top _
  have mA0 : sr 0 ∈ A.1 := Subgroup.mem_top _
  have mB1 : r 1 ∈ B.1 := mem_R0_r 1
  have mB0 : sr 0 ∉ B.1 := not_mem_R0_sr 0
  have mC1 : r 1 ∉ C.1 := by
    show r 1 ∉ (chi p 0).ker
    rw [mem_chi_ker]; simp [chiF, hp1]
  have mC0 : sr 0 ∈ C.1 := by
    show sr 0 ∈ (chi p 0).ker
    rw [mem_chi_ker]; simp [chiF, hp0]
  have mD1 : r 1 ∉ D.1 := by
    show r 1 ∉ (chi p 1).ker
    rw [mem_chi_ker]; simp [chiF, hp1]
  have mD0 : sr 0 ∉ D.1 := by
    show sr 0 ∉ (chi p 1).ker
    rw [mem_chi_ker]; simp [chiF, hp0]
  have hAB : A ≠ B := fun h => mB0 (h ▸ mA0)
  have hAC : A ≠ C := fun h => mC1 (h ▸ mA1)
  have hAD : A ≠ D := fun h => mD0 (h ▸ mA0)
  have hBC : B ≠ C := fun h => mC1 (h ▸ mB1)
  have hBD : B ≠ D := fun h => mD1 (h ▸ mB1)
  have hCD : C ≠ D := fun h => mD0 (h ▸ mC0)
  have hsub : Nat.card A.1 + (Nat.card B.1 + (Nat.card C.1 + Nat.card D.1)) ≤
      ∑ H : {H : Subgroup (DihedralGroup n) // H.Normal}, Nat.card H := by
    calc Nat.card A.1 + (Nat.card B.1 + (Nat.card C.1 + Nat.card D.1))
        = ∑ H ∈ ({A, B, C, D} : Finset _), Nat.card H.1 := by
          rw [Finset.sum_insert (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hAB, hAC, hAD⟩),
              Finset.sum_insert (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hBC, hBD⟩),
              Finset.sum_pair hCD]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem dihedral_is_leinster_iff_odd_perfect (n : ℕ) [NeZero n] :
    IsLeinster (DihedralGroup n) ↔ Nat.Perfect n ∧ Odd n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  unfold IsLeinster
  rw [DihedralGroup.card]
  rcases Nat.even_or_odd n with he | ho
  · have h2 : 2 ∣ n := even_iff_two_dvd.1 he
    have := sum_even h2
    constructor
    · intro h; omega
    · rintro ⟨_, ho⟩; exact absurd he (Nat.not_even_iff_odd.2 ho)
  · rw [sum_odd ho, Nat.perfect_iff_sum_divisors_eq_two_mul hn]
    constructor
    · intro h; exact ⟨by omega, ho⟩
    · rintro ⟨h, _⟩; omega

end LeinsterGroup

#print axioms LeinsterGroup.dihedral_is_leinster_iff_odd_perfect
