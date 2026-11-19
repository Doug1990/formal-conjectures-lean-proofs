import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.SetLike.Fintype

namespace LeinsterGroup

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

open scoped Classical in
/-- For a cyclic group the sum of orders of normal subgroups is `σ(n)`. -/
lemma sum_cyclic (G : Type*) [Group G] [Fintype G] [IsCyclic G] :
    ∑ H : {H : Subgroup G // H.Normal}, Nat.card H = ∑ d ∈ (Fintype.card G).divisors, d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    rw [Nat.mem_divisors]
    refine ⟨?_, Fintype.card_ne_zero⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H _ K _ hHK
    exact Subtype.ext (subgroup_eq_of_card_eq H.1 K.1 hHK)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨m, hm⟩, hne⟩ := hd
    have hmpos : m ≠ 0 := by
      rintro rfl; simp_all
    refine ⟨⟨Subgroup.zpowers (g ^ m), ?_⟩, Finset.mem_univ _, ?_⟩
    · constructor
      intro x hx y
      have hc : ∀ a b : G, a * b = b * a := fun a b =>
        (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
      rw [hc y x, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · simp only
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hmpos, hg, Nat.card_eq_fintype_card, hm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
      rw [hg, Nat.card_eq_fintype_card, hm]
      exact Dvd.intro_left _ rfl
  · intro H _
    rfl

theorem cyclic_of_perfect_is_leinster (G : Type*) [Group G] [Fintype G]
    [IsCyclic G] (h_perfect : Nat.Perfect (Fintype.card G)) :
    IsLeinster G := by
  unfold IsLeinster
  have hn := (Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos).mp h_perfect
  rw [← hn]
  exact sum_cyclic G

/-- Sum of orders of cyclic subgroups `⟨g⟩` (each counted once) exceeds `|G|` when `G` is
nontrivial: fibres of `g ↦ ⟨g⟩` inside each subgroup, and `1` is never a generator of a
nontrivial cyclic subgroup. -/
lemma card_lt_sum_zpowers (G : Type*) [Group G] [Fintype G] [DecidableEq (Subgroup G)]
    (g₀ : G) (hg₀ : g₀ ≠ 1) :
    Fintype.card G < ∑ H ∈ Finset.univ.image (fun g : G => Subgroup.zpowers g), Nat.card H := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image (fun g : G => Subgroup.zpowers g)]
  apply Finset.sum_lt_sum
  · intro H _
    calc (Finset.univ.filter fun x : G => Subgroup.zpowers x = H).card
        ≤ (Finset.univ.filter fun x : G => x ∈ H).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          refine ⟨hx.1, ?_⟩
          rw [← hx.2]
          exact Subgroup.mem_zpowers x
      _ = Nat.card H := by
          rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  · refine ⟨Subgroup.zpowers g₀, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    calc (Finset.univ.filter fun x : G => Subgroup.zpowers x = Subgroup.zpowers g₀).card
        ≤ ((Finset.univ.filter fun x : G => x ∈ Subgroup.zpowers g₀).erase 1).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨?_, hx.1, ?_⟩
          · rintro rfl
            have h1 : g₀ ∈ Subgroup.zpowers (1 : G) := by
              rw [hx.2]; exact Subgroup.mem_zpowers g₀
            rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
            exact hg₀ h1
          · rw [← hx.2]; exact Subgroup.mem_zpowers x
      _ < (Finset.univ.filter fun x : G => x ∈ Subgroup.zpowers g₀).card := by
          apply Finset.card_erase_lt_of_mem
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, one_mem _⟩
      _ = Nat.card (Subgroup.zpowers g₀) := by
          rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]

open scoped Classical in
lemma two_mul_lt_of_not_cyclic (G : Type*) [CommGroup G] [Fintype G] (h : ¬ IsCyclic G) :
    2 * Fintype.card G < ∑ H : {H : Subgroup G // H.Normal}, Nat.card H := by
  have hnt : ∃ g₀ : G, g₀ ≠ 1 := by
    by_contra hc
    push Not at hc
    apply h
    exact ⟨⟨1, fun x => ⟨0, by simp [hc x]⟩⟩⟩
  obtain ⟨g₀, hg₀⟩ := hnt
  set T := Finset.univ.image (fun g : G => Subgroup.zpowers g) with hT
  have htop : (⊤ : Subgroup G) ∉ T := by
    intro hm
    rw [hT, Finset.mem_image] at hm
    obtain ⟨g, _, hg⟩ := hm
    exact h ⟨⟨g, fun x => Subgroup.mem_zpowers_iff.1 (by rw [hg]; exact Subgroup.mem_top x)⟩⟩
  have hlt := card_lt_sum_zpowers G g₀ hg₀
  rw [← hT] at hlt
  have hS : ∑ H ∈ insert ⊤ T, Nat.card H = Fintype.card G + ∑ H ∈ T, Nat.card H := by
    rw [Finset.sum_insert htop, Subgroup.card_top, Nat.card_eq_fintype_card]
  let φ : Subgroup G ↪ {H : Subgroup G // H.Normal} :=
    ⟨fun H => ⟨H, Subgroup.normal_of_isMulCommutative H⟩, fun a b hab => congrArg Subtype.val hab⟩
  have hle : ∑ H ∈ insert ⊤ T, Nat.card H ≤ ∑ H : {H : Subgroup G // H.Normal}, Nat.card H := by
    calc ∑ H ∈ insert ⊤ T, Nat.card H
        = ∑ H ∈ (insert ⊤ T).map φ, Nat.card H.1 := by rw [Finset.sum_map]; rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem abelian_is_leinster_iff_cyclic_perfect (G : Type*) [CommGroup G] [Fintype G] :
    IsLeinster G ↔ IsCyclic G ∧ Nat.Perfect (Fintype.card G) := by
  constructor
  · intro hL
    have hc : IsCyclic G := by
      by_contra hc
      have := two_mul_lt_of_not_cyclic G hc
      unfold IsLeinster at hL
      omega
    refine ⟨hc, ?_⟩
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos]
    unfold IsLeinster at hL
    rw [← sum_cyclic G]
    exact hL
  · rintro ⟨hc, hp⟩
    exact cyclic_of_perfect_is_leinster G hp

end LeinsterGroup

#print axioms LeinsterGroup.abelian_is_leinster_iff_cyclic_perfect
