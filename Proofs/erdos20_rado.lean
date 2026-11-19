import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Action.Defs

/-! Restated from FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean. -/

section Sunflower
variable {α : Type*}

def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

end Sunflower

namespace Erdos20

noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

section Core
variable {α : Type} [DecidableEq α]

/-- Either `k` pairwise disjoint members, or a small set meeting every member. -/
lemma disj_or_cover (n k : ℕ) (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = n) (hn : 0 < n) :
    (∃ D ⊆ F, D.card = k ∧ (D : Set (Finset α)).PairwiseDisjoint id) ∨
      ∃ U : Finset α, U.card ≤ (k - 1) * n ∧ ∀ A ∈ F, ∃ x ∈ U, x ∈ A := by
  classical
  let P : Finset (Finset (Finset α)) :=
    F.powerset.filter (fun D : Finset (Finset α) => (↑D : Set (Finset α)).PairwiseDisjoint id)
  have hP : P.Nonempty := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _,
    by rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩⟩
  obtain ⟨D, hDP, hDmax⟩ := Finset.exists_max_image P Finset.card hP
  obtain ⟨hDF, hDdisj⟩ := Finset.mem_filter.1 hDP
  rw [Finset.mem_powerset] at hDF
  by_cases hk : k ≤ D.card
  · left
    obtain ⟨D', hD'D, hD'k⟩ := Finset.exists_subset_card_eq hk
    exact ⟨D', hD'D.trans hDF, hD'k, hDdisj.subset (by exact_mod_cast hD'D)⟩
  · right
    refine ⟨D.biUnion id, ?_, ?_⟩
    · calc (D.biUnion id).card ≤ ∑ A ∈ D, (id A).card := Finset.card_biUnion_le
        _ = D.card * n := by
          rw [Finset.sum_congr rfl (fun A hA => (hF A (hDF hA) : (id A).card = n)),
            Finset.sum_const, smul_eq_mul]
        _ ≤ (k - 1) * n := Nat.mul_le_mul_right _ (by omega)
    · intro A hA
      by_contra h
      push Not at h
      have hAD : A ∉ D := by
        intro hAD
        have : A.Nonempty := by rw [← Finset.card_pos, hF A hA]; exact hn
        obtain ⟨x, hx⟩ := this
        exact h x (Finset.mem_biUnion.2 ⟨A, hAD, hx⟩) hx
      have hins : insert A D ∈ P := by
        refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hA hDF), ?_⟩
        rw [Finset.coe_insert]
        refine hDdisj.insert ?_
        intro B hB _
        refine Finset.disjoint_left.2 ?_
        intro x hxA hxB
        exact h x (Finset.mem_biUnion.2 ⟨B, hB, hxB⟩) hxA
      have := hDmax _ hins
      rw [Finset.card_insert_of_notMem hAD] at this
      omega

/-- Erdős–Rado, Finset version. -/
theorem core (k : ℕ) : ∀ (n : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →
    (k - 1) ^ n * n.factorial < F.card →
    ∃ S ⊆ F, S.card = k ∧ ∃ K : Finset α, (S : Set (Finset α)).Pairwise (fun A B => A ∩ B = K) := by
  intro n
  induction n with
  | zero =>
    intro F hF hcard
    exfalso
    have : F.card ≤ 1 := by
      refine Finset.card_le_one.2 ?_
      intro a ha b hb
      rw [Finset.card_eq_zero.1 (hF a ha), Finset.card_eq_zero.1 (hF b hb)]
    simp at hcard
    omega
  | succ m ih =>
    intro F hF hcard
    rcases disj_or_cover (m + 1) k F hF (Nat.succ_pos m) with ⟨D, hD, hDk, hdisj⟩ | ⟨U, hU, hcov⟩
    · refine ⟨D, hD, hDk, ∅, ?_⟩
      intro A hA B hB hAB
      exact Finset.disjoint_iff_inter_eq_empty.1 (hdisj hA hB hAB)
    · have hx : ∃ x ∈ U, (k - 1) ^ m * m.factorial < (F.filter (fun A => x ∈ A)).card := by
        by_contra h
        push Not at h
        have h1 : F ⊆ U.biUnion (fun x => F.filter (fun A => x ∈ A)) := by
          intro A hA
          obtain ⟨x, hx, hxA⟩ := hcov A hA
          exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hA, hxA⟩⟩
        have h2 : F.card ≤ U.card * ((k - 1) ^ m * m.factorial) :=
          calc F.card ≤ (U.biUnion (fun x => F.filter (fun A => x ∈ A))).card :=
                Finset.card_le_card h1
            _ ≤ ∑ x ∈ U, (F.filter (fun A => x ∈ A)).card := Finset.card_biUnion_le
            _ ≤ U.card • ((k - 1) ^ m * m.factorial) := Finset.sum_le_card_nsmul _ _ _ h
            _ = U.card * ((k - 1) ^ m * m.factorial) := smul_eq_mul _ _
        have h3 : U.card * ((k - 1) ^ m * m.factorial) ≤
            (k - 1) * (m + 1) * ((k - 1) ^ m * m.factorial) := Nat.mul_le_mul_right _ hU
        have h4 : (k - 1) * (m + 1) * ((k - 1) ^ m * m.factorial) =
            (k - 1) ^ (m + 1) * (m + 1).factorial := by
          rw [pow_succ, Nat.factorial_succ]; ring
        omega
      obtain ⟨x, -, hxc⟩ := hx
      set Fx := F.filter (fun A => x ∈ A) with hFx
      set G := Fx.image (fun A => A.erase x) with hG
      have hGc : G.card = Fx.card := by
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB hAB
        have hxA := (Finset.mem_filter.1 (Finset.mem_coe.1 hA)).2
        have hxB := (Finset.mem_filter.1 (Finset.mem_coe.1 hB)).2
        rw [← Finset.insert_erase hxA, ← Finset.insert_erase hxB]
        exact congrArg (insert x) hAB
      have hGm : ∀ B ∈ G, B.card = m := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
        obtain ⟨hAF, hxA⟩ := Finset.mem_filter.1 hA
        rw [Finset.card_erase_of_mem hxA, hF A hAF]
        rfl
      have hxG : ∀ B ∈ G, x ∉ B := by
        intro B hB
        obtain ⟨A, -, rfl⟩ := Finset.mem_image.1 hB
        exact Finset.notMem_erase x A
      obtain ⟨S', hS'G, hS'k, K, hK⟩ := ih G hGm (by rw [hGc]; exact hxc)
      refine ⟨S'.image (insert x), ?_, ?_, insert x K, ?_⟩
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA
        obtain ⟨A0, hA0, rfl⟩ := Finset.mem_image.1 (hS'G hB)
        obtain ⟨hA0F, hxA0⟩ := Finset.mem_filter.1 hA0
        rw [Finset.insert_erase hxA0]
        exact hA0F
      · rw [Finset.card_image_of_injOn, hS'k]
        intro B hB C hC hBC
        have hxB := hxG B (hS'G (Finset.mem_coe.1 hB))
        have hxC := hxG C (hS'G (Finset.mem_coe.1 hC))
        rw [← Finset.erase_insert hxB, ← Finset.erase_insert hxC]
        exact congrArg (fun s => Finset.erase s x) hBC
      · intro A hA B hB hAB
        obtain ⟨B1, hB1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
        obtain ⟨C1, hC1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
        have hne : B1 ≠ C1 := fun h => hAB (by rw [h])
        rw [← Finset.insert_inter_distrib, hK (Finset.mem_coe.2 hB1) (Finset.mem_coe.2 hC1) hne]

end Core

theorem erdos_20.variants.erdos_rado_bound :
    ∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k - 1) ^ n * n.factorial + 1 := by
  intro n k hn hk
  apply Nat.sInf_le
  intro α F hFM
  obtain ⟨hF, hM⟩ := hFM
  classical
  have hFfin : F.Finite := Set.finite_of_ncard_pos (by omega)
  have hAfin : ∀ A ∈ F, A.Finite := fun A hA =>
    Set.finite_of_ncard_pos (by rw [hF A hA]; exact hn)
  have hpre : ((fun B : Finset α => (↑B : Set α)) ⁻¹' F).Finite :=
    hFfin.preimage Finset.coe_injective.injOn
  let F' : Finset (Finset α) := hpre.toFinset
  have hmem : ∀ B : Finset α, B ∈ F' ↔ (↑B : Set α) ∈ F := by
    intro B; simp [F']
  have hcard : F'.card = F.ncard := by
    rw [← Set.ncard_eq_toFinset_card _ hpre]
    exact Set.ncard_preimage_of_injective_subset_range Finset.coe_injective
      (fun A hA => ⟨(hAfin A hA).toFinset, by simp⟩)
  have hF' : ∀ B ∈ F', B.card = n := by
    intro B hB
    have := hF _ ((hmem B).1 hB)
    rwa [Set.ncard_coe_finset] at this
  obtain ⟨S', hS', hk', K, hK⟩ := core k n F' hF' (by omega)
  refine ⟨(fun B : Finset α => (↑B : Set α)) '' ↑S', ?_, ?_, ↑K, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    exact (hmem B).1 (hS' hB)
  · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hk']
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hBC
    have hne : B ≠ C := fun h => hBC (by rw [h])
    show (↑B : Set α) ∩ ↑C = ↑K
    rw [← Finset.coe_inter, hK hB hC hne]

end Erdos20

#print axioms Erdos20.erdos_20.variants.erdos_rado_bound
