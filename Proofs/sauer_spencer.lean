import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

variable {V : Type*}

def Packs (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ u v, G₁.Adj u v → ¬ G₂.Adj (σ u) (σ v)

section SS

variable [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)

/-- Ordered conflict pairs of a placement `σ`. -/
noncomputable def conf (σ : Equiv.Perm V) : Finset (V × V) := by
  classical
  exact (Finset.univ : Finset (V × V)).filter
    (fun p => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2))

omit [DecidableEq V] in
lemma mem_conf {σ : Equiv.Perm V} {p : V × V} :
    p ∈ conf G₁ G₂ σ ↔ G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2) := by
  classical
  unfold conf
  simp

/-- Swapping `u` with a good vertex `w` does not create conflicts. -/
lemma swap_sub (σ : Equiv.Perm V) (u w : V)
    (ha : ∀ x, G₁.Adj u x → ¬ G₂.Adj (σ x) (σ w))
    (hb : ∀ y, G₁.Adj w y → ¬ G₂.Adj (σ y) (σ u)) :
    conf G₁ G₂ (σ * Equiv.swap u w) ⊆ conf G₁ G₂ σ := by
  intro p hp
  obtain ⟨a, b⟩ := p
  rw [mem_conf] at hp ⊢
  obtain ⟨h1, h2⟩ := hp
  refine ⟨h1, ?_⟩
  simp only [Equiv.Perm.mul_apply] at h2
  have hab : a ≠ b := G₁.ne_of_adj h1
  by_cases hau : a = u
  · subst hau
    by_cases hbw : b = w
    · subst hbw
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
      exact h2.symm
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbw] at h2
      exact absurd h2.symm (ha b h1)
  · by_cases haw : a = w
    · subst haw
      by_cases hbu : b = u
      · subst hbu
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at h2
        exact h2.symm
      · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbu (Ne.symm hab)] at h2
        exact absurd h2.symm (hb b h1)
    · rw [Equiv.swap_apply_of_ne_of_ne hau haw] at h2
      by_cases hbu : b = u
      · subst hbu
        rw [Equiv.swap_apply_left] at h2
        exact absurd h2 (ha a h1.symm)
      · by_cases hbw : b = w
        · subst hbw
          rw [Equiv.swap_apply_right] at h2
          exact absurd h2 (hb a h1.symm)
        · rw [Equiv.swap_apply_of_ne_of_ne hbu hbw] at h2
          exact h2

lemma not_mem_swap (σ : Equiv.Perm V) (u v w : V) (huv : G₁.Adj u v) (hvw : v ≠ w)
    (ha : ∀ x, G₁.Adj u x → ¬ G₂.Adj (σ x) (σ w)) :
    (u, v) ∉ conf G₁ G₂ (σ * Equiv.swap u w) := by
  rw [mem_conf]
  rintro ⟨-, h2⟩
  simp only [Equiv.Perm.mul_apply] at h2
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (G₁.ne_of_adj huv).symm hvw] at h2
  exact ha v huv h2.symm

variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

/-- Existence of a good swap partner. -/
lemma exists_good (σ : Equiv.Perm V) (u v : V) (h1 : G₁.Adj u v) (h2 : G₂.Adj (σ u) (σ v))
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    ∃ w, w ≠ v ∧ (∀ x, G₁.Adj u x → ¬ G₂.Adj (σ x) (σ w)) ∧
      (∀ y, G₁.Adj w y → ¬ G₂.Adj (σ y) (σ u)) := by
  classical
  set A : Finset V := Finset.univ.filter (fun w => ∃ x, G₁.Adj u x ∧ G₂.Adj (σ x) (σ w)) with hAdef
  set B : Finset V := Finset.univ.filter (fun w => ∃ y, G₁.Adj w y ∧ G₂.Adj (σ y) (σ u)) with hBdef
  have hA : A.card ≤ G₁.maxDegree * G₂.maxDegree := by
    have hsub : A ⊆ (G₁.neighborFinset u).biUnion
        (fun x => (G₂.neighborFinset (σ x)).image σ.symm) := by
      intro w hw
      rw [hAdef, Finset.mem_filter] at hw
      obtain ⟨x, hx1, hx2⟩ := hw.2
      rw [Finset.mem_biUnion]
      refine ⟨x, (G₁.mem_neighborFinset u x).2 hx1, ?_⟩
      rw [Finset.mem_image]
      exact ⟨σ w, (G₂.mem_neighborFinset _ _).2 hx2, by simp⟩
    calc A.card ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ G₁.neighborFinset u, ((G₂.neighborFinset (σ x)).image σ.symm).card :=
          Finset.card_biUnion_le
      _ ≤ (G₁.neighborFinset u).card • G₂.maxDegree := by
          refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
          refine le_trans Finset.card_image_le ?_
          rw [card_neighborFinset_eq_degree]
          exact G₂.degree_le_maxDegree _
      _ ≤ G₁.maxDegree * G₂.maxDegree := by
          rw [smul_eq_mul, card_neighborFinset_eq_degree]
          exact Nat.mul_le_mul_right _ (G₁.degree_le_maxDegree _)
  have hB : B.card ≤ G₁.maxDegree * G₂.maxDegree := by
    have hsub : B ⊆ (G₂.neighborFinset (σ u)).biUnion
        (fun z => G₁.neighborFinset (σ.symm z)) := by
      intro w hw
      rw [hBdef, Finset.mem_filter] at hw
      obtain ⟨y, hy1, hy2⟩ := hw.2
      rw [Finset.mem_biUnion]
      refine ⟨σ y, (G₂.mem_neighborFinset _ _).2 hy2.symm, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact (G₁.mem_neighborFinset _ _).2 hy1.symm
    calc B.card ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ z ∈ G₂.neighborFinset (σ u), (G₁.neighborFinset (σ.symm z)).card :=
          Finset.card_biUnion_le
      _ ≤ (G₂.neighborFinset (σ u)).card • G₁.maxDegree := by
          refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
          rw [card_neighborFinset_eq_degree]
          exact G₁.degree_le_maxDegree _
      _ ≤ G₁.maxDegree * G₂.maxDegree := by
          rw [smul_eq_mul, card_neighborFinset_eq_degree, Nat.mul_comm]
          exact Nat.mul_le_mul_left _ (G₂.degree_le_maxDegree _)
  have huA : u ∈ A := by
    rw [hAdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, v, h1, h2.symm⟩
  have huB : u ∈ B := by
    rw [hBdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, v, h1, h2.symm⟩
  have hinter : 1 ≤ (A ∩ B).card :=
    Finset.card_pos.2 ⟨u, Finset.mem_inter.2 ⟨huA, huB⟩⟩
  have hunion := Finset.card_union_add_card_inter A B
  have hins := Finset.card_insert_le v (A ∪ B)
  have hlt : (insert v (A ∪ B)).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    have : 2 * G₁.maxDegree * G₂.maxDegree = G₁.maxDegree * G₂.maxDegree +
        G₁.maxDegree * G₂.maxDegree := by rw [Nat.mul_assoc, Nat.two_mul]
    omega
  by_contra hno
  push Not at hno
  have hsub : (Finset.univ : Finset V) ⊆ insert v (A ∪ B) := by
    intro w _
    by_cases hwv : w = v
    · exact Finset.mem_insert.2 (Or.inl hwv)
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 ?_))
      by_cases hwa : ∀ x, G₁.Adj u x → ¬ G₂.Adj (σ x) (σ w)
      · obtain ⟨y, hy1, hy2⟩ := hno w hwv hwa
        exact Or.inr (by rw [hBdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, y, hy1, hy2⟩)
      · push Not at hwa
        obtain ⟨x, hx1, hx2⟩ := hwa
        exact Or.inl (by rw [hAdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, x, hx1, hx2⟩)
  exact absurd (Finset.card_le_card hsub) (not_le.2 hlt)

theorem bollobas_eldridge_catlin_conjecture.variants.sauer_spencer
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ := by
  obtain ⟨σ, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm V))
    (fun σ => (conf G₁ G₂ σ).card) Finset.univ_nonempty
  refine ⟨σ, fun u v h1 h2 => ?_⟩
  obtain ⟨w, hvw, ha, hb⟩ := exists_good G₁ G₂ σ u v h1 h2 h
  have hsub := swap_sub G₁ G₂ σ u w ha hb
  have hnot := not_mem_swap G₁ G₂ σ u v w h1 hvw.symm ha
  have hmem : (u, v) ∈ conf G₁ G₂ σ := (mem_conf G₁ G₂).2 ⟨h1, h2⟩
  have hss : conf G₁ G₂ (σ * Equiv.swap u w) ⊂ conf G₁ G₂ σ :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨(u, v), hmem, hnot⟩
  have := hmin (σ * Equiv.swap u w) (Finset.mem_univ _)
  exact absurd (Finset.card_lt_card hss) (not_lt.2 this)

end SS

end BollobasEldridgeCatlinConjecture

#print axioms BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.sauer_spencer
