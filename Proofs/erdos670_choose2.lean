import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Linarith

namespace Erdos670

def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

lemma gap_bound (s : Finset ℝ) : (∀ x ∈ s, 1 ≤ x) →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |x - y|) →
    ∀ y : ℝ, 0 ≤ y → (∀ x ∈ s, x ≤ y) → (s.card : ℝ) ≤ y := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ y hy _; simpa using hy
  | insert a s ha ih =>
    intro h1 h2 y hy hle
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.card_insert_of_notMem has]
    have ha1 : 1 ≤ a := h1 a (Finset.mem_insert_self a s)
    have hs := ih (fun x hx => h1 x (Finset.mem_insert_of_mem hx))
      (fun x hx z hz hxz => h2 x (Finset.mem_insert_of_mem hx) z (Finset.mem_insert_of_mem hz) hxz)
      (a - 1) (by linarith) (fun x hx => by
        have hxa := ha x hx
        have := h2 x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s) (ne_of_lt hxa)
        rw [abs_sub_comm, abs_of_pos (by linarith)] at this
        linarith)
    have hay := hle a (Finset.mem_insert_self a s)
    push_cast
    linarith

theorem erdos_670.variants.choose_two (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : HasSeparatedDistances A) (hn : A.card ≠ 2) :
    (A.card.choose 2 : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  have hdiam0 : 0 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := Metric.diam_nonneg
  rcases Nat.lt_or_ge A.card 2 with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simpa using hdiam0
  have h3 : 3 ≤ A.card := by omega
  have hbdd : Bornology.IsBounded (A : Set (EuclideanSpace ℝ (Fin d))) :=
    A.finite_toSet.isBounded
  have hge : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 ≤ dist a b := by
    intro a ha b hb hab
    obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ A, c ≠ a ∧ c ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsub : A ⊆ {a, b} := by
        intro c hc
        by_cases hca : c = a
        · simp [hca]
        · simp [hcon c hc hca]
      have := le_trans (Finset.card_le_card hsub) Finset.card_le_two
      omega
    have hs : s(a, c) ≠ s(b, c) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hab h1
      · exact hca h1.symm
    have key := hA a ha c hc b hb c hc (fun h => hca h.symm) (fun h => hcb h.symm) hs
    have := abs_dist_sub_le a b c
    linarith
  set S := A.offDiag.image (fun p => dist p.1 p.2) with hSdef
  have hcard : A.offDiag.card ≤ 2 * S.card := by
    apply Finset.card_le_mul_card_image
    intro r hr
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hr
    have hsub : A.offDiag.filter (fun p => dist p.1 p.2 = dist a b) ⊆ {(a, b), (b, a)} := by
      rintro ⟨c, e⟩ hce
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hce hab
      obtain ⟨⟨hc, he, hce'⟩, hd⟩ := hce
      obtain ⟨ha, hb, hab'⟩ := hab
      by_contra hne
      have hs : s(a, b) ≠ s(c, e) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp at hne
        · simp at hne
      have := hA a ha b hb c hc e he hab' hce' hs
      rw [hd, sub_self, abs_zero] at this
      linarith
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hS1 : ∀ x ∈ S, 1 ≤ x := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_offDiag] at hab
    exact hge a hab.1 b hab.2.1 hab.2.2
  have hS2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨c, e⟩, hce, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_offDiag] at hab hce
    apply hA a hab.1 b hab.2.1 c hce.1 e hce.2.1 hab.2.2 hce.2.2
    intro h
    apply hxy
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact dist_comm _ _
  have hSd : ∀ x ∈ S, x ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_offDiag] at hab
    exact Metric.dist_le_diam_of_mem hbdd hab.1 hab.2.1
  have hmain := gap_bound S hS1 hS2 _ hdiam0 hSd
  have hc : A.card.choose 2 ≤ S.card := by
    rw [Nat.choose_two_right, Nat.mul_sub_one]
    rw [Finset.offDiag_card] at hcard
    omega
  calc (A.card.choose 2 : ℝ) ≤ S.card := by exact_mod_cast hc
    _ ≤ _ := hmain

end Erdos670

#print axioms Erdos670.erdos_670.variants.choose_two
