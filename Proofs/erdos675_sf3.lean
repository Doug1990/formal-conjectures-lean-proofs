import Mathlib

namespace Erdos675

def IsTranslation (A : Set ℕ) (n t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

noncomputable def minTranslation (A : Set ℕ) (n : ℕ) : ℕ :=
  sInf {t : ℕ | IsTranslation A n t}

lemma not_sf4 : ¬ Squarefree (4 : ℕ) := by
  intro h
  have := h 2 (by norm_num)
  norm_num at this

lemma sf_prime {p : ℕ} (hp : p.Prime) : Squarefree p := hp.prime.squarefree

lemma sf6 : Squarefree (6 : ℕ) := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.squarefree_mul (by norm_num)]
  exact ⟨sf_prime (by norm_num), sf_prime (by norm_num)⟩

theorem minTranslation_squarefree_three : minTranslation {m : ℕ | Squarefree m} 3 = 4 := by
  have sf1 : Squarefree (1 : ℕ) := squarefree_one
  have sf2 : Squarefree (2 : ℕ) := sf_prime (by norm_num)
  have sf3 : Squarefree (3 : ℕ) := sf_prime (by norm_num)
  have sf5 : Squarefree (5 : ℕ) := sf_prime (by norm_num)
  have sf7 : Squarefree (7 : ℕ) := sf_prime (by norm_num)
  have h4 : IsTranslation {m : ℕ | Squarefree m} 3 4 := by
    refine ⟨by norm_num, ?_⟩
    intro a ha1 ha3
    interval_cases a <;> simp [sf2, sf3, sf5, sf6, sf7]
  unfold minTranslation
  apply le_antisymm
  · exact Nat.sInf_le h4
  · apply le_csInf ⟨4, h4⟩
    rintro t ⟨ht1, ht⟩
    by_contra hlt
    push Not at hlt
    interval_cases t
    · exact not_sf4 ((ht 3 (by norm_num) (by norm_num)).mp sf3)
    · exact not_sf4 ((ht 2 (by norm_num) (by norm_num)).mp sf2)
    · exact not_sf4 ((ht 1 (by norm_num) (by norm_num)).mp sf1)

end Erdos675

#print axioms Erdos675.minTranslation_squarefree_three
