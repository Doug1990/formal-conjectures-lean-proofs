import Mathlib

namespace SimpleGraph

noncomputable def multicolourGraphRamsey {α : Type*} [Fintype α] (k : ℕ) (G : SimpleGraph α) : ℕ :=
  sInf {n : ℕ | ∀ C : TopEdgeLabeling (Fin n) (Fin k), ∃ i, G.IsContained (C.labelGraph i)}

end SimpleGraph

open Filter SimpleGraph

namespace Erdos554

/-- With one colour, the colour class is the whole complete graph. -/
lemma labelGraph_fin_one {n : ℕ} (C : TopEdgeLabeling (Fin n) (Fin 1)) (i : Fin 1) :
    C.labelGraph i = ⊤ := by
  ext x y
  rw [TopEdgeLabeling.labelGraph_adj, top_adj]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Subsingleton.elim _ _⟩⟩

theorem multicolourGraphRamsey_one_cycleGraph_five :
    multicolourGraphRamsey 1 (cycleGraph 5) = 5 := by
  have hmem : ∀ n : ℕ, 5 ≤ n →
      ∀ C : TopEdgeLabeling (Fin n) (Fin 1), ∃ i, (cycleGraph 5).IsContained (C.labelGraph i) := by
    intro n hn C
    refine ⟨0, ?_⟩
    rw [labelGraph_fin_one]
    exact isContained_top_iff.mpr ⟨⟨Fin.castLE hn, Fin.castLE_injective hn⟩⟩
  unfold multicolourGraphRamsey
  apply le_antisymm
  · exact Nat.sInf_le (hmem 5 le_rfl)
  · refine le_csInf ⟨5, ?_⟩ ?_
    · exact hmem 5 le_rfl
    intro n hn
    obtain ⟨i, hi⟩ := hn (show TopEdgeLabeling (Fin n) (Fin 1) from fun _ => 0)
    rw [labelGraph_fin_one] at hi
    obtain ⟨f⟩ := isContained_top_iff.mp hi
    simpa using Fintype.card_le_of_embedding f

end Erdos554

#print axioms Erdos554.multicolourGraphRamsey_one_cycleGraph_five
