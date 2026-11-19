import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases

/-! Restated from the checkout (FormalConjectures/Paper/MonochromaticQuantumGraph.lean). -/

open scoped NNReal

namespace MonochromaticQuantumGraph

abbrev V (N : Nat) := Fin N

structure EdgeN (N D : Nat) where
  u : V N
  v : V N
  i : Fin D
  j : Fin D
deriving DecidableEq

abbrev WeightsN (N D : Nat) (α : Type) := EdgeN N D → α

def mkEdge {N D : Nat} (u v : V N) (i j : Fin D) : EdgeN N D :=
  ⟨u, v, i, j⟩

def vertices : (N : Nat) → List (V N)
  | 0 => []
  | N + 1 =>
      (0 : Fin (N + 1)) :: (vertices N).map Fin.succ

def allEqualList {N D : Nat} (ι : V N → Fin D) (L : List (V N)) : Prop :=
  List.IsChain (fun v w => ι v = ι w) L

def allEqual {N D : Nat} (ι : V N → Fin D) : Prop :=
  allEqualList ι (vertices N)

instance {N D : Nat} (ι : V N → Fin D) (L : List (V N)) :
    Decidable (allEqualList ι L) := by
  letI : DecidableRel (fun v w : V N => ι v = ι w) := fun v w => inferInstance
  unfold allEqualList
  infer_instance

instance {N D : Nat} (ι : V N → Fin D) : Decidable (allEqual ι) := by
  unfold allEqual
  infer_instance

def pmSumListAux {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) :
    Nat → List (V N) → α
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, [] => 1
  | _ + 2, [_] => 0
  | n + 2, v :: vs =>
      (vs.map (fun u =>
          W (mkEdge v u (ι v) (ι u)) *
            pmSumListAux W ι n (vs.erase u)
        )).sum

def pmSumList {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) (L : List (V N)) : α :=
  pmSumListAux W ι L.length L

def pmSumN {α : Type} [Semiring α] (N D : Nat)
    (W : WeightsN N D α) (ι : V N → Fin D) : α :=
  pmSumList W ι (vertices N)

def EqSystemN {α : Type} [Semiring α] (N D : Nat) (W : WeightsN N D α) : Prop :=
  ∀ ι : V N → Fin D,
    pmSumN N D W ι =
      (if allEqual ι then (1 : α) else (0 : α))

namespace B4

lemma pm4 {α : Type} [Semiring α] {D : Nat} (W : WeightsN 4 D α) (ι : V 4 → Fin D) :
    pmSumN 4 D W ι =
      W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) +
      W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) +
      W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, add_assoc]

lemma allEq4 {D : Nat} (ι : V 4 → Fin D) :
    allEqual ι ↔ ι 0 = ι 1 ∧ ι 1 = ι 2 ∧ ι 2 = ι 3 := by
  simp [allEqual, allEqualList, vertices]

/-- The three matching products at the constant colouring `i`. -/
noncomputable def P {D : Nat} (W : WeightsN 4 D ℝ≥0) (i : Fin D) : Fin 3 → ℝ≥0 :=
  ![W (mkEdge 0 1 i i) * W (mkEdge 2 3 i i),
    W (mkEdge 0 2 i i) * W (mkEdge 1 3 i i),
    W (mkEdge 0 3 i i) * W (mkEdge 1 2 i i)]

lemma sum_P {D : Nat} (W : WeightsN 4 D ℝ≥0) (hW : EqSystemN 4 D W) (i : Fin D) :
    P W i 0 + P W i 1 + P W i 2 = 1 := by
  have h := hW (fun _ => i)
  rw [pm4, if_pos ((allEq4 _).2 ⟨rfl, rfl, rfl⟩)] at h
  simpa [P] using h

lemma exists_P {D : Nat} (W : WeightsN 4 D ℝ≥0) (hW : EqSystemN 4 D W) (i : Fin D) :
    ∃ k : Fin 3, P W i k ≠ 0 := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have h := sum_P W hW i
  rw [hc 0, hc 1, hc 2] at h
  simp at h

lemma zero_of {D : Nat} (W : WeightsN 4 D ℝ≥0) (hW : EqSystemN 4 D W) (ι : V 4 → Fin D)
    (h01 : ι 0 ≠ ι 1 ∨ ι 1 ≠ ι 2 ∨ ι 2 ≠ ι 3) :
    W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) = 0 ∧
    W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) = 0 ∧
    W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) = 0 := by
  have h := hW ι
  rw [pm4, if_neg (by rw [allEq4]; tauto)] at h
  rw [add_eq_zero, add_eq_zero] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end B4

open B4 in
theorem eqSystem4_no_solution_nnreal_ge4 :
    ∀ D : Nat, D ≥ 4 →
      ¬ ∃ W : WeightsN 4 D ℝ≥0, EqSystemN 4 D W := by
  rintro D hD ⟨W, hW⟩
  choose f hf using exists_P W hW
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp; omega)
  have hi := hf i
  have hj := hf j
  rw [hfij] at hi
  generalize f j = k at hi hj
  fin_cases k
  · have h := (zero_of W hW ![i, i, j, j] (by simp [hij])).1
    simp [P] at hi hj h
    tauto
  · have h := (zero_of W hW ![i, j, i, j] (by simp [hij])).2.1
    simp [P] at hi hj h
    tauto
  · have h := (zero_of W hW ![i, j, j, i] (by simp [hij])).2.2
    simp [P] at hi hj h
    tauto

end MonochromaticQuantumGraph

#print axioms MonochromaticQuantumGraph.eqSystem4_no_solution_nnreal_ge4
