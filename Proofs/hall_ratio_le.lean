import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

/-! Restated locally from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/FractionalChromaticNumber.lean -/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure IsFractionalColoring (w : Finset V → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ w S
  indep : ∀ S, w S ≠ 0 → G.IsIndepSet (S : Set V)
  cover : ∀ v, 1 ≤ ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S), w S

def fractionalColoringWeights : Set ℝ :=
  {t | ∃ w : Finset V → ℝ, G.IsFractionalColoring w ∧ ∑ S, w S = t}

noncomputable def fractionalChromaticNumber : ℝ :=
  sInf (fractionalColoringWeights G)

def singletonWeights : Finset V → ℝ := fun S => if S.card = 1 then 1 else 0

theorem isFractionalColoring_singletonWeights : G.IsFractionalColoring singletonWeights where
  nonneg S := by unfold singletonWeights; split_ifs <;> simp
  indep S hS := by
    unfold singletonWeights at hS
    split_ifs at hS with h
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      intro x hx y hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · exact absurd rfl hS
  cover v := by
    have hmem : {v} ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S) := by simp
    calc (1 : ℝ) = singletonWeights {v} := by simp [singletonWeights]
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S), singletonWeights S :=
          Finset.single_le_sum (fun S _ => by unfold singletonWeights; split_ifs <;> simp) hmem

theorem fractionalColoringWeights_nonempty : (fractionalColoringWeights G).Nonempty :=
  ⟨_, singletonWeights, G.isFractionalColoring_singletonWeights, rfl⟩

theorem fractionalColoringWeights_nonneg {t : ℝ} (ht : t ∈ fractionalColoringWeights G) :
    0 ≤ t := by
  obtain ⟨w, hw, rfl⟩ := ht
  exact Finset.sum_nonneg fun S _ => hw.nonneg S

theorem fractionalChromaticNumber_nonneg : 0 ≤ G.fractionalChromaticNumber :=
  Real.sInf_nonneg fun _ ht => G.fractionalColoringWeights_nonneg ht

end SimpleGraph

open SimpleGraph

namespace HallRatioConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def hallRatio (G : SimpleGraph V) : ℝ :=
  sSup {r | ∃ S : Finset V, S.Nonempty ∧
    r = (S.card : ℝ) / ((G.induce (S : Set V)).indepNum : ℝ)}

/-- An independent set `T` meets `S` in at most `α(G[S])` vertices. -/
lemma card_filter_le_indepNum (G : SimpleGraph V) (S T : Finset V)
    (hT : G.IsIndepSet (T : Set V)) :
    (S.filter (· ∈ T)).card ≤ (G.induce (S : Set V)).indepNum := by
  classical
  let U : Finset (S : Set V) := Finset.univ.filter (fun x => x.1 ∈ T)
  have hU : U.card = (S.filter (· ∈ T)).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_filter.2 ⟨x.2, hx⟩
    · intro x _ y _ h
      exact Subtype.ext h
    · intro y hy
      rw [Finset.mem_filter] at hy
      exact ⟨⟨y, hy.1⟩, by simp [U, hy.2], rfl⟩
  rw [← hU]
  apply IsIndepSet.card_le_indepNum
  intro x hx y hy hxy
  simp only [U, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
  have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have := hT hx hy hne
  simpa [SimpleGraph.comap_adj] using this

/-- Double counting: `|S| ≤ t · α(G[S])` for every fractional colouring of total weight `t`. -/
lemma card_le_mul (G : SimpleGraph V) (S : Finset V) (w : Finset V → ℝ)
    (hw : G.IsFractionalColoring w) :
    (S.card : ℝ) ≤ (∑ T, w T) * ((G.induce (S : Set V)).indepNum : ℝ) := by
  classical
  generalize hα : ((G.induce (S : Set V)).indepNum : ℝ) = α
  have hcard : ∀ T, w T ≠ 0 → ((S.filter (· ∈ T)).card : ℝ) ≤ α := by
    intro T h0
    rw [← hα]
    exact_mod_cast card_filter_le_indepNum G S T (hw.indep T h0)
  calc (S.card : ℝ) = ∑ v ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ S, ∑ T ∈ (Finset.univ : Finset (Finset V)).filter (fun T => v ∈ T), w T :=
        Finset.sum_le_sum fun v _ => hw.cover v
    _ = ∑ v ∈ S, ∑ T : Finset V, (if v ∈ T then w T else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ T : Finset V, ∑ v ∈ S, (if v ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ T : Finset V, ((S.filter (· ∈ T)).card : ℝ) * w T := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ T : Finset V, α * w T := by
        refine Finset.sum_le_sum fun T _ => ?_
        by_cases h0 : w T = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_right (hcard T h0) (hw.nonneg T)
    _ = (∑ T, w T) * α := by rw [Finset.sum_mul]; simp [mul_comm]

theorem hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    hallRatio G ≤ G.fractionalChromaticNumber := by
  refine Real.sSup_le ?_ G.fractionalChromaticNumber_nonneg
  rintro r ⟨S, hS, rfl⟩
  refine le_csInf G.fractionalColoringWeights_nonempty ?_
  rintro t ⟨w, hw, rfl⟩
  have hle := card_le_mul G S w hw
  have hS1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hα : (0 : ℝ) < ((G.induce (S : Set V)).indepNum : ℝ) := by
    rcases Nat.eq_zero_or_pos (G.induce (S : Set V)).indepNum with h | h
    · rw [h] at hle; simp at hle; exact absurd hle hS.ne_empty
    · exact_mod_cast h
  rw [div_le_iff₀ hα]
  exact hle

end HallRatioConjecture

#print axioms HallRatioConjecture.hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber
