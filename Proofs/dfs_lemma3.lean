import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

end SimpleGraph

namespace DfsL3

open SimpleGraph

/-- Block pattern: rows 0–3 are the four `A` blocks, rows 4–7 the four `B` blocks.
Code 0: `i + j ≥ n`, code 1: `i + j ≥ n - 1`, code 2: complete, code 3: no edges. -/
def W : Fin 8 → Fin 8 → ℕ :=
  ![![3, 3, 3, 3, 0, 0, 2, 1],
    ![3, 3, 3, 3, 2, 0, 1, 1],
    ![3, 3, 3, 3, 1, 1, 1, 2],
    ![3, 3, 3, 3, 0, 2, 1, 1],
    ![0, 2, 1, 0, 3, 3, 3, 3],
    ![0, 0, 1, 2, 3, 3, 3, 3],
    ![2, 1, 1, 1, 3, 3, 3, 3],
    ![1, 1, 2, 1, 3, 3, 3, 3]]

def off : Fin 8 → ℕ := ![0, 1, 2, 1, 0, 0, 2, 2]

def pos : Fin 8 → Fin 3 := ![0, 0, 0, 1, 1, 2, 1, 2]

def thr (n c : ℕ) : ℕ := if c = 2 then 0 else n - c

def val (n c i : ℕ) : ℕ := if c = 3 then 0 else if c = 2 then n else i + c

lemma W_symm : ∀ a b : Fin 8, W a b = W b a := by decide

lemma W_diag : ∀ a : Fin 8, W a a = 3 := by decide

lemma W_le : ∀ a b : Fin 8, W a b ≤ 3 := by decide

lemma W_side : ∀ a b : Fin 8, W a b ≠ 3 → (a.val < 4 ↔ ¬ b.val < 4) := by decide

lemma pos_inj : ∀ a b : Fin 8, pos a = pos b → off a = off b → a = b := by decide

lemma off_lt : ∀ a : Fin 8, off a < 3 := by decide

def H (n : ℕ) : SimpleGraph (Fin 8 × Fin n) where
  Adj x y := W x.1 y.1 ≠ 3 ∧ thr n (W x.1 y.1) ≤ x.2.val + y.2.val
  symm := ⟨fun x y h => by
    rw [W_symm y.1 x.1, Nat.add_comm y.2.val]
    exact h⟩
  loopless := ⟨fun x h => h.1 (W_diag x.1)⟩

instance (n : ℕ) : DecidableRel (H n).Adj := fun x y =>
  inferInstanceAs (Decidable (W x.1 y.1 ≠ 3 ∧ thr n (W x.1 y.1) ≤ x.2.val + y.2.val))

lemma inner (n i c : ℕ) (hi : i < n) (hc : c ≤ 3) :
    (∑ j : Fin n, if (c ≠ 3 ∧ thr n c ≤ i + j.val) then 1 else 0) = val n c i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if (c ≠ 3 ∧ thr n c ≤ i + j) then 1 else 0) n,
    ← Finset.card_filter]
  have : (Finset.range n).filter (fun j => c ≠ 3 ∧ thr n c ≤ i + j) =
      Finset.Ico (if c = 3 then n else thr n c - i) n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    unfold thr
    split_ifs <;> omega
  rw [this, Nat.card_Ico]
  unfold val thr
  split_ifs <;> omega

lemma degH (n : ℕ) (x : Fin 8 × Fin n) :
    (H n).degree x = 3 * x.2.val + n + 1 + off x.1 := by
  obtain ⟨q, i⟩ := x
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_prod_type]
  have key : ∀ r : Fin 8, (∑ j : Fin n, if (H n).Adj (q, i) (r, j) then 1 else 0)
      = val n (W q r) i := fun r => inner n i (W q r) i.isLt (W_le q r)
  rw [Finset.sum_congr rfl (fun r _ => key r), Fin.sum_univ_eight]
  have hi := i.isLt
  fin_cases q <;> simp [W, val, off] <;> omega

def e (n : ℕ) : Fin (8 * n) ≃ Fin 8 × Fin n := finProdFinEquiv.symm

lemma degG (n : ℕ) (v : Fin (8 * n)) [Fintype (((H n).comap (e n)).neighborSet v)] :
    ((H n).comap (e n)).degree v = 3 * (e n v).2.val + n + 1 + off (e n v).1 := by
  rw [← (Iso.comap (e n) (H n)).degree_eq v]
  exact degH n (e n v)

instance instGr (n : ℕ) : DecidableRel ((H n).comap (e n)).Adj := fun u v =>
  inferInstanceAs (Decidable ((H n).Adj (e n u) (e n v)))

end DfsL3

namespace SimpleGraph

open DfsL3

lemma lemma3 (n : ℕ) (hn : 0 < n) :
    ∃ (G : SimpleGraph (Fin (8 * n))) (_ : DecidableRel G.Adj),
      G.IsBipartite ∧ G.minDegree = n + 1 ∧ degreeSequenceMultiplicity G = 3 := by
  refine ⟨(H n).comap (e n), instGr n, ?_, ?_, ?_⟩
  · refine Coloring.colorable (Coloring.mk (fun v => if (e n v).1.val < 4 then (0 : Fin 2) else 1) ?_)
    intro u v h
    have h' : W (e n u).1 (e n v).1 ≠ 3 := h.1
    have h1 := W_side _ _ h'
    by_cases hu : (e n u).1.val < 4 <;> by_cases hv : (e n v).1.val < 4
    · exact absurd hv (h1.1 hu)
    · simp [hu, hv]
    · simp [hu, hv]
    · exact absurd (h1.2 hv) hu
  · apply le_antisymm
    · calc ((H n).comap (e n)).minDegree ≤ ((H n).comap (e n)).degree ((e n).symm (0, ⟨0, hn⟩)) :=
            minDegree_le_degree _ _
        _ = n + 1 := by rw [degG]; simp [off]
    · have : Nonempty (Fin (8 * n)) := ⟨⟨0, by omega⟩⟩
      apply le_minDegree_of_forall_le_degree
      intro v
      rw [degG]
      omega
  · set G := (H n).comap (e n) with hG
    set L := degreeSequence G with hL
    have hc : ∀ d, L.count d = #(univ.filter fun v => d = G.degree v) := by
      intro d
      rw [hL, degreeSequence, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_map]
      rfl
    have hle : ∀ d, #(univ.filter fun v => d = G.degree v) ≤ 3 := by
      intro d
      have := Finset.card_le_card_of_injOn (s := univ.filter fun v => d = G.degree v)
        (t := (univ : Finset (Fin 3))) (fun v => pos (e n v).1) (fun _ _ => Finset.mem_univ _) ?_
      · simpa using this
      intro v hv w hw hpw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      rw [degG] at hv hw
      have o1 := off_lt (e n v).1
      have o2 := off_lt (e n w).1
      have hoff : off (e n v).1 = off (e n w).1 := by omega
      have h1 : (e n v).1 = (e n w).1 := pos_inj _ _ hpw hoff
      have h2 : (e n v).2 = (e n w).2 := Fin.ext (by omega)
      exact (e n).injective (Prod.ext h1 h2)
    have hge : 3 ≤ #(univ.filter fun v => n + 1 = G.degree v) := by
      have h0 : ∀ q : Fin 8, off q = 0 →
          (e n).symm (q, ⟨0, hn⟩) ∈ univ.filter fun v => n + 1 = G.degree v := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [degG]
        simp [hq]
      have := Finset.two_lt_card.2 ⟨_, h0 0 rfl, _, h0 4 rfl, _, h0 5 rfl,
        by simp, by simp, by simp⟩
      omega
    have hmul : degreeSequenceMultiplicity G = (L.map fun d => L.count d).max?.getD 0 := rfl
    refine hmul.trans ?_
    apply le_antisymm
    · cases h : (L.map fun d => L.count d).max? with
      | none => simp
      | some a =>
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 (List.max?_mem h)
        simpa [hc] using hle x
    · have hpos : 0 < L.count (n + 1) := by rw [hc]; omega
      have hmem : L.count (n + 1) ∈ L.map fun d => L.count d :=
        List.mem_map_of_mem (List.count_pos_iff.1 hpos)
      have := List.le_max?_getD_of_mem (k := 0) hmem
      rw [hc] at this
      omega

end SimpleGraph

#print axioms SimpleGraph.lemma3
