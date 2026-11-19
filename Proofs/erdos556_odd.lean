import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

open Finset

namespace SimpleGraph

/-- Restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/EdgeColouring.lean. -/
def IsEdgeColouring {V ι : Type*} (H : SimpleGraph V) (c : ι → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- Restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean. -/
noncomputable def multicolourRamsey {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin k → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, G ⊑ c i}

end SimpleGraph

namespace Erdos556

open SimpleGraph

namespace RC

/-- Three-colour Ramsey with asymmetric clique sizes, bound `3 ^ (a 0 + a 1 + a 2)`. -/
lemma ramsey {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V)
    (hc : ∀ x y, x ≠ y → ∃ i, (c i).Adj x y) (r : ℕ) :
    ∀ a : Fin 3 → ℕ, a 0 + a 1 + a 2 ≤ r → ∀ s : Finset V, 3 ^ r ≤ s.card →
      ∃ i, ∃ t ⊆ s, t.card = a i ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → (c i).Adj x y := by
  classical
  induction r with
  | zero =>
    intro a ha s _
    exact ⟨0, ∅, Finset.empty_subset _, by simp; omega, by simp⟩
  | succ r ih =>
    intro a ha s hs
    by_cases h0 : ∃ j, a j = 0
    · obtain ⟨j, hj⟩ := h0
      exact ⟨j, ∅, Finset.empty_subset _, by simp [hj], by simp⟩
    have h0' : ∀ j, a j ≠ 0 := fun j hj => h0 ⟨j, hj⟩
    have hpos : 0 < s.card := lt_of_lt_of_le (pow_pos (by norm_num) _) hs
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    have hcard' := Finset.card_erase_add_one hv
    let S : Fin 3 → Finset V := fun j => (s.erase v).filter (fun x => (c j).Adj v x)
    have hcover : s.erase v ⊆ Finset.univ.biUnion S := by
      intro x hx
      obtain ⟨j, hj⟩ := hc v x (Finset.ne_of_mem_erase hx).symm
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨hx, hj⟩⟩
    have hle : (s.erase v).card ≤ ∑ j, (S j).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    rw [Fin.sum_univ_three] at hle
    have hex : ∃ j, 3 ^ r ≤ (S j).card := by
      by_contra hne
      simp only [not_exists, not_le] at hne
      have h1 := hne 0
      have h2 := hne 1
      have h3 := hne 2
      rw [pow_succ] at hs
      generalize 3 ^ r = P at *
      omega
    obtain ⟨j, hj⟩ := hex
    let a' : Fin 3 → ℕ := fun i => if i = j then a j - 1 else a i
    have ha' : a' 0 + a' 1 + a' 2 ≤ r := by
      have e0 := h0' 0
      have e1 := h0' 1
      have e2 := h0' 2
      fin_cases j <;> simp [a'] <;> omega
    obtain ⟨i, t, ht, htc, hmono⟩ := ih a' ha' (S j) hj
    have htS : t ⊆ s.erase v := ht.trans (Finset.filter_subset _ _)
    by_cases hij : i = j
    · rw [hij] at hmono htc
      simp only [a', if_pos rfl] at htc
      refine ⟨j, insert v t, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hv (htS.trans (Finset.erase_subset _ _))
      · have hvt : v ∉ t := fun h => (Finset.notMem_erase v s) (htS h)
        rw [Finset.card_insert_of_notMem hvt, htc]
        have := h0' j
        omega
      · intro x hx y hy hxy
        rw [Finset.mem_insert] at hx hy
        have hadj : ∀ z ∈ t, (c j).Adj v z := fun z hz => (Finset.mem_filter.1 (ht hz)).2
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact hadj y hy
        · exact (hadj x hx).symm
        · exact hmono x hx y hy hxy
    · refine ⟨i, t, htS.trans (Finset.erase_subset _ _), ?_, hmono⟩
      rw [htc]
      simp [a', hij]

/-- Every 3-colouring of `K_{3^{3n}}` contains a monochromatic `C_n`. -/
lemma exists_N (n : ℕ) : ∃ N, ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, cycleGraph n ⊑ c i := by
  refine ⟨3 ^ (3 * n), fun c hc => ?_⟩
  have hcov : ∀ x y : Fin (3 ^ (3 * n)), x ≠ y → ∃ i, (c i).Adj x y := by
    intro x y hxy
    have h : (⊤ : SimpleGraph (Fin (3 ^ (3 * n)))).Adj x y := hxy
    rw [hc.1, iSup_adj] at h
    exact h
  obtain ⟨i, t, -, htc, hmono⟩ := ramsey c hcov (3 * n) (fun _ => n)
    (by show n + n + n ≤ 3 * n; omega) Finset.univ (by simp)
  have htc' : t.card = n := htc
  let e := t.orderEmbOfFin htc'
  refine ⟨i, ⟨⟨{ toFun := fun k => e k, map_rel' := ?_ }, fun a b h => e.injective h⟩⟩⟩
  intro a b hab
  exact hmono _ (t.orderEmbOfFin_mem htc' a) _ (t.orderEmbOfFin_mem htc' b)
    (e.injective.ne hab.ne)

/-- Colour code: 0 inside a block of length `m`, 2 between blocks 0-1 / 2-3, 1 otherwise. -/
def code (m a b : ℕ) : ℕ :=
  if a / m = b / m then 0 else if a / m / 2 = b / m / 2 then 2 else 1

lemma code_symm (m a b : ℕ) : code m a b = code m b a := by
  unfold code
  generalize a / m = p
  generalize b / m = q
  split_ifs <;> omega

def C (m N : ℕ) (i : Fin 3) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ code m x.val y.val = i.val
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [code_symm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma C_col (m N : ℕ) : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring (C m N) := by
  refine ⟨?_, ?_⟩
  · ext x y
    simp only [top_adj, iSup_adj]
    constructor
    · intro h
      refine ⟨⟨code m x.val y.val, ?_⟩, h, rfl⟩
      unfold code
      split_ifs <;> omega
    · rintro ⟨i, h, _⟩
      exact h
  · intro i j hij
    rw [disjoint_iff]
    ext x y
    simp only [inf_adj, bot_adj, iff_false, not_and]
    intro h1 h2
    exact hij (Fin.ext (h1.2.symm.trans h2.2))

lemma walk_const {V W : Type*} {G : SimpleGraph V} (g : V → W)
    (h : ∀ x y, G.Adj x y → g x = g y) {u v : V} (p : G.Walk u v) : g u = g v := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Colour 0 is a disjoint union of cliques of size `≤ m`, so it has no `C_n` with `n > m`. -/
lemma no0 {m N n : ℕ} (hm : 0 < m) (i : Fin 3) (hi : i.val = 0)
    (f : Copy (cycleGraph n) (C m N i)) : n ≤ m := by
  set F := f.toHom
  have hblk : ∀ a b, (cycleGraph n).Adj a b → (F a).val / m = (F b).val / m := by
    intro a b hab
    obtain ⟨-, hc⟩ := F.map_adj hab
    rw [hi] at hc
    by_contra hne
    unfold code at hc
    rw [if_neg hne] at hc
    split_ifs at hc
  have hall : ∀ a b, (F a).val / m = (F b).val / m := fun a b =>
    walk_const (fun k => (F k).val / m) hblk (cycleGraph_preconnected a b).some
  have hinj : Function.Injective
      (fun k : Fin n => (⟨(F k).val % m, Nat.mod_lt _ hm⟩ : Fin m)) := by
    intro a b hab
    have hmod : (F a).val % m = (F b).val % m := congrArg Fin.val hab
    apply f.injective
    apply Fin.ext
    calc (F a).val = m * ((F a).val / m) + (F a).val % m := (Nat.div_add_mod _ _).symm
      _ = m * ((F b).val / m) + (F b).val % m := by rw [hall a b, hmod]
      _ = (F b).val := Nat.div_add_mod _ _
  simpa using Fintype.card_le_of_injective _ hinj

def phi (i p : ℕ) : ℕ := if i = 1 then p / 2 else p % 2

lemma valid12 (m i a b : ℕ) (ha : a / m < 4) (hb : b / m < 4) (hi0 : i ≠ 0)
    (h : code m a b = i) : decide (phi i (a / m) = 0) ≠ decide (phi i (b / m) = 0) := by
  unfold code at h
  generalize a / m = p at *
  generalize b / m = q at *
  have key : (phi i p = 0 ∧ phi i q ≠ 0) ∨ (phi i p ≠ 0 ∧ phi i q = 0) := by
    unfold phi
    split_ifs at h ⊢ <;> (try omega)
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- Colours 1 and 2 are bipartite when there are at most 4 blocks. -/
lemma col12 {m N n : ℕ} (hm : 0 < m) (hN : N ≤ 4 * m) (i : Fin 3) (hi : i.val ≠ 0)
    (f : Copy (cycleGraph n) (C m N i)) : (cycleGraph n).Colorable 2 := by
  have hv : ∀ x : Fin N, x.val / m < 4 := fun x =>
    (Nat.div_lt_iff_lt_mul hm).2 (by have := x.isLt; omega)
  let c : (C m N i).Coloring Bool :=
    Coloring.mk (fun x => decide (phi i.val (x.val / m) = 0)) (by
      intro x y hxy
      obtain ⟨-, hc⟩ := hxy
      exact valid12 m i.val x.val y.val (hv x) (hv y) hi hc)
  have c' : (cycleGraph n).Coloring Bool := c.comp f.toHom
  simpa using c'.colorable

end RC

theorem erdos_556.variants.odd_lower_bound (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3 := by
  obtain ⟨N0, hN0⟩ := RC.exists_N n
  unfold multicolourRamsey
  apply le_csInf
  · exact ⟨N0, hN0⟩
  intro N hN
  by_contra hlt
  have hN' : ∀ c : Fin 3 → SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, cycleGraph n ⊑ c i := hN
  have hN4 : N ≤ 4 * (n - 1) := by omega
  have hm : 0 < n - 1 := by omega
  obtain ⟨i, ⟨f⟩⟩ := hN' (RC.C (n - 1) N) (RC.C_col (n - 1) N)
  by_cases hi : i.val = 0
  · have := RC.no0 hm i hi f
    omega
  · have hcol := RC.col12 hm hN4 i hi f
    have h3 := chromaticNumber_cycleGraph_of_odd n (by omega) hodd
    have h2 := hcol.chromaticNumber_le
    rw [h3] at h2
    norm_num at h2

end Erdos556

#print axioms Erdos556.erdos_556.variants.odd_lower_bound
