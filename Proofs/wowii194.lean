import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
Independence.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture194

open SimpleGraph Finset

/-! The counterexample: K = {0,…,10} is a clique, A = {11,…,14} is independent and complete
to K, and the leaves 15, 16, 17 hang at 11, 12, 14. -/

def adjF (i j : Fin 18) : Prop :=
  (i.val < 11 ∧ j.val < 11 ∧ i.val ≠ j.val) ∨
  (i.val < 11 ∧ 11 ≤ j.val ∧ j.val ≤ 14) ∨ (j.val < 11 ∧ 11 ≤ i.val ∧ i.val ≤ 14) ∨
  (i.val = 15 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 15) ∨
  (i.val = 16 ∧ j.val = 12) ∨ (i.val = 12 ∧ j.val = 16) ∨
  (i.val = 17 ∧ j.val = 14) ∨ (i.val = 14 ∧ j.val = 17)

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_symm (i j : Fin 18) (h : adjF i j) : adjF j i := by
  unfold adjF at *
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨h.2.1, h.1, fun e => h.2.2 e.symm⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))))

lemma adjF_irrefl (i : Fin 18) : ¬ adjF i i := by
  unfold adjF; omega

def G : SimpleGraph (Fin 18) where
  Adj := adjF
  symm := ⟨fun x y h => adjF_symm x y h⟩
  loopless := ⟨fun x h => adjF_irrefl x h⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma connected : G.Connected := by
  have A : ∀ i j : Fin 18, adjF i j → G.Reachable i j := fun i j h => Adj.reachable h
  have hR : ∀ i : Fin 18, G.Reachable 0 i := by
    intro i
    by_cases h0 : i = 0
    · subst h0; exact Reachable.refl _
    by_cases h1 : i.val < 15
    · exact A 0 i (by
        have : i.val ≠ 0 := fun e => h0 (Fin.ext e)
        unfold adjF; simp only [Fin.val_zero]; omega)
    · have h15 : i.val = 15 ∨ i.val = 16 ∨ i.val = 17 := by omega
      rcases h15 with e | e | e
      · have : i = 15 := Fin.ext e
        subst this; exact (A 0 11 (by decide)).trans (A 11 15 (by decide))
      · have : i = 16 := Fin.ext e
        subst this; exact (A 0 12 (by decide)).trans (A 12 16 (by decide))
      · have : i = 17 := Fin.ext e
        subst this; exact (A 0 14 (by decide)).trans (A 14 17 (by decide))
  rw [connected_iff]
  exact ⟨fun u v => (hR u).symm.trans (hR v), ⟨0⟩⟩

/-! ### `α(G) ≤ 4` via a cover by 4 cliques -/

def gc (x : Fin 18) : ℕ :=
  if x.val = 11 ∨ x.val = 15 then 0
  else if x.val = 12 ∨ x.val = 16 then 1
  else if x.val = 14 ∨ x.val = 17 then 2
  else 3

lemma gc_lt (x : Fin 18) : gc x < 4 := by
  unfold gc; split_ifs <;> omega

set_option maxRecDepth 100000 in
lemma gc_clique' : ∀ x y : Fin 18, x ≠ y → gc x = gc y → adjF x y := by decide

lemma gc_clique (x y : Fin 18) (hne : x ≠ y) (hg : gc x = gc y) : adjF x y :=
  gc_clique' x y hne hg

lemma indep_le : G.indepNum ≤ 4 := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  have hle := Finset.card_le_card_of_injOn gc (t := range 4) (s := s)
    (fun i _ => mem_coe.2 (mem_range.2 (gc_lt _))) ?_
  · rw [card_range] at hle
    exact hle
  · intro x hx y hy hg
    by_contra e
    exact hs.isIndepSet hx hy e (gc_clique x y e hg)

/-! ### `Σ_v α(N(v)) ≥ 54` via explicit witnesses -/

def wit (v : Fin 18) : Finset (Fin 18) :=
  if v.val < 11 then {11, 12, 13, 14}
  else match v.val with
  | 11 => {0, 15}
  | 12 => {0, 16}
  | 13 => {0}
  | 14 => {0, 17}
  | 15 => {11}
  | 16 => {12}
  | _ => {14}

set_option maxRecDepth 100000 in
lemma wit_adj : ∀ v : Fin 18, ∀ x ∈ wit v, adjF v x := by decide

set_option maxRecDepth 100000 in
lemma wit_ind : ∀ v : Fin 18, ∀ x ∈ wit v, ∀ y ∈ wit v, ¬ adjF x y := by decide

set_option maxRecDepth 100000 in
lemma wit_sum : ∑ v : Fin 18, (wit v).card = 54 := by decide

lemma inc_ge (v : Fin 18) : (wit v).card ≤ indepNeighborsCard G v := by
  classical
  unfold indepNeighborsCard
  have hw1 : ∀ x ∈ wit v, adjF v x := wit_adj v
  have hw2 : ∀ x ∈ wit v, ∀ y ∈ wit v, ¬ adjF x y := wit_ind v
  have hcard : ((wit v).subtype (fun x => x ∈ G.neighborSet v)).card = (wit v).card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact hw1 x hx
  rw [← hcard]
  apply IsIndepSet.card_le_indepNum
  intro x hx y hy _ hadj
  exact hw2 x.1 (Finset.mem_subtype.1 hx) y.1 (Finset.mem_subtype.1 hy) hadj

lemma sum_ge : 54 ≤ ∑ v : Fin 18, indepNeighborsCard G v :=
  calc 54 = ∑ v : Fin 18, (wit v).card := wit_sum.symm
    _ ≤ _ := sum_le_sum fun v _ => inc_ge v

lemma hyp : (G.indepNum : ℝ) ≤ 1 + averageIndepNeighbors G := by
  unfold averageIndepNeighbors indepNeighbors
  have h18 : (Fintype.card (Fin 18) : ℝ) = 18 := by simp
  rw [h18]
  have A : (54 : ℝ) ≤ ∑ v : Fin 18, (indepNeighborsCard G v : ℝ) := by exact_mod_cast sum_ge
  have B : (G.indepNum : ℝ) ≤ 4 := by exact_mod_cast indep_le
  have C : 3 ≤ (∑ v : Fin 18, (indepNeighborsCard G v : ℝ)) / 18 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  linarith

/-! ### No Hamiltonian path: three pendant vertices -/

lemma two_nbrs {V : Type*} {H : SimpleGraph V} {a b : V} (p : H.Walk a b) (hp : p.IsPath)
    (v : V) (hv : v ∈ p.support) (ha : v ≠ a) (hb : v ≠ b) :
    ∃ u w, u ≠ w ∧ H.Adj v u ∧ H.Adj v w := by
  induction p with
  | nil =>
    simp at hv
    exact absurd hv ha
  | @cons x c y h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact absurd rfl ha
    · by_cases hvc : v = c
      · subst hvc
        cases q with
        | nil => exact absurd rfl hb
        | cons h' q' =>
          refine ⟨x, _, ?_, h.symm, h'⟩
          intro e
          apply hp.2
          rw [e, Walk.support_cons]
          exact List.mem_cons_of_mem _ q'.start_mem_support
      · exact ih hp.1 hv hvc hb

lemma pendant (v p : Fin 18) (h : ∀ u, adjF v u → u = p) :
    ∀ u w, G.Adj v u → G.Adj v w → u = w :=
  fun u w hu hw => (h u hu).trans (h w hw).symm

lemma ham_false {a b : Fin 18} (p : G.Walk a b) (hp : p.IsHamiltonian) : False := by
  have hpath := hp.isPath
  have key : ∀ v : Fin 18, (∀ u w, G.Adj v u → G.Adj v w → u = w) → v = a ∨ v = b := by
    intro v hv
    by_contra hc
    rw [not_or] at hc
    obtain ⟨u, w, hne, h1, h2⟩ := two_nbrs p hpath v (hp.mem_support v) hc.1 hc.2
    exact hne (hv u w h1 h2)
  have p15 := key 15 (pendant 15 11 (by decide))
  have p16 := key 16 (pendant 16 12 (by decide))
  have p17 := key 17 (pendant 17 14 (by decide))
  rcases p15 with h8 | h8 <;> rcases p16 with h9 | h9 <;> rcases p17 with h10 | h10 <;>
    first
    | exact absurd (h8.trans h9.symm) (by decide)
    | exact absurd (h8.trans h10.symm) (by decide)
    | exact absurd (h9.trans h10.symm) (by decide)

theorem conjecture194 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (G.indepNum : ℝ) ≤ 1 + averageIndepNeighbors G →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  intro h
  obtain ⟨a, b, p, hp⟩ := h (Fin 18) G connected hyp
  exact ham_false p hp

end WrittenOnTheWallII.GraphConjecture194

#print axioms WrittenOnTheWallII.GraphConjecture194.conjecture194
