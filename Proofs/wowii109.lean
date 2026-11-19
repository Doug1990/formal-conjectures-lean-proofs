import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
Residue.lean and Induced.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    let (to_decrement, remaining) := rest.splitAt d
    let decremented := to_decrement.map (· - 1)
    (decremented ++ remaining).mergeSort (· ≥ ·)

theorem havelHakimiStep_length_cons (d : ℕ) (rest : List ℕ) :
    (havelHakimiStep (d :: rest)).length = rest.length := by
  grind [havelHakimiStep, List.length_mergeSort]

def residueAux : List ℕ → ℕ
  | [] => 0
  | 0 :: s => 1 + s.length
  | d :: rest => residueAux (havelHakimiStep (d :: rest))
termination_by l => l.length
decreasing_by
  simp_wf
  rw [havelHakimiStep_length_cons]

noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  residueAux ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

omit [Fintype α] in
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture109

open SimpleGraph Finset

/-! ### Havel–Hakimi computation helpers -/

lemma ms_eq (l m : List ℕ) (hp : l.Perm m) (hs : m.Pairwise (· ≥ ·)) :
    l.mergeSort (fun a b => decide (a ≥ b)) = m :=
  List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' (· ≥ ·) l) hs
    ((List.mergeSort_perm _ _).trans hp)

lemma hh (d : ℕ) (rest m : List ℕ)
    (hp : ((rest.take d).map (· - 1) ++ rest.drop d).Perm m)
    (hs : m.Pairwise (· ≥ ·)) : havelHakimiStep (d :: rest) = m := by
  simp only [havelHakimiStep, List.splitAt_eq]
  exact ms_eq _ _ hp hs

lemma ra_ne (d : ℕ) (rest : List ℕ) (hd : d ≠ 0) :
    residueAux (d :: rest) = residueAux (havelHakimiStep (d :: rest)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  rw [residueAux.eq_def]; rfl

lemma ra0 (s : List ℕ) : residueAux (0 :: s) = 1 + s.length := by
  rw [residueAux.eq_def]; rfl

lemma step (d : ℕ) (rest m : List ℕ) (hd : d ≠ 0)
    (hp : ((rest.take d).map (· - 1) ++ rest.drop d).Perm m)
    (hs : m.Pairwise (· ≥ ·)) : residueAux (d :: rest) = residueAux m := by
  rw [ra_ne d rest hd, hh d rest m hp hs]

lemma chain : residueAux [9, 9, 9, 9, 9, 9, 6, 6, 6, 6, 6, 6, 6] = 2 := by
  calc residueAux [9, 9, 9, 9, 9, 9, 6, 6, 6, 6, 6, 6, 6]
      = residueAux [8, 8, 8, 8, 8, 6, 6, 6, 5, 5, 5, 5] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [7, 7, 7, 7, 5, 5, 5, 5, 5, 5, 4] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [6, 6, 6, 5, 5, 4, 4, 4, 4, 4] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [5, 5, 4, 4, 4, 4, 4, 3, 3] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [4, 4, 3, 3, 3, 3, 3, 3] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [3, 3, 3, 3, 2, 2, 2] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [2, 2, 2, 2, 2, 2] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [2, 2, 2, 1, 1] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [1, 1, 1, 1] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [1, 1, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = 2 := by rw [ra0]; rfl

/-! ### The graph `K̄₇ ∨ (K₃ ⊔ K₃)` on `Fin 13`
Vertices `0..6` independent, cliques `{7,8,9}` and `{10,11,12}`. -/

def adjF (i j : Fin 13) : Prop :=
  i.val ≠ j.val ∧ ((i.val < 7 ∧ 7 ≤ j.val) ∨ (j.val < 7 ∧ 7 ≤ i.val) ∨
    (7 ≤ i.val ∧ 7 ≤ j.val ∧ i.val / 10 = j.val / 10))

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

def G : SimpleGraph (Fin 13) where
  Adj := adjF
  symm := ⟨fun x y h => by unfold adjF at *; omega⟩
  loopless := ⟨fun x h => by unfold adjF at h; omega⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adjF)

def f13 (v : Fin 13) : ℕ := if v.val < 7 then 6 else 9

lemma deg (v : Fin 13) : G.degree v = f13 v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  revert v
  decide

lemma resid : residue G = 2 := by
  unfold residue
  have hm : (Finset.univ.val.map fun v => G.degree v) =
      (([6, 6, 6, 6, 6, 6, 6, 9, 9, 9, 9, 9, 9] : List ℕ) : Multiset ℕ) := by
    rw [show (fun v => G.degree v) = f13 from funext deg]
    decide
  rw [hm, Multiset.coe_sort,
    ms_eq _ [9, 9, 9, 9, 9, 9, 6, 6, 6, 6, 6, 6, 6] (by decide) (by decide)]
  exact chain

lemma connected : G.Connected := by
  have v7 : (7 : Fin 13).val = 7 := rfl
  have v0 : (0 : Fin 13).val = 0 := rfl
  have r7 : ∀ u : Fin 13, G.Reachable u 7 := by
    intro u
    have hu' := u.isLt
    by_cases h1 : u.val < 7
    · exact (show G.Adj u 7 by
        show adjF u 7
        unfold adjF; rw [v7]; omega).reachable
    · by_cases h2 : u = 7
      · subst h2; rfl
      · have hu : u.val ≠ 7 := fun e => h2 (Fin.ext e)
        have a1 : G.Adj u 0 := by
          show adjF u 0
          unfold adjF; rw [v0]; omega
        have a2 : G.Adj 0 7 := by decide
        exact a1.reachable.trans a2.reachable
  rw [connected_iff]
  exact ⟨fun u v => (r7 u).trans (r7 v).symm, ⟨0⟩⟩

lemma alpha_ge : 7 ≤ G.indepNum := by
  have hI : G.IsIndepSet ((univ.filter (fun v : Fin 13 => v.val < 7) : Finset _) : Set _) := by
    intro x hx y hy _ h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    change adjF x y at h
    unfold adjF at h
    omega
  have hc : (univ.filter (fun v : Fin 13 => v.val < 7)).card = 7 := by decide
  rw [← hc]
  exact hI.card_le_indepNum

lemma b_le : largestInducedBipartiteSubgraphSize G ≤ 9 := by
  unfold largestInducedBipartiteSubgraphSize
  apply csSup_le'
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring G s).1 hs
  have key : ∀ p q r : Fin 2, p ≠ q → q ≠ r → p ≠ r → False := by decide
  have tri : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → adjF x y → adjF y z → adjF x z → False :=
    fun x y z hx hy hz h1 h2 h3 => key _ _ _ (hc x hx y hy h1) (hc y hy z hz h2) (hc x hx z hz h3)
  set I := s.filter (fun v : Fin 13 => v.val < 7) with hI
  set A := s.filter (fun v : Fin 13 => 7 ≤ v.val ∧ v.val < 10) with hA
  set B := s.filter (fun v : Fin 13 => 10 ≤ v.val) with hB
  have hsub : s ⊆ I ∪ (A ∪ B) := by
    intro x hx
    simp only [hI, hA, hB, mem_union, mem_filter, hx, true_and]
    have := x.isLt
    omega
  have hcard : s.card ≤ I.card + (A.card + B.card) :=
    (card_le_card hsub).trans ((card_union_le _ _).trans (by
      have := card_union_le A B; omega))
  have cI : I.card ≤ 7 := by
    have h7 : (univ.filter (fun v : Fin 13 => v.val < 7)).card = 7 := by decide
    rw [← h7]
    apply card_le_card
    intro x hx
    simp only [hI, mem_filter] at hx
    simp [hx.2]
  have cA : A.card ≤ 3 := by
    have h3 : (univ.filter (fun v : Fin 13 => 7 ≤ v.val ∧ v.val < 10)).card = 3 := by decide
    rw [← h3]
    apply card_le_card
    intro x hx
    simp only [hA, mem_filter] at hx
    simp [hx.2]
  have cB : B.card ≤ 3 := by
    have h3 : (univ.filter (fun v : Fin 13 => 10 ≤ v.val)).card = 3 := by decide
    rw [← h3]
    apply card_le_card
    intro x hx
    simp only [hB, mem_filter] at hx
    simp [hx.2]
  by_cases hIe : I = ∅
  · rw [hIe, card_empty] at hcard
    omega
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 hIe
    simp only [hI, mem_filter] at hi
    have cA1 : A.card ≤ 1 := by
      by_contra hlt
      obtain ⟨a1, h1, a2, h2, hne⟩ := one_lt_card.1 (by omega : 1 < A.card)
      simp only [hA, mem_filter] at h1 h2
      have nv : a1.val ≠ a2.val := fun e => hne (Fin.ext e)
      exact tri i a1 a2 hi.1 h1.1 h2.1 (by unfold adjF; omega) (by unfold adjF; omega)
        (by unfold adjF; omega)
    have cB1 : B.card ≤ 1 := by
      by_contra hlt
      obtain ⟨a1, h1, a2, h2, hne⟩ := one_lt_card.1 (by omega : 1 < B.card)
      simp only [hB, mem_filter] at h1 h2
      have nv : a1.val ≠ a2.val := fun e => hne (Fin.ext e)
      have l1 := a1.isLt
      have l2 := a2.isLt
      exact tri i a1 a2 hi.1 h1.1 h2.1 (by unfold adjF; omega) (by unfold adjF; omega)
        (by unfold adjF; omega)
    omega

theorem conjecture109 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋ := by
  intro h
  have H := h (Fin 13) G connected
  have hb : b G ≤ 9 := by
    unfold b
    exact_mod_cast b_le
  have ha : (7 : ℝ) ≤ G.indepNum := by exact_mod_cast alpha_ge
  have hx : ((residue G : ℝ) + 2 * b G) / 3 < ((7 : ℤ) : ℝ) := by
    rw [resid]; push_cast; linarith
  have hfl : ⌊((residue G : ℝ) + 2 * b G) / 3⌋ ≤ 6 := by
    have := Int.floor_lt.2 hx
    omega
  have hfl' : ((⌊((residue G : ℝ) + 2 * b G) / 3⌋ : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hfl
  linarith

end WrittenOnTheWallII.GraphConjecture109

#print axioms WrittenOnTheWallII.GraphConjecture109.conjecture109
