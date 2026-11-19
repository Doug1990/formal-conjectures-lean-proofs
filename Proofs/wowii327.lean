import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Fin

/-! WOWII 327. Definitions restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean and
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean. -/

namespace SimpleGraph

section Dom

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

structure IsNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def dominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNDominatingSet n D}

structure IsNIndepDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}

end Dom

section WTD

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

def IsWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

end WTD

end SimpleGraph

namespace W327

open SimpleGraph Finset

/-- u = 0, v = 1, a_i = 2 + i, b_i = 7 + i. -/
def E : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,7),(1,8),(1,9),(1,10),(1,11),
   (2,10),(3,10),(4,7),(5,7),(6,10),(6,11)]

def R (i j : Fin 12) : Prop := (i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E

instance : DecidableRel R := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def G : SimpleGraph (Fin 12) where
  Adj := R
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by
    have : ∀ i : Fin 12, ¬ R i i := by decide
    exact this i h⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel R)

lemma conn : G.Connected := by
  have h : ∀ x : Fin 12, x = 0 ∨ G.Adj 0 x ∨ G.Adj 1 x := by decide
  have h01 : G.Adj 0 1 := by decide
  have r : ∀ x, G.Reachable 0 x := by
    intro x
    rcases h x with rfl | hx | hx
    · exact Reachable.refl _
    · exact hx.reachable
    · exact h01.reachable.trans hx.reachable
  exact { preconnected := fun x y => (r x).symm.trans (r y), nonempty := ⟨0⟩ }

lemma dom2 : G.dominationNumber = 2 := by
  unfold SimpleGraph.dominationNumber
  have hmem : 2 ∈ {n | ∃ D : Finset (Fin 12), G.IsNDominatingSet n D} := by
    refine ⟨{0, 1}, ⟨?_, by decide⟩⟩
    have : ∀ v : Fin 12, v ∈ ({0, 1} : Finset (Fin 12)) ∨
        ∃ w ∈ ({0, 1} : Finset (Fin 12)), G.Adj v w := by decide
    exact this
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨2, hmem⟩
  rintro n ⟨D, hD, hc⟩
  by_contra hlt
  have h1 : D.card ≤ 1 := by omega
  obtain ⟨w, hw⟩ := Finset.card_le_one_iff_subset_singleton.1 h1
  have key : ∀ w : Fin 12, ∃ v : Fin 12, v ≠ w ∧ ¬ G.Adj v w := by decide
  obtain ⟨v, hv1, hv2⟩ := key w
  rcases hD v with h | ⟨y, hy, hy2⟩
  · exact hv1 (Finset.mem_singleton.1 (hw h))
  · rw [Finset.mem_singleton.1 (hw hy)] at hy2
    exact hv2 hy2

def ind (s : Finset (Fin 12)) (n : ℕ) : ℕ :=
  if h : n < 12 then (if (⟨n, h⟩ : Fin 12) ∈ s then 1 else 0) else 0

lemma ind_fin (s : Finset (Fin 12)) (i : Fin 12) : ind s i.val = if i ∈ s then 1 else 0 := by
  unfold ind
  rw [dif_pos i.isLt]

lemma ind_le (s : Finset (Fin 12)) (n : ℕ) : ind s n ≤ 1 := by
  unfold ind
  split_ifs <;> omega

lemma card_ind (s : Finset (Fin 12)) : s.card = ind s 0 + ind s 1 + ind s 2 + ind s 3 +
    ind s 4 + ind s 5 + ind s 6 + ind s 7 + ind s 8 + ind s 9 + ind s 10 + ind s 11 := by
  have h1 : s.card = ∑ i : Fin 12, ind s i.val := by
    calc s.card = ∑ i : Fin 12, (if i ∈ s then 1 else 0) := by simp
      _ = ∑ i : Fin 12, ind s i.val := by simp only [ind_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => ind s n) 12] at h1
  simp only [sum_range_succ, sum_range_zero, zero_add] at h1
  exact h1

lemma mem_le_sum (f : ℕ → ℕ) (l : List ℕ) (n : ℕ) (h : n ∈ l) : f n ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

lemma dom_c (D : Finset (Fin 12)) (hD : G.IsDominating (D : Set (Fin 12))) (v : Fin 12)
    (n : ℕ) (hv : v.val = n) (l : List ℕ) (hl : ∀ w : Fin 12, G.Adj v w → w.val ∈ l) :
    1 ≤ ind D n + (l.map (ind D)).sum := by
  subst hv
  rcases hD v with h | ⟨w, hw, hadj⟩
  · have : ind D v.val = 1 := by rw [ind_fin, if_pos (Finset.mem_coe.1 h)]
    omega
  · have h1 := mem_le_sum (ind D) l w.val (hl w hadj)
    have h2 : ind D w.val = 1 := by rw [ind_fin, if_pos (Finset.mem_coe.1 hw)]
    omega

lemma edge_c (D : Finset (Fin 12)) (hI : G.IsIndepSet (D : Set (Fin 12))) (a b : Fin 12)
    (i j : ℕ) (ha : a.val = i) (hb : b.val = j) (h : G.Adj a b) : ind D i + ind D j ≤ 1 := by
  subst ha hb
  rw [ind_fin, ind_fin]
  split_ifs with h1 h2
  · exact absurd h (hI h1 h2 (G.ne_of_adj h))
  all_goals omega

lemma idom6 : G.indepDominationNumber = 6 := by
  unfold SimpleGraph.indepDominationNumber
  have hmem : 6 ∈ {n | ∃ D : Finset (Fin 12), G.IsNIndepDominatingSet n D} := by
    refine ⟨{0, 7, 8, 9, 10, 11}, ⟨?_, ?_, by decide⟩⟩
    · have : ∀ x ∈ ({0, 7, 8, 9, 10, 11} : Finset (Fin 12)),
          ∀ y ∈ ({0, 7, 8, 9, 10, 11} : Finset (Fin 12)), x ≠ y → ¬ G.Adj x y := by decide
      exact fun x hx y hy hxy => this x hx y hy hxy
    · have : ∀ v : Fin 12, v ∈ ({0, 7, 8, 9, 10, 11} : Finset (Fin 12)) ∨
          ∃ w ∈ ({0, 7, 8, 9, 10, 11} : Finset (Fin 12)), G.Adj v w := by decide
      exact this
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨6, hmem⟩
  rintro n ⟨D, hI, hD, hc⟩
  rw [← hc, card_ind D]
  have d0 := dom_c D hD 0 0 rfl [1, 2, 3, 4, 5, 6] (by decide)
  have d1 := dom_c D hD 1 1 rfl [0, 7, 8, 9, 10, 11] (by decide)
  have d2 := dom_c D hD 2 2 rfl [0, 10] (by decide)
  have d3 := dom_c D hD 3 3 rfl [0, 10] (by decide)
  have d4 := dom_c D hD 4 4 rfl [0, 7] (by decide)
  have d5 := dom_c D hD 5 5 rfl [0, 7] (by decide)
  have d6 := dom_c D hD 6 6 rfl [0, 10, 11] (by decide)
  have d7 := dom_c D hD 7 7 rfl [1, 4, 5] (by decide)
  have d8 := dom_c D hD 8 8 rfl [1] (by decide)
  have d9 := dom_c D hD 9 9 rfl [1] (by decide)
  have d10 := dom_c D hD 10 10 rfl [1, 2, 3, 6] (by decide)
  have d11 := dom_c D hD 11 11 rfl [1, 6] (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
  have e1 := edge_c D hI 0 1 0 1 rfl rfl (by decide)
  have e2 := edge_c D hI 0 2 0 2 rfl rfl (by decide)
  have e3 := edge_c D hI 0 3 0 3 rfl rfl (by decide)
  have e4 := edge_c D hI 0 4 0 4 rfl rfl (by decide)
  have e5 := edge_c D hI 0 5 0 5 rfl rfl (by decide)
  have e6 := edge_c D hI 0 6 0 6 rfl rfl (by decide)
  have e7 := edge_c D hI 1 7 1 7 rfl rfl (by decide)
  have e8 := edge_c D hI 1 8 1 8 rfl rfl (by decide)
  have e9 := edge_c D hI 1 9 1 9 rfl rfl (by decide)
  have e10 := edge_c D hI 1 10 1 10 rfl rfl (by decide)
  have e11 := edge_c D hI 1 11 1 11 rfl rfl (by decide)
  have e12 := edge_c D hI 2 10 2 10 rfl rfl (by decide)
  have e13 := edge_c D hI 3 10 3 10 rfl rfl (by decide)
  have e14 := edge_c D hI 4 7 4 7 rfl rfl (by decide)
  have e15 := edge_c D hI 5 7 5 7 rfl rfl (by decide)
  have e16 := edge_c D hI 6 10 6 10 rfl rfl (by decide)
  have e17 := edge_c D hI 6 11 6 11 rfl rfl (by decide)
  have i0 := ind_le D 0
  have i1 := ind_le D 1
  have i2 := ind_le D 2
  have i3 := ind_le D 3
  have i4 := ind_le D 4
  have i5 := ind_le D 5
  have i6 := ind_le D 6
  have i7 := ind_le D 7
  have i8 := ind_le D 8
  have i9 := ind_le D 9
  have i10 := ind_le D 10
  have i11 := ind_le D 11
  have c0 : ind D 0 = 0 ∨ ind D 0 = 1 := by omega
  have c1 : ind D 1 = 0 ∨ ind D 1 = 1 := by omega
  have c7 : ind D 7 = 0 ∨ ind D 7 = 1 := by omega
  have c10 : ind D 10 = 0 ∨ ind D 10 = 1 := by omega
  rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c7 with c7 | c7 <;>
    rcases c10 with c10 | c10 <;> omega

lemma min_of_priv {S : Finset (Fin 12)} (hS : IsTotalDominatingSet G S)
    (hp : ∀ x ∈ S, ∃ p : Fin 12, ∀ w ∈ S, G.Adj p w → w = x) :
    IsMinimalTotalDominatingSet G S := by
  refine ⟨hS, fun T hT hTD => ?_⟩
  obtain ⟨x, hxS, hxT⟩ := Finset.exists_of_ssubset hT
  obtain ⟨p, hp⟩ := hp x hxS
  obtain ⟨w, hw, hadj⟩ := hTD p
  have hwx := hp w ((Finset.ssubset_iff_subset_ne.1 hT).1 hw) hadj
  subst hwx
  exact hxT hw

end W327

namespace WrittenOnTheWallII.GraphConjecture327

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conjecture327 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hG : G.Connected)
      (_h : 3 * G.dominationNumber = G.indepDominationNumber),
      IsWellTotallyDominated G := by
  intro H
  have h3 : 3 * W327.G.dominationNumber = W327.G.indepDominationNumber := by
    rw [W327.dom2, W327.idom6]
  have hW := H (Fin 12) W327.G W327.conn h3
  have m1 : IsMinimalTotalDominatingSet W327.G {0, 1} :=
    W327.min_of_priv (by unfold IsTotalDominatingSet; decide) (by decide)
  have m2 : IsMinimalTotalDominatingSet W327.G {1, 7, 10} :=
    W327.min_of_priv (by unfold IsTotalDominatingSet; decide) (by decide)
  have := hW _ _ m1 m2
  exact absurd this (by decide)

end WrittenOnTheWallII.GraphConjecture327

#print axioms WrittenOnTheWallII.GraphConjecture327.conjecture327
