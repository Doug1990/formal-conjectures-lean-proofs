import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture59

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

lemma chain :
    residueAux [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1] = 10 := by
  calc residueAux [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1]
      = residueAux [5, 5, 5, 5, 5, 4, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [4, 4, 4, 4, 4, 4, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [4, 3, 3, 3, 3, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [3, 3, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = residueAux [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
        step _ _ _ (by decide) (by decide) (by decide)
    _ = 10 := by rw [ra0]; rfl

/-! ### The graph on `Fin 18`
Chain core: `x_i = i` (`i < 5`), `y_j = 5 + j`, `x_i ~ y_j` iff `j < k_i`, `k = [5,5,5,4,2]`.
Hub `10` adjacent to every other vertex (so `11..17` are leaves). -/

def cA (u v : ℕ) : Prop :=
  u < 5 ∧ 5 ≤ v ∧ v < 10 ∧ (u ≤ 2 ∨ (u = 3 ∧ v ≤ 8) ∨ (u = 4 ∧ v ≤ 6))

def adjF (i j : Fin 18) : Prop :=
  i.val ≠ j.val ∧ (cA i.val j.val ∨ cA j.val i.val ∨ i.val = 10 ∨ j.val = 10)

instance : DecidableRel adjF := fun i j => by unfold adjF cA; infer_instance

def G : SimpleGraph (Fin 18) where
  Adj := adjF
  symm := ⟨fun x y h => by unfold adjF cA at *; omega⟩
  loopless := ⟨fun x h => by unfold adjF at h; omega⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adjF)

def f18 (v : Fin 18) : ℕ :=
  if v.val < 3 then 6 else if v.val = 3 then 5 else if v.val = 4 then 3 else
  if v.val < 7 then 6 else if v.val < 9 then 5 else if v.val = 9 then 4 else
  if v.val = 10 then 17 else 1

lemma deg (v : Fin 18) : G.degree v = f18 v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  revert v
  decide

lemma resid : residue G = 10 := by
  unfold residue
  have hm : (Finset.univ.val.map fun v => G.degree v) =
      (([6, 6, 6, 5, 3, 6, 6, 5, 5, 4, 17, 1, 1, 1, 1, 1, 1, 1] : List ℕ) : Multiset ℕ) := by
    rw [show (fun v => G.degree v) = f18 from funext deg]
    decide
  rw [hm, Multiset.coe_sort,
    ms_eq _ [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1] (by decide) (by decide)]
  exact chain

lemma connected : G.Connected := by
  have v10 : (10 : Fin 18).val = 10 := rfl
  have r : ∀ u : Fin 18, G.Reachable u 10 := by
    intro u
    by_cases h : u = 10
    · subst h; rfl
    · have hu : u.val ≠ 10 := fun e => h (Fin.ext e)
      exact (show G.Adj u 10 by
        show adjF u 10
        unfold adjF; rw [v10]; omega).reachable
  rw [connected_iff]
  exact ⟨fun u v => (r u).trans (r v).symm, ⟨0⟩⟩

/-! ### `b G ≥ 17` -/

def S17 : Finset (Fin 18) := univ.filter (fun v : Fin 18 => v.val ≠ 10)

lemma b_ge : (17 : ℝ) ≤ b G := by
  have hbip : (G.induce (S17 : Set (Fin 18))).IsBipartite := by
    refine ⟨Coloring.mk (fun x => (if x.1.val < 5 ∨ 10 < x.1.val then 0 else 1 : Fin 2)) ?_⟩
    intro x y hxy
    have hx : x.1.val ≠ 10 := (mem_filter.1 (mem_coe.1 x.2)).2
    have hy : y.1.val ≠ 10 := (mem_filter.1 (mem_coe.1 y.2)).2
    have h : adjF x.1 y.1 := hxy
    have lx := x.1.isLt
    have ly := y.1.isLt
    unfold adjF cA at h
    split_ifs <;> first | decide | (exfalso; omega)
  have hcard : S17.card = 17 := by decide
  unfold b largestInducedBipartiteSubgraphSize
  have : 17 ≤ sSup { n | ∃ s : Finset (Fin 18),
      (G.induce (s : Set _)).IsBipartite ∧ s.card = n } := by
    apply le_csSup
    · refine ⟨Fintype.card (Fin 18), ?_⟩
      rintro _ ⟨t, -, rfl⟩
      exact card_le_univ t
    · exact ⟨S17, hbip, hcard⟩
  exact_mod_cast this

/-! ### Largest induced forest `≤ 13` -/

lemma del_adj {W : Type*} {H : SimpleGraph W} {a b x y : W} (h : H.Adj x y)
    (h1 : ¬ (x = a ∧ y = b)) (h2 : ¬ (x = b ∧ y = a)) :
    (H.deleteEdges {s(a, b)}).Adj x y := by
  rw [deleteEdges_adj]
  refine ⟨h, ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

lemma not_acyc_tri {W : Type*} (H : SimpleGraph W) {a b c : W} (hab : H.Adj a b)
    (hbc : H.Adj b c) (hca : H.Adj c a) : ¬ H.IsAcyclic := by
  intro h
  rw [isAcyclic_iff_forall_adj_isBridge] at h
  have hb := h hab
  rw [isBridge_iff] at hb
  apply hb
  have hcb : c ≠ b := fun e => H.loopless.irrefl b (e ▸ hbc)
  have hca' : c ≠ a := H.ne_of_adj hca
  have hab' : a ≠ b := H.ne_of_adj hab
  have e1 : (H.deleteEdges {s(a, b)}).Adj a c :=
    del_adj hca.symm (fun ⟨_, e⟩ => hcb e) (fun ⟨e, _⟩ => hab' e)
  have e2 : (H.deleteEdges {s(a, b)}).Adj c b :=
    del_adj hbc.symm (fun ⟨e, _⟩ => hca' e) (fun ⟨e, _⟩ => hcb e)
  exact e1.reachable.trans e2.reachable

lemma not_acyc_c4 {W : Type*} (H : SimpleGraph W) {a b c d : W} (hab : H.Adj a b)
    (hbc : H.Adj b c) (hcd : H.Adj c d) (hda : H.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ H.IsAcyclic := by
  intro h
  rw [isAcyclic_iff_forall_adj_isBridge] at h
  have hb := h hab
  rw [isBridge_iff] at hb
  apply hb
  have hab' : a ≠ b := H.ne_of_adj hab
  have hda' : d ≠ a := H.ne_of_adj hda
  have e1 : (H.deleteEdges {s(a, b)}).Adj a d :=
    del_adj hda.symm (fun ⟨_, e⟩ => hbd e.symm) (fun ⟨e, _⟩ => hab' e)
  have e2 : (H.deleteEdges {s(a, b)}).Adj d c :=
    del_adj hcd.symm (fun ⟨e, _⟩ => hda' e) (fun ⟨e, _⟩ => hbd e.symm)
  have e3 : (H.deleteEdges {s(a, b)}).Adj c b :=
    del_adj hbc.symm (fun ⟨e, _⟩ => hac e.symm) (fun ⟨e1, e2⟩ => hac (e1.trans e2).symm)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)

def ind (s : Finset (Fin 18)) (n : ℕ) : ℕ :=
  if h : n < 18 then (if (⟨n, h⟩ : Fin 18) ∈ s then 1 else 0) else 0

lemma ind_fin (s : Finset (Fin 18)) (i : Fin 18) : ind s i.val = if i ∈ s then 1 else 0 := by
  unfold ind
  rw [dif_pos i.isLt]

lemma ind_le (s : Finset (Fin 18)) (n : ℕ) : ind s n ≤ 1 := by
  unfold ind
  split_ifs <;> omega

lemma card_ind (s : Finset (Fin 18)) : s.card = ind s 0 + ind s 1 + ind s 2 + ind s 3 +
    ind s 4 + ind s 5 + ind s 6 + ind s 7 + ind s 8 + ind s 9 + ind s 10 + ind s 11 +
    ind s 12 + ind s 13 + ind s 14 + ind s 15 + ind s 16 + ind s 17 := by
  have h1 : s.card = ∑ i : Fin 18, ind s i.val := by
    calc s.card = ∑ i : Fin 18, (if i ∈ s then 1 else 0) := by simp
      _ = ∑ i : Fin 18, ind s i.val := by simp only [ind_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => ind s n) 18] at h1
  simp only [sum_range_succ, sum_range_zero, zero_add] at h1
  exact h1

lemma filt_card (s : Finset (Fin 18)) (p : ℕ → Prop) [DecidablePred p] :
    (s.filter (fun v : Fin 18 => p v.val)).card =
      ∑ n ∈ range 18, (if p n then ind s n else 0) := by
  calc (s.filter (fun v : Fin 18 => p v.val)).card
      = ∑ a ∈ s, (if p a.val then 1 else 0) := by rw [Finset.card_filter]
    _ = ∑ a : Fin 18, (if a ∈ s then (if p a.val then 1 else 0) else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ a : Fin 18, (if p a.val then ind s a.val else 0) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ind_fin]
        split_ifs <;> rfl
    _ = _ := Fin.sum_univ_eq_sum_range (fun n => if p n then ind s n else 0) 18

def yr (s : Finset (Fin 18)) (n : ℕ) : Finset (Fin 18) :=
  s.filter (fun v : Fin 18 => 5 ≤ v.val ∧ v.val < 5 + n)

lemma arith59 (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 h : ℕ)
    (bx0 : x0 ≤ 1) (bx1 : x1 ≤ 1) (bx2 : x2 ≤ 1) (bx3 : x3 ≤ 1) (bx4 : x4 ≤ 1)
    (by0 : y0 ≤ 1) (by1 : y1 ≤ 1) (by2 : y2 ≤ 1) (by3 : y3 ≤ 1) (by4 : y4 ≤ 1) (bh : h ≤ 1)
    (p01 : x0 + x1 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 ≤ 1)
    (p02 : x0 + x2 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 ≤ 1)
    (p12 : x1 + x2 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 ≤ 1)
    (p03 : x0 + x3 ≤ 1 ∨ y0 + y1 + y2 + y3 ≤ 1)
    (p13 : x1 + x3 ≤ 1 ∨ y0 + y1 + y2 + y3 ≤ 1)
    (p23 : x2 + x3 ≤ 1 ∨ y0 + y1 + y2 + y3 ≤ 1)
    (p04 : x0 + x4 ≤ 1 ∨ y0 + y1 ≤ 1) (p14 : x1 + x4 ≤ 1 ∨ y0 + y1 ≤ 1)
    (p24 : x2 + x4 ≤ 1 ∨ y0 + y1 ≤ 1) (p34 : x3 + x4 ≤ 1 ∨ y0 + y1 ≤ 1)
    (t0 : h + x0 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 = 0)
    (t1 : h + x1 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 = 0)
    (t2 : h + x2 ≤ 1 ∨ y0 + y1 + y2 + y3 + y4 = 0)
    (t3 : h + x3 ≤ 1 ∨ y0 + y1 + y2 + y3 = 0)
    (t4 : h + x4 ≤ 1 ∨ y0 + y1 = 0) :
    x0 + x1 + x2 + x3 + x4 + y0 + y1 + y2 + y3 + y4 + h ≤ 6 := by
  have e0 : x0 = 0 ∨ x0 = 1 := by omega
  have e1 : x1 = 0 ∨ x1 = 1 := by omega
  have e2 : x2 = 0 ∨ x2 = 1 := by omega
  have e3 : x3 = 0 ∨ x3 = 1 := by omega
  have e4 : x4 = 0 ∨ x4 = 1 := by omega
  rcases e0 with rfl | rfl <;> rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;>
    rcases e3 with rfl | rfl <;> rcases e4 with rfl | rfl <;> omega

lemma forest_card (s : Finset (Fin 18)) (hs : (G.induce (s : Set (Fin 18))).IsAcyclic) :
    s.card ≤ 13 := by
  have adjI : ∀ i j : Fin 18, (hi : i ∈ s) → (hj : j ∈ s) → adjF i j →
      (G.induce (s : Set _)).Adj ⟨i, hi⟩ ⟨j, hj⟩ := fun i j _ _ h => h
  have c4b : ∀ (i j : ℕ) (hi : i < 18) (hj : j < 18) (n : ℕ), i ≠ j →
      (∀ v : Fin 18, 5 ≤ v.val → v.val < 5 + n → adjF ⟨i, hi⟩ v ∧ adjF ⟨j, hj⟩ v) →
      ind s i + ind s j ≤ 1 ∨ (yr s n).card ≤ 1 := by
    intro i j hi hj n hij hadj
    by_cases hsi : (⟨i, hi⟩ : Fin 18) ∈ s
    · by_cases hsj : (⟨j, hj⟩ : Fin 18) ∈ s
      · right
        rw [card_le_one]
        intro a ha c hc
        by_contra hne
        simp only [yr, mem_filter] at ha hc
        obtain ⟨hia, hja⟩ := hadj a ha.2.1 ha.2.2
        obtain ⟨hic, hjc⟩ := hadj c hc.2.1 hc.2.2
        exact not_acyc_c4 _ (adjI _ _ hsi ha.1 hia)
          (adjI _ _ ha.1 hsj (show adjF a ⟨j, hj⟩ from G.adj_symm hja))
          (adjI _ _ hsj hc.1 hjc) (adjI _ _ hc.1 hsi (show adjF c ⟨i, hi⟩ from G.adj_symm hic))
          (fun e => hij (by simpa using e)) (fun e => hne (by simpa using e)) hs
      · left
        have e1 : ind s i = ind s (⟨i, hi⟩ : Fin 18).val := rfl
        have e2 : ind s j = ind s (⟨j, hj⟩ : Fin 18).val := rfl
        rw [e1, e2, ind_fin, ind_fin, if_neg hsj]
        split_ifs <;> omega
    · left
      have e1 : ind s i = ind s (⟨i, hi⟩ : Fin 18).val := rfl
      have e2 : ind s j = ind s (⟨j, hj⟩ : Fin 18).val := rfl
      rw [e1, e2, ind_fin, ind_fin, if_neg hsi]
      split_ifs <;> omega
  have trb : ∀ (i : ℕ) (hi : i < 18) (n : ℕ), n ≤ 5 → i ≠ 10 →
      (∀ v : Fin 18, 5 ≤ v.val → v.val < 5 + n → adjF ⟨i, hi⟩ v) →
      ind s 10 + ind s i ≤ 1 ∨ (yr s n).card = 0 := by
    intro i hi n hn hi10 hadj
    have hh : (⟨10, by omega⟩ : Fin 18) = 10 := rfl
    by_cases hsh : (10 : Fin 18) ∈ s
    · by_cases hsi : (⟨i, hi⟩ : Fin 18) ∈ s
      · right
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro a ha
        simp only [yr, mem_filter] at ha
        obtain ⟨_, ha1, ha2⟩ := ha
        have h1 : adjF 10 ⟨i, hi⟩ := by
          refine ⟨?_, Or.inr (Or.inr (Or.inl rfl))⟩
          show (10 : ℕ) ≠ i
          omega
        have h3 : adjF a 10 := by
          refine ⟨?_, Or.inr (Or.inr (Or.inr rfl))⟩
          show a.val ≠ 10
          omega
        exact not_acyc_tri _ (adjI _ _ hsh hsi h1) (adjI _ _ hsi ‹_› (hadj a ha1 ha2))
          (adjI _ _ ‹_› hsh h3) hs
      · left
        have e1 : ind s i = ind s (⟨i, hi⟩ : Fin 18).val := rfl
        have e2 : ind s 10 = ind s (10 : Fin 18).val := rfl
        rw [e1, e2, ind_fin, ind_fin, if_neg hsi]
        split_ifs <;> omega
    · left
      have e1 : ind s i = ind s (⟨i, hi⟩ : Fin 18).val := rfl
      have e2 : ind s 10 = ind s (10 : Fin 18).val := rfl
      rw [e1, e2, ind_fin, ind_fin, if_neg hsh]
      split_ifs <;> omega
  have y2 : (yr s 2).card = ind s 5 + ind s 6 := by
    unfold yr
    rw [filt_card s (fun n => 5 ≤ n ∧ n < 5 + 2)]
    simp [sum_range_succ]
  have y4 : (yr s 4).card = ind s 5 + ind s 6 + ind s 7 + ind s 8 := by
    unfold yr
    rw [filt_card s (fun n => 5 ≤ n ∧ n < 5 + 4)]
    simp [sum_range_succ]
    try omega
  have y5 : (yr s 5).card = ind s 5 + ind s 6 + ind s 7 + ind s 8 + ind s 9 := by
    unfold yr
    rw [filt_card s (fun n => 5 ≤ n ∧ n < 5 + 5)]
    simp [sum_range_succ]
    try omega
  have ad : ∀ (i : ℕ) (hi : i < 18) (n : ℕ), (∀ v : ℕ, 5 ≤ v → v < 5 + n → v < 18 → cA i v) →
      ∀ v : Fin 18, 5 ≤ v.val → v.val < 5 + n → adjF ⟨i, hi⟩ v := by
    intro i hi n h v h1 h2
    have := h v.val h1 h2 v.isLt
    unfold adjF
    unfold cA at this
    dsimp only
    unfold cA
    omega
  have pr : ∀ (i j : ℕ) (hi : i < 18) (hj : j < 18) (n : ℕ), i ≠ j →
      (∀ v : ℕ, 5 ≤ v → v < 5 + n → v < 18 → cA i v ∧ cA j v) →
      ind s i + ind s j ≤ 1 ∨ (yr s n).card ≤ 1 := by
    intro i j hi hj n hij h
    exact c4b i j hi hj n hij (fun v h1 h2 =>
      ⟨ad i hi n (fun w a b c => (h w a b c).1) v h1 h2,
       ad j hj n (fun w a b c => (h w a b c).2) v h1 h2⟩)
  have p01 := pr 0 1 (by omega) (by omega) 5 (by omega) (by intro v; unfold cA; omega)
  have p02 := pr 0 2 (by omega) (by omega) 5 (by omega) (by intro v; unfold cA; omega)
  have p12 := pr 1 2 (by omega) (by omega) 5 (by omega) (by intro v; unfold cA; omega)
  have p03 := pr 0 3 (by omega) (by omega) 4 (by omega) (by intro v; unfold cA; omega)
  have p13 := pr 1 3 (by omega) (by omega) 4 (by omega) (by intro v; unfold cA; omega)
  have p23 := pr 2 3 (by omega) (by omega) 4 (by omega) (by intro v; unfold cA; omega)
  have p04 := pr 0 4 (by omega) (by omega) 2 (by omega) (by intro v; unfold cA; omega)
  have p14 := pr 1 4 (by omega) (by omega) 2 (by omega) (by intro v; unfold cA; omega)
  have p24 := pr 2 4 (by omega) (by omega) 2 (by omega) (by intro v; unfold cA; omega)
  have p34 := pr 3 4 (by omega) (by omega) 2 (by omega) (by intro v; unfold cA; omega)
  have t0 := trb 0 (by omega) 5 (by omega) (by omega) (ad 0 (by omega) 5 (by intro v; unfold cA; omega))
  have t1 := trb 1 (by omega) 5 (by omega) (by omega) (ad 1 (by omega) 5 (by intro v; unfold cA; omega))
  have t2 := trb 2 (by omega) 5 (by omega) (by omega) (ad 2 (by omega) 5 (by intro v; unfold cA; omega))
  have t3 := trb 3 (by omega) 4 (by omega) (by omega) (ad 3 (by omega) 4 (by intro v; unfold cA; omega))
  have t4 := trb 4 (by omega) 2 (by omega) (by omega) (ad 4 (by omega) 2 (by intro v; unfold cA; omega))
  rw [y5] at p01 p02 p12 t0 t1 t2
  rw [y4] at p03 p13 p23 t3
  rw [y2] at p04 p14 p24 p34 t4
  have key := arith59 _ _ _ _ _ _ _ _ _ _ _ (ind_le s 0) (ind_le s 1) (ind_le s 2)
    (ind_le s 3) (ind_le s 4) (ind_le s 5) (ind_le s 6) (ind_le s 7) (ind_le s 8)
    (ind_le s 9) (ind_le s 10) p01 p02 p12 p03 p13 p23 p04 p14 p24 p34 t0 t1 t2 t3 t4
  have hc := card_ind s
  have l11 := ind_le s 11
  have l12 := ind_le s 12
  have l13 := ind_le s 13
  have l14 := ind_le s 14
  have l15 := ind_le s 15
  have l16 := ind_le s 16
  have l17 := ind_le s 17
  omega

lemma forest_le : G.largestInducedForestSize ≤ 13 := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro _ ⟨s, hs, rfl⟩
  exact forest_card s hs

theorem conjecture59 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_ : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  intro h
  have H := h (Fin 18) G connected
  have hb := b_ge
  have hf : (G.largestInducedForestSize : ℝ) ≤ 13 := by exact_mod_cast forest_le
  have hprod : (169 : ℝ) < (residue G : ℝ) * b G := by
    rw [resid]; push_cast; nlinarith
  have hs : (13 : ℝ) < Real.sqrt ((residue G : ℝ) * b G) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have h13 : (13 : ℤ) < ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ := by
    rw [Int.lt_ceil]
    exact_mod_cast hs
  have h' : ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (13 : ℤ) := by
    have := H.trans hf
    exact_mod_cast this
  omega

end WrittenOnTheWallII.GraphConjecture59

#print axioms WrittenOnTheWallII.GraphConjecture59.conjecture59
