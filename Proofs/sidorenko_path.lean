import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Field

set_option linter.unusedSectionVars false

open Finset SimpleGraph Matrix

namespace SimpleGraph

variable {V W : Type*}

noncomputable def homCount [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (H →g G)

noncomputable def homDensity [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount H G : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

end SimpleGraph

namespace SidorenkoConjecture

namespace BR

/-- Concavity of log (weighted AM–GM), in the form needed here. -/
lemma jensen {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < w i → 0 < x i) (hS : 0 < ∑ i ∈ s, w i) :
    ∑ i ∈ s, w i * Real.log (x i) ≤
      (∑ i ∈ s, w i) * Real.log ((∑ i ∈ s, w i * x i) / ∑ i ∈ s, w i) := by
  have hterm : ∀ i ∈ s, 0 ≤ w i * x i := by
    intro i hi
    rcases (hw i hi).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · exact (mul_pos h (hx i hi h)).le
  have hT : 0 < ∑ i ∈ s, w i * x i := by
    obtain ⟨i, hi, hwi⟩ : ∃ i ∈ s, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos h
      linarith
    calc 0 < w i * x i := mul_pos hwi (hx i hi hwi)
      _ ≤ ∑ i ∈ s, w i * x i := Finset.single_le_sum (f := fun i => w i * x i) hterm hi
  generalize hSdef : ∑ i ∈ s, w i = S at hS ⊢
  generalize hTdef : ∑ i ∈ s, w i * x i = T at hT ⊢
  have hA : 0 < T / S := div_pos hT hS
  have key : ∀ i ∈ s, w i * Real.log (x i) ≤
      w i * Real.log (T / S) + (w i * x i / (T / S) - w i) := by
    intro i hi
    rcases (hw i hi).eq_or_lt with h | h
    · rw [← h]; simp
    · have hxi := hx i hi h
      have h1 : Real.log (x i / (T / S)) ≤ x i / (T / S) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hxi hA)
      rw [Real.log_div hxi.ne' hA.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 h.le
      have e : w i * (x i / (T / S) - 1) = w i * x i / (T / S) - w i := by ring
      nlinarith [h2, e]
  calc ∑ i ∈ s, w i * Real.log (x i)
      ≤ ∑ i ∈ s, (w i * Real.log (T / S) + (w i * x i / (T / S) - w i)) :=
        Finset.sum_le_sum key
    _ = S * Real.log (T / S) + (T / (T / S) - S) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
          hSdef, hTdef]
    _ = S * Real.log (T / S) := by
        have : T / (T / S) = S := by field_simp
        rw [this]; ring

/-- Lower Jensen bound for `x log x`. -/
lemma jensen_low {ι : Type*} (s : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hD : 0 < ∑ i ∈ s, d i) :
    (∑ i ∈ s, d i) * Real.log ((∑ i ∈ s, d i) / s.card) ≤ ∑ i ∈ s, d i * Real.log (d i) := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hD
    exact lt_irrefl _ hD
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  generalize hDdef : ∑ i ∈ s, d i = D at hD ⊢
  have hc : 0 < D / s.card := div_pos hD hN
  have key : ∀ i ∈ s, d i * Real.log (D / s.card) + (d i - D / s.card) ≤
      d i * Real.log (d i) := by
    intro i hi
    rcases (hd i hi).eq_or_lt with h | h
    · rw [← h]; simp; exact hc.le
    · have h1 : 1 - (d i / (D / s.card))⁻¹ ≤ Real.log (d i / (D / s.card)) :=
        Real.one_sub_inv_le_log_of_pos (div_pos h hc)
      rw [Real.log_div h.ne' hc.ne', inv_div] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 h.le
      have e : d i * (1 - D / s.card / d i) = d i - D / s.card := by
        field_simp
      nlinarith [h2, e]
  calc D * Real.log (D / s.card)
      = ∑ i ∈ s, (d i * Real.log (D / s.card) + (d i - D / s.card)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hDdef,
          Finset.sum_const, nsmul_eq_mul]
        field_simp
        ring
    _ ≤ ∑ i ∈ s, d i * Real.log (d i) := Finset.sum_le_sum key

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Walk-count vector `A^j 1`. -/
noncomputable def F (A : Matrix W W ℝ) (j : ℕ) : W → ℝ := (A ^ j) *ᵥ (fun _ => 1)

/-- Row sums. -/
noncomputable def deg (A : Matrix W W ℝ) (v : W) : ℝ := ∑ u, A v u

lemma F_zero (A : Matrix W W ℝ) (v : W) : F A 0 v = 1 := by
  simp [F]

lemma F_succ (A : Matrix W W ℝ) (j : ℕ) (v : W) : F A (j + 1) v = ∑ u, A v u * F A j u := by
  unfold F
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

variable (A : Matrix W W ℝ) (hsym : ∀ u v, A u v = A v u) (hnn : ∀ u v, 0 ≤ A u v)
include hsym hnn

lemma col_sum (u : W) : ∑ v, A v u = deg A u := by
  unfold deg
  exact Finset.sum_congr rfl fun v _ => hsym v u

lemma F_nonneg (j : ℕ) (v : W) : 0 ≤ F A j v := by
  induction j generalizing v with
  | zero => rw [F_zero]; exact zero_le_one
  | succ j ih =>
    rw [F_succ]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hnn v u) (ih u)

lemma deg_pos_of (v u : W) (h : 0 < A v u) : 0 < deg A u := by
  unfold deg
  calc 0 < A u v := by rw [hsym]; exact h
    _ ≤ ∑ w, A u w := Finset.single_le_sum (f := fun w => A u w) (fun w _ => hnn u w)
        (mem_univ v)

lemma exists_pos (v : W) (h : 0 < deg A v) : ∃ u, 0 < A v u := by
  by_contra hc
  push Not at hc
  have : deg A v ≤ 0 := Finset.sum_nonpos fun u _ => hc u
  linarith

lemma F_pos (j : ℕ) (v : W) (h : 0 < deg A v) : 0 < F A j v := by
  induction j generalizing v with
  | zero => rw [F_zero]; exact zero_lt_one
  | succ j ih =>
    rw [F_succ]
    obtain ⟨u, hu⟩ := exists_pos A hsym hnn v h
    have hu' := ih u (deg_pos_of A hsym hnn v u hu)
    calc 0 < A v u * F A j u := mul_pos hu hu'
      _ ≤ ∑ w, A v w * F A j w :=
        Finset.single_le_sum (f := fun w => A v w * F A j w)
          (fun w _ => mul_nonneg (hnn v w) (F_nonneg A hsym hnn j w)) (mem_univ u)

lemma step_v (j : ℕ) (v : W) :
    deg A v * Real.log (deg A v) + ∑ u, A v u * Real.log (F A j u) ≤
      deg A v * Real.log (F A (j + 1) v) := by
  have hd : 0 ≤ deg A v := Finset.sum_nonneg (fun u _ => hnn v u)
  rcases hd.eq_or_lt with h | h
  · have hz : ∀ u, A v u = 0 := by
      intro u
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hnn v u)).1 h.symm u (mem_univ u)
      exact this
    rw [← h]
    simp [hz]
  · have hj := jensen univ (fun u => A v u) (F A j) (fun u _ => hnn v u)
      (fun u _ hu => F_pos A hsym hnn j u (deg_pos_of A hsym hnn v u hu)) h
    have hF := F_pos A hsym hnn (j + 1) v h
    rw [← F_succ] at hj
    change ∑ u, A v u * Real.log (F A j u) ≤ deg A v * Real.log (F A (j + 1) v / deg A v) at hj
    rw [Real.log_div hF.ne' h.ne'] at hj
    nlinarith [hj]

lemma step (j : ℕ) :
    ∑ v, deg A v * Real.log (deg A v) + ∑ u, deg A u * Real.log (F A j u) ≤
      ∑ v, deg A v * Real.log (F A (j + 1) v) := by
  have e : ∑ u, deg A u * Real.log (F A j u) = ∑ v, ∑ u, A v u * Real.log (F A j u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, col_sum A hsym hnn]
  rw [e, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ => step_v A hsym hnn j v

lemma ind (j : ℕ) :
    (j : ℝ) * ∑ v, deg A v * Real.log (deg A v) ≤ ∑ v, deg A v * Real.log (F A j v) := by
  induction j with
  | zero => simp [F_zero]
  | succ j ih =>
    have := step A hsym hnn j
    push_cast
    linarith

lemma total (j : ℕ) : ∑ v, F A (j + 1) v = ∑ u, deg A u * F A j u := by
  simp only [F_succ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, col_sum A hsym hnn]

lemma main [Nonempty W] (m : ℕ) :
    (Fintype.card W : ℝ) * ((∑ v, deg A v) / Fintype.card W) ^ m ≤ ∑ v, F A m v := by
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hdeg : ∀ v, 0 ≤ deg A v := fun v => Finset.sum_nonneg fun u _ => hnn v u
  rcases m with _ | j
  · simp [F_zero]
  rcases (Finset.sum_nonneg (fun v _ => hdeg v) : (0 : ℝ) ≤ ∑ v, deg A v).eq_or_lt with hD | hD
  · rw [← hD]
    simp only [zero_div, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact Finset.sum_nonneg fun v _ => F_nonneg A hsym hnn _ v
  generalize hDdef : ∑ v, deg A v = D at hD
  have h1 := jensen univ (deg A) (F A j) (fun v _ => hdeg v)
    (fun v _ hv => F_pos A hsym hnn j v hv) (by rw [hDdef]; exact hD)
  have h2 := ind A hsym hnn j
  have h3 := jensen_low univ (deg A) (fun v _ => hdeg v) (by rw [hDdef]; exact hD)
  rw [← total A hsym hnn j] at h1
  rw [hDdef] at h1 h3
  rw [Finset.card_univ] at h3
  generalize hTdef : ∑ v, F A (j + 1) v = T at h1 ⊢
  have hT : 0 < T := by
    obtain ⟨v, hv⟩ : ∃ v, 0 < deg A v := by
      by_contra hc
      push Not at hc
      have : ∑ v, deg A v ≤ 0 := Finset.sum_nonpos fun v _ => hc v
      linarith
    rw [← hTdef]
    calc 0 < F A (j + 1) v := F_pos A hsym hnn (j + 1) v hv
      _ ≤ ∑ w, F A (j + 1) w :=
        Finset.single_le_sum (f := fun w => F A (j + 1) w)
          (fun w _ => F_nonneg A hsym hnn _ w) (mem_univ v)
  have hc : 0 < D / Fintype.card W := div_pos hD hN
  -- D * log (T/D) ≥ j * D * log (D/N)
  have h4 : D * ((j : ℝ) * Real.log (D / Fintype.card W)) ≤ D * Real.log (T / D) := by
    have h5 : (j : ℝ) * (D * Real.log (D / Fintype.card W)) ≤
        (j : ℝ) * ∑ v, deg A v * Real.log (deg A v) :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j)
    nlinarith [h1, h2, h5]
  have h6 : (j : ℝ) * Real.log (D / Fintype.card W) ≤ Real.log (T / D) :=
    le_of_mul_le_mul_left h4 hD
  rw [← Real.log_pow] at h6
  have h7 : (D / Fintype.card W) ^ j ≤ T / D :=
    (Real.log_le_log_iff (pow_pos hc j) (div_pos hT hD)).1 h6
  rw [le_div_iff₀ hD] at h7
  calc (Fintype.card W : ℝ) * (D / Fintype.card W) ^ (j + 1)
      = (D / Fintype.card W) ^ j * D := by
        have hN' : (Fintype.card W : ℝ) ≠ 0 := hN.ne'
        rw [pow_succ]; field_simp
    _ ≤ T := h7

end BR

namespace BRG

open BR

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

lemma homCount_K2 : homCount (completeGraph (Fin 2)) G = 2 * #G.edgeFinset := by
  unfold homCount
  rw [← G.dart_card_eq_twice_card_edges]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f =>
        ⟨(f 0, f 1), f.map_adj (by decide : (completeGraph (Fin 2)).Adj 0 1)⟩
      invFun := fun d =>
        { toFun := fun i => if i = 0 then d.fst else d.snd
          map_rel' := fun {a b} hab => by
            simp only [completeGraph, top_adj] at hab
            fin_cases a <;> fin_cases b
            · simp at hab
            · exact d.adj
            · exact d.adj.symm
            · simp at hab }
      left_inv := fun f => by
        ext i
        fin_cases i <;> simp
      right_inv := fun d => by
        cases d
        rfl }

omit [DecidableEq W] in
lemma row_sum (i : W) : ∑ j, G.adjMatrix ℝ i j = (G.degree i : ℝ) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter (G := G)]
  simp [adjMatrix_apply, Finset.sum_boole]

/-- Walks of length `m` give homomorphisms from the path on `m + 1` vertices. -/
def toHom (m : ℕ) (x : Σ v : W, Σ u : W, {p : G.Walk v u | p.length = m}) :
    pathGraph (m + 1) →g G where
  toFun i := x.2.2.1.getVert i
  map_rel' := by
    intro a b hab
    have hl : x.2.2.1.length = m := x.2.2.2
    rcases pathGraph_adj.1 hab with h | h
    · have := x.2.2.1.adj_getVert_succ (i := a) (by have := b.isLt; omega)
      rw [h] at this
      exact this
    · have := x.2.2.1.adj_getVert_succ (i := b) (by have := a.isLt; omega)
      rw [h] at this
      exact this.symm

lemma card_le (m : ℕ) [DecidableRel (pathGraph (m + 1)).Adj] :
    Fintype.card (Σ v : W, Σ u : W, {p : G.Walk v u | p.length = m}) ≤
      homCount (pathGraph (m + 1)) G := by
  unfold homCount
  refine Fintype.card_le_of_injective (toHom G m) ?_
  rintro ⟨v, u, p, hp⟩ ⟨v', u', p', hp'⟩ h
  have hv : ∀ i : Fin (m + 1), p.getVert i = p'.getVert i := fun i => by
    have := DFunLike.congr_fun h i
    exact this
  have hl : p.length = m := hp
  have hl' : p'.length = m := hp'
  have hvv : v = v' := by
    have := hv 0
    simpa [Walk.getVert_zero] using this
  subst hvv
  have e1 : p.getVert m = u := by rw [← hl, Walk.getVert_length]
  have e2 : p'.getVert m = u' := by rw [← hl', Walk.getVert_length]
  have huu : u = u' := by
    have := hv ⟨m, by omega⟩
    simp only at this
    rw [← e1, ← e2, this]
  subst huu
  have : p = p' := by
    refine Walk.ext_getVert_le_length (by rw [hl, hl']) (fun k hk => ?_)
    exact hv ⟨k, by omega⟩
  subst this
  rfl

lemma sumF_eq (m : ℕ) : ∑ v, F (G.adjMatrix ℝ) m v =
    (Fintype.card (Σ v : W, Σ u : W, {p : G.Walk v u | p.length = m}) : ℝ) := by
  rw [Fintype.card_sigma]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.card_sigma]
  push_cast
  simp only [F, Matrix.mulVec, dotProduct, mul_one, adjMatrix_pow_apply_eq_card_walk]

lemma edges_ge (m : ℕ) [DecidableRel (pathGraph (m + 1)).Adj] :
    m ≤ (pathGraph (m + 1)).edgeFinset.card := by
  have := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin m)))
    (t := (pathGraph (m + 1)).edgeFinset) (fun i => s(i.castSucc, i.succ)) ?_ ?_
  · simpa using this
  · intro i _
    simp only [Finset.mem_coe, mem_edgeFinset, mem_edgeSet, pathGraph_adj]
    left
    simp
  · intro i _ j _ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact Fin.castSucc_inj.1 h1
    · exfalso
      have a := congrArg Fin.val h1
      have b := congrArg Fin.val h2
      simp at a b
      omega

end BRG

open BR BRG in
theorem sidorenko_conjecture.variants.path_blakley_roy (n : ℕ)
    [DecidableRel (pathGraph n).Adj]
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^ ((pathGraph n).edgeFinset.card) ≤
      homDensity (pathGraph n) G := by
  have hN : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card W : ℝ) with hNdef
  set D : ℝ := ∑ y : W, (G.degree y : ℝ) with hDdef
  have hL : homDensity (completeGraph (Fin 2)) G = D / N ^ 2 := by
    unfold homDensity
    rw [homCount_K2, ← G.sum_degrees_eq_twice_card_edges, Fintype.card_fin]
    push_cast
    rfl
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun y _ => Nat.cast_nonneg _
  have hN' : N ≠ 0 := hN.ne'
  have hDN : D ≤ N * N := by
    have : ∀ y : W, (G.degree y : ℝ) ≤ N := by
      intro y
      rw [hNdef]
      have : G.degree y ≤ Fintype.card W := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_le_univ _
      exact_mod_cast this
    calc D ≤ ∑ _y : W, N := Finset.sum_le_sum fun y _ => this y
      _ = N * N := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hx0 : 0 ≤ D / N ^ 2 := by positivity
  have hx1 : D / N ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rw [hL]
  rcases n with _ | m
  · -- empty path
    calc (D / N ^ 2) ^ (pathGraph 0).edgeFinset.card ≤ 1 := pow_le_one₀ hx0 hx1
      _ ≤ homDensity (pathGraph 0) G := by
        unfold homDensity homCount
        rw [Fintype.card_fin, pow_zero, div_one]
        have : 0 < Fintype.card (pathGraph 0 →g G) :=
          Fintype.card_pos_iff.2 ⟨⟨fun i => Fin.elim0 i, fun {a} => Fin.elim0 a⟩⟩
        exact_mod_cast this
  · have hA := main (G.adjMatrix ℝ) (fun u v => by simp [adjMatrix_apply, G.adj_comm])
      (fun u v => by simp only [adjMatrix_apply]; split_ifs <;> norm_num) m
    have hdeg : ∀ v, deg (G.adjMatrix ℝ) v = (G.degree v : ℝ) := fun v => row_sum G v
    simp only [hdeg] at hA
    rw [sumF_eq] at hA
    have hc := card_le G m
    calc (D / N ^ 2) ^ (pathGraph (m + 1)).edgeFinset.card ≤ (D / N ^ 2) ^ m :=
          pow_le_pow_of_le_one hx0 hx1 (edges_ge m)
      _ = N * (D / N) ^ m / N ^ (m + 1) := by
          rw [div_pow, div_pow, ← pow_mul]
          field_simp
          ring
      _ ≤ homDensity (pathGraph (m + 1)) G := by
          unfold homDensity
          rw [Fintype.card_fin]
          refine div_le_div_of_nonneg_right (hA.trans ?_) (by positivity)
          exact_mod_cast hc

end SidorenkoConjecture

#print axioms SidorenkoConjecture.sidorenko_conjecture.variants.path_blakley_roy
