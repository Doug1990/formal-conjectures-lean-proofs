import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

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

namespace EC

variable {W : Type} [Fintype W] [DecidableEq W]

lemma entries (U : Matrix W W ℝ) (d : W → ℝ) :
    ∑ i, ∑ j, (U * diagonal d * star U) i j = ∑ l, d l * (∑ i, U i l) ^ 2 := by
  have hij : ∀ i j, (U * diagonal d * star U) i j = ∑ l, U i l * d l * U j l := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      star_trivial]
  simp only [hij]
  calc ∑ i, ∑ j, ∑ l, U i l * d l * U j l = ∑ i, ∑ l, ∑ j, U i l * d l * U j l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, U i l * d l * U j l := Finset.sum_comm
    _ = ∑ l, d l * (∑ i, U i l) ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

lemma spec [Nonempty W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (hD : 0 ≤ ∑ i, ∑ j, A i j) (k : ℕ) :
    ((∑ i, ∑ j, A i j) / Fintype.card W) ^ (2 * k) ≤ (A ^ (2 * k)).trace := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix W W ℝ, U = (hA.eigenvectorUnitary : Matrix W W ℝ) := ⟨_, rfl⟩
  obtain ⟨ev, hevdef⟩ : ∃ ev : W → ℝ, ev = hA.eigenvalues := ⟨_, rfl⟩
  have hs : A = U * diagonal ev * star U := by
    have := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at this
    rw [hUdef, hevdef]
    exact this
  have hUU : star U * U = 1 := by rw [hUdef]; exact Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := by rw [hUdef]; exact Unitary.coe_mul_star_self _
  have hpow : ∀ m : ℕ, A ^ m = U * diagonal (fun l => ev l ^ m) * star U := by
    intro m
    induction m with
    | zero => simp [hUU']
    | succ m ih =>
      rw [pow_succ, ih, hs]
      have e : U * diagonal (fun l => ev l ^ m) * star U * (U * diagonal ev * star U) =
          U * (diagonal (fun l => ev l ^ m) * (star U * U) * diagonal ev) * star U := by
        simp only [Matrix.mul_assoc]
      rw [e, hUU, Matrix.mul_one, diagonal_mul_diagonal]
      simp only [pow_succ]
  have htr : (A ^ (2 * k)).trace = ∑ l, (ev l ^ 2) ^ k := by
    rw [hpow, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, trace_diagonal]
    simp only [pow_mul]
  have hD' : ∑ i, ∑ j, A i j = ∑ l, ev l * (∑ i, U i l) ^ 2 := by
    conv_lhs => rw [hs]
    exact entries U ev
  have hN : ∑ l, (∑ i, U i l) ^ 2 = (Fintype.card W : ℝ) := by
    have h1 := entries U (fun _ => 1)
    rw [diagonal_one, Matrix.mul_one, hUU'] at h1
    simp only [one_mul] at h1
    rw [← h1]
    simp [Matrix.one_apply]
  obtain ⟨l0, -, hl0⟩ := Finset.exists_max_image univ (fun l => |ev l|) univ_nonempty
  have hle : ∑ l, ev l * (∑ i, U i l) ^ 2 ≤ |ev l0| * ∑ l, (∑ i, U i l) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    calc ev l * (∑ i, U i l) ^ 2 ≤ |ev l| * (∑ i, U i l) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |ev l0| * (∑ i, U i l) ^ 2 :=
          mul_le_mul_of_nonneg_right (hl0 l (mem_univ _)) (sq_nonneg _)
  have hNpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hq : (∑ i, ∑ j, A i j) / Fintype.card W ≤ |ev l0| := by
    rw [div_le_iff₀ hNpos, hD', ← hN]
    exact hle
  calc ((∑ i, ∑ j, A i j) / Fintype.card W) ^ (2 * k) ≤ |ev l0| ^ (2 * k) :=
        pow_le_pow_left₀ (div_nonneg hD hNpos.le) hq _
    _ = (ev l0 ^ 2) ^ k := by rw [pow_mul, sq_abs]
    _ ≤ ∑ l, (ev l ^ 2) ^ k :=
        Finset.single_le_sum (f := fun l => (ev l ^ 2) ^ k) (fun l _ => by positivity)
          (mem_univ l0)
    _ = (A ^ (2 * k)).trace := htr.symm

variable (G : SimpleGraph W) [DecidableRel G.Adj]

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
lemma adj_one {m : ℕ} (f : ℕ → W) (hf : ∀ i < m + 2, G.Adj (f i) (f (i + 1)))
    (h0 : f (m + 2) = f 0) (u v : Fin (m + 2)) (h : u - v = 1) : G.Adj (f u) (f v) := by
  have hu : u = v + 1 := by rw [← h]; abel
  subst hu
  rw [Fin.val_add_one]
  split_ifs with hv
  · have hvv : (v : ℕ) = m + 1 := by rw [hv]; rfl
    rw [hvv]
    have := hf (m + 1) (by omega)
    rw [show m + 1 + 1 = m + 2 by omega, h0] at this
    exact this.symm
  · exact (hf v v.isLt).symm

def toHom (m : ℕ) (u : W) (p : {p : G.Walk u u | p.length = m + 2}) :
    cycleGraph (m + 2) →g G where
  toFun i := p.1.getVert i
  map_rel' := by
    intro a b hab
    have hl : p.1.length = m + 2 := p.2
    have hf : ∀ i < m + 2, G.Adj (p.1.getVert i) (p.1.getVert (i + 1)) :=
      fun i hi => p.1.adj_getVert_succ (by rw [hl]; exact hi)
    have h0 : p.1.getVert (m + 2) = p.1.getVert 0 := by
      have hlen := p.1.getVert_length
      rw [hl] at hlen
      rw [hlen, Walk.getVert_zero]
    rcases (cycleGraph_adj).1 hab with h | h
    · exact adj_one G _ hf h0 a b h
    · exact (adj_one G _ hf h0 b a h).symm

lemma trace_le (m : ℕ) :
    (G.adjMatrix ℝ ^ (m + 2)).trace ≤ (homCount (cycleGraph (m + 2)) G : ℝ) := by
  have e : (G.adjMatrix ℝ ^ (m + 2)).trace =
      (Fintype.card (Σ u : W, {p : G.Walk u u | p.length = m + 2}) : ℝ) := by
    rw [Matrix.trace, Fintype.card_sigma]
    push_cast
    simp only [Matrix.diag_apply, adjMatrix_pow_apply_eq_card_walk]
  rw [e, homCount]
  have inj : Function.Injective (fun x : (Σ u : W, {p : G.Walk u u | p.length = m + 2}) =>
      toHom G m x.1 x.2) := by
    rintro ⟨u, p, hp⟩ ⟨u', p', hp'⟩ h
    have hv : ∀ i : Fin (m + 2), p.getVert i = p'.getVert i := fun i => by
      have := DFunLike.congr_fun h i
      exact this
    have hu : u = u' := by
      have := hv 0
      simpa [Walk.getVert_zero] using this
    subst hu
    have hl : p.length = m + 2 := hp
    have hl' : p'.length = m + 2 := hp'
    have : p = p' := by
      refine Walk.ext_getVert_le_length (by rw [hl, hl']) (fun k hk => ?_)
      rcases Nat.lt_or_ge k (m + 2) with h1 | h1
      · exact hv ⟨k, h1⟩
      · have hk' : k = m + 2 := by omega
        subst hk'
        calc p.getVert (m + 2) = u := by rw [← hl, Walk.getVert_length]
          _ = p'.getVert (m + 2) := by rw [← hl', Walk.getVert_length]
    subst this
    rfl
  exact_mod_cast Fintype.card_le_of_injective _ inj

lemma edges_cyc (m : ℕ) : (cycleGraph (m + 3)).edgeFinset.card = m + 3 := by
  have h := (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  omega

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

end EC

open EC in
theorem sidorenko_conjecture.variants.even_cycle (k : ℕ) (hk : 2 ≤ k)
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 3 := ⟨2 * k - 3, by omega⟩
  have hN : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ i, ∑ j, G.adjMatrix ℝ i j) = ∑ y : W, (G.degree y : ℝ) := by
    simp only [row_sum]
  have hL : homDensity (completeGraph (Fin 2)) G =
      (∑ y : W, (G.degree y : ℝ)) / (Fintype.card W : ℝ) ^ 2 := by
    unfold homDensity
    rw [homCount_K2, ← G.sum_degrees_eq_twice_card_edges, Fintype.card_fin]
    push_cast
    rfl
  have hHerm : (G.adjMatrix ℝ).IsHermitian :=
    Matrix.IsHermitian.ext fun i j => by simp [adjMatrix_apply, G.adj_comm]
  have hD0 : 0 ≤ ∑ i, ∑ j, G.adjMatrix ℝ i j := by rw [hsum]; positivity
  have hsp := spec (G.adjMatrix ℝ) hHerm hD0 k
  have htr : (G.adjMatrix ℝ ^ (m + 3)).trace ≤ (homCount (cycleGraph (m + 3)) G : ℝ) :=
    trace_le G (m + 1)
  rw [hm, hsum] at hsp
  rw [hm, edges_cyc, hL]
  unfold homDensity
  rw [Fintype.card_fin]
  have e1 : (∑ y : W, (G.degree y : ℝ)) / (Fintype.card W : ℝ) ^ 2 =
      (∑ y : W, (G.degree y : ℝ)) / (Fintype.card W : ℝ) / (Fintype.card W : ℝ) := by
    rw [div_div, sq]
  rw [e1, div_pow]
  exact (div_le_div_iff_of_pos_right (by positivity)).2 (hsp.trans htr)

end SidorenkoConjecture

#print axioms SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle
