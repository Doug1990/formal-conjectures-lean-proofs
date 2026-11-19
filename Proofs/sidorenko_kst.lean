import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

open Finset SimpleGraph

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

namespace KST

/-- Power mean: `(∑ f)^m · N ≤ (∑ f^m) · N^m`. -/
lemma jensen {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (m : ℕ) :
    (∑ i, f i) ^ m * (Fintype.card ι : ℝ) ≤ (∑ i, f i ^ m) * (Fintype.card ι : ℝ) ^ m := by
  rcases m with _ | k
  · simp
  · rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · rw [h0]; simp
    · have hN : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
      have hj := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset ι)) (f := f)
        (fun i _ => hf i) k
      rw [Finset.card_univ, div_le_iff₀ (pow_pos hN k)] at hj
      calc (∑ i, f i) ^ (k + 1) * (Fintype.card ι : ℝ)
          ≤ ((∑ i, f i ^ (k + 1)) * (Fintype.card ι : ℝ) ^ k) * (Fintype.card ι : ℝ) :=
            mul_le_mul_of_nonneg_right hj hN.le
        _ = (∑ i, f i ^ (k + 1)) * (Fintype.card ι : ℝ) ^ (k + 1) := by ring

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

/-- common neighbourhood of a tuple -/
def cn {s : ℕ} (x : Fin s → W) : Finset W := univ.filter fun y => ∀ i, G.Adj (x i) y

lemma homCount_kst (s t : ℕ) [DecidableRel (completeBipartiteGraph (Fin s) (Fin t)).Adj] :
    homCount (completeBipartiteGraph (Fin s) (Fin t)) G = ∑ x : Fin s → W, (cn G x).card ^ t := by
  unfold homCount
  have e : (completeBipartiteGraph (Fin s) (Fin t) →g G) ≃
      Σ x : Fin s → W, (Fin t → {y : W // y ∈ cn G x}) :=
    { toFun := fun f => ⟨fun i => f (Sum.inl i), fun j => ⟨f (Sum.inr j), by
        simp only [cn, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        exact f.map_adj (by simp)⟩⟩
      invFun := fun p =>
        { toFun := Sum.elim p.1 (fun j => (p.2 j).1)
          map_rel' := by
            rintro (a | a) (b | b) hab
            · simp at hab
            · have := (p.2 b).2
              simp only [cn, Finset.mem_filter, Finset.mem_univ, true_and] at this
              exact this a
            · have := (p.2 a).2
              simp only [cn, Finset.mem_filter, Finset.mem_univ, true_and] at this
              exact (this b).symm
            · simp at hab }
      left_inv := fun f => by
        ext v
        cases v <;> rfl
      right_inv := fun p => by
        rcases p with ⟨x, g⟩
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

omit [DecidableEq W] in
lemma sum_cn (s : ℕ) : ∑ x : Fin s → W, (cn G x).card = ∑ y : W, G.degree y ^ s := by
  have h1 : ∀ x : Fin s → W, (cn G x).card =
      ∑ y : W, if (∀ i, G.Adj (x i) y) then 1 else 0 := by
    intro x
    rw [cn, Finset.card_filter]
  have h2 : ∀ y : W, G.degree y ^ s =
      ∑ x : Fin s → W, if (∀ i, G.Adj (x i) y) then 1 else 0 := by
    intro y
    rw [← Finset.card_filter]
    have : (univ.filter fun x : Fin s → W => ∀ i, G.Adj (x i) y) =
        Fintype.piFinset (fun _ : Fin s => univ.filter fun w => G.Adj w y) := by
      ext x
      simp [Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp [mem_neighborFinset, G.adj_comm]
  simp only [h1, h2]
  exact Finset.sum_comm

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

lemma edges_kst (s t : ℕ) [DecidableRel (completeBipartiteGraph (Fin s) (Fin t)).Adj] :
    (completeBipartiteGraph (Fin s) (Fin t)).edgeFinset.card = s * t := by
  have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin s) (W₂ := Fin t)
  rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at h
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
  exact_mod_cast h

/-- The real inequality. -/
lemma key (N D S1 S2 : ℝ) (s t : ℕ) (hN : 0 < N) (hD : 0 ≤ D) (hS1 : 0 ≤ S1)
    (hA : D ^ s * N ≤ S1 * N ^ s) (hB : S1 ^ t * N ^ s ≤ S2 * (N ^ s) ^ t) :
    (D / N ^ 2) ^ (s * t) ≤ S2 / N ^ (s + t) := by
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA' : (D ^ s * N) ^ t ≤ (S1 * N ^ s) ^ t := pow_le_pow_left₀ (by positivity) hA t
  rw [mul_pow, mul_pow] at hA'
  have hNs : (0 : ℝ) ≤ N ^ s := by positivity
  have hNst : (0 : ℝ) ≤ (N ^ s) ^ t := by positivity
  calc D ^ (s * t) * N ^ (s + t) = ((D ^ s) ^ t * N ^ t) * N ^ s := by
        rw [← pow_mul, pow_add]; ring
    _ ≤ ((S1 ^ t) * (N ^ s) ^ t) * N ^ s := mul_le_mul_of_nonneg_right hA' hNs
    _ = (S1 ^ t * N ^ s) * (N ^ s) ^ t := by ring
    _ ≤ (S2 * (N ^ s) ^ t) * (N ^ s) ^ t := mul_le_mul_of_nonneg_right hB hNst
    _ = S2 * (N ^ 2) ^ (s * t) := by
        rw [← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        ring

end KST

open KST in
theorem sidorenko_conjecture.variants.complete_bipartite (s t : ℕ)
    [DecidableRel (completeBipartiteGraph (Fin s) (Fin t)).Adj]
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
        ((completeBipartiteGraph (Fin s) (Fin t)).edgeFinset.card) ≤
      homDensity (completeBipartiteGraph (Fin s) (Fin t)) G := by
  have hN : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hL : homDensity (completeGraph (Fin 2)) G =
      (∑ y : W, (G.degree y : ℝ)) / (Fintype.card W : ℝ) ^ 2 := by
    unfold homDensity
    rw [homCount_K2, ← G.sum_degrees_eq_twice_card_edges, Fintype.card_fin]
    push_cast
    rfl
  have hR : homDensity (completeBipartiteGraph (Fin s) (Fin t)) G =
      (∑ x : Fin s → W, ((cn G x).card : ℝ) ^ t) / (Fintype.card W : ℝ) ^ (s + t) := by
    unfold homDensity
    rw [homCount_kst, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  rw [hL, hR, edges_kst]
  have hA := jensen (fun y : W => (G.degree y : ℝ)) (fun _ => by positivity) s
  have hB := jensen (fun x : Fin s → W => ((cn G x).card : ℝ)) (fun _ => by positivity) t
  have hS1 : (∑ x : Fin s → W, ((cn G x).card : ℝ)) = ∑ y : W, (G.degree y : ℝ) ^ s := by
    exact_mod_cast sum_cn G s
  rw [hS1] at hB
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hB
  exact key _ _ _ _ s t hN (by positivity) (by positivity) hA hB

end SidorenkoConjecture

#print axioms SidorenkoConjecture.sidorenko_conjecture.variants.complete_bipartite
