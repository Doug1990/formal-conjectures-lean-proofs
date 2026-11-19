import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

universe u w

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

end SimpleGraph

namespace DfsT2

noncomputable section

open SimpleGraph

lemma mult_iso {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W}
    {iV : Fintype V} {rA : DecidableRel A.Adj}
    [Fintype W] [DecidableRel B.Adj] (e : A ≃g B) :
    degreeSequenceMultiplicity A = degreeSequenceMultiplicity B := by
  have h : (Finset.univ.val.map fun v : V => A.degree v) =
      Finset.univ.val.map fun w : W => B.degree w := by
    rw [← Finset.map_univ_equiv e.toEquiv, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun v _ => ?_
    exact (e.degree_eq v).symm
  simp only [degreeSequenceMultiplicity, degreeSequence, h]

lemma mult_eq_three {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hle : ∀ d, #(univ.filter fun v => d = G.degree v) ≤ 3) (d₀ : ℕ)
    (hge : 3 ≤ #(univ.filter fun v => d₀ = G.degree v)) :
    degreeSequenceMultiplicity G = 3 := by
  set L := degreeSequence G with hL
  have hc : ∀ d, L.count d = #(univ.filter fun v => d = G.degree v) := by
    intro d
    rw [hL, degreeSequence, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_map]
    rfl
  have hmul : degreeSequenceMultiplicity G = (L.map fun d => L.count d).max?.getD 0 := rfl
  refine hmul.trans ?_
  apply le_antisymm
  · cases h : (L.map fun d => L.count d).max? with
    | none => simp
    | some a =>
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 (List.max?_mem h)
      simpa [hc] using hle x
  · have hpos : 0 < L.count d₀ := by rw [hc]; omega
    have hmem : L.count d₀ ∈ L.map fun d => L.count d :=
      List.mem_map_of_mem (List.count_pos_iff.1 hpos)
    have := List.le_max?_getD_of_mem (k := 0) hmem
    rw [hc] at this
    omega

lemma half1 (N i : ℕ) (hi : i < N) :
    (∑ j : Fin N, if N ≤ i + j.val + 1 then 1 else 0) = i + 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if N ≤ i + j + 1 then 1 else 0) N,
    ← Finset.card_filter]
  have : (Finset.range N).filter (fun j => N ≤ i + j + 1) = Finset.Ico (N - 1 - i) N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

lemma half2 (N j : ℕ) (hj : j < N) :
    (∑ i : Fin N, if N ≤ i.val + j + 1 then 1 else 0) = j + 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if N ≤ i + j + 1 then 1 else 0) N,
    ← Finset.card_filter]
  have : (Finset.range N).filter (fun i => N ≤ i + j + 1) = Finset.Ico (N - 1 - j) N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

lemma sum_le_one {X : Type*} [Fintype X] (f : X → ℕ) (hf : Function.Injective f) (d : ℕ) :
    (∑ x, if d = f x then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  apply Finset.card_le_one.2
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact hf (hx.symm.trans hy)

section gen

variable {α L : Type*} (G : SimpleGraph α) (p : L → α) (idx : L → ℕ) (N : ℕ)

def A : α ⊕ (L ⊕ Fin N) → α ⊕ (L ⊕ Fin N) → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr (.inl l) => p l = a
  | .inl _, .inr (.inr _) => False
  | .inr (.inl l), .inl a => p l = a
  | .inr (.inl _), .inr (.inl _) => False
  | .inr (.inl l), .inr (.inr j) => N ≤ idx l + j.val + 1
  | .inr (.inr _), .inl _ => False
  | .inr (.inr j), .inr (.inl l) => N ≤ idx l + j.val + 1
  | .inr (.inr _), .inr (.inr _) => False

def Hg : SimpleGraph (α ⊕ (L ⊕ Fin N)) where
  Adj := A G p idx N
  symm := ⟨fun x y h => by
    rcases x with a | l | j <;> rcases y with b | l' | j' <;> simp only [A] at h ⊢
    all_goals first | exact h | exact G.adj_symm h⟩
  loopless := ⟨fun x h => by
    rcases x with a | l | j <;> simp only [A] at h
    exact G.irrefl h⟩

instance instDec [DecidableEq α] [DecidableRel G.Adj] : DecidableRel (Hg G p idx N).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inl a, .inr (.inl l) => inferInstanceAs (Decidable (p l = a))
  | .inl _, .inr (.inr _) => inferInstanceAs (Decidable False)
  | .inr (.inl l), .inl a => inferInstanceAs (Decidable (p l = a))
  | .inr (.inl _), .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inr (.inl l), .inr (.inr j) => inferInstanceAs (Decidable (N ≤ idx l + j.val + 1))
  | .inr (.inr _), .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inr j), .inr (.inl l) => inferInstanceAs (Decidable (N ≤ idx l + j.val + 1))
  | .inr (.inr _), .inr (.inr _) => inferInstanceAs (Decidable False)

def emb : G ↪g Hg G p idx N where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := by
    intro a b
    exact Iff.rfl

lemma cf [DecidableEq α] (hG : G.CliqueFree 3) : (Hg G p idx N).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 hs
  change A G p idx N _ _ at hab hac hbc
  rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;>
    simp only [A] at hab hac hbc
  all_goals first
    | exact hG {a, b, c} (is3Clique_iff.2 ⟨_, _, _, hab, hac, hbc, rfl⟩)
    | (subst_vars; exact G.irrefl (by assumption))

variable [Fintype α] [Fintype L] [DecidableEq α] [DecidableRel G.Adj]

lemma deg_g (a : α) : (Hg G p idx N).degree (Sum.inl a) =
    G.degree a + ∑ l, if p l = a then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree (G := Hg G p idx N),
    neighborFinset_eq_filter (G := Hg G p idx N), Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  rw [← card_neighborFinset_eq_degree (G := G), neighborFinset_eq_filter (G := G),
    Finset.card_filter]
  show (∑ b, if G.Adj a b then 1 else 0) + ((∑ l, if p l = a then 1 else 0) +
    ∑ j : Fin N, if False then 1 else 0) = _
  simp

lemma deg_l (l : L) (hl : idx l < N) : (Hg G p idx N).degree (Sum.inr (Sum.inl l)) =
    idx l + 2 := by
  rw [← card_neighborFinset_eq_degree (G := Hg G p idx N),
    neighborFinset_eq_filter (G := Hg G p idx N), Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  show (∑ a, if p l = a then 1 else 0) + ((∑ l' : L, if False then 1 else 0) +
    ∑ j : Fin N, if N ≤ idx l + j.val + 1 then 1 else 0) = _
  rw [half1 N (idx l) hl]
  simp
  omega

lemma deg_r (j : Fin N) : (Hg G p idx N).degree (Sum.inr (Sum.inr j)) =
    ∑ l, if N ≤ idx l + j.val + 1 then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree (G := Hg G p idx N),
    neighborFinset_eq_filter (G := Hg G p idx N), Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  show (∑ a : α, if False then 1 else 0) + ((∑ l, if N ≤ idx l + j.val + 1 then 1 else 0) +
    ∑ j' : Fin N, if False then 1 else 0) = _
  simp

end gen

section spec

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

noncomputable def cc (a : α) : ℕ :=
  Fintype.card α + 1 + (Fintype.equivFin α a).val - G.degree a

abbrev LL := Σ a : α, Fin (cc G a)

noncomputable def NN : ℕ := Fintype.card (LL G)

noncomputable def idx (l : LL G) : ℕ := (Fintype.equivFin (LL G) l).val

abbrev H0 := Hg G (Sigma.fst : LL G → α) (idx G) (NN G)

omit [DecidableEq α] in
lemma idx_lt (l : LL G) : idx G l < NN G := (Fintype.equivFin (LL G) l).isLt

omit [DecidableEq α] in
lemma idx_inj : Function.Injective (idx G) :=
  fun _ _ h => (Fintype.equivFin (LL G)).injective (Fin.ext h)

lemma fib (a : α) : (∑ l : LL G, if l.1 = a then 1 else 0) = cc G a := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma dg (a : α) : (H0 G).degree (Sum.inl a) = Fintype.card α + 1 + (Fintype.equivFin α a).val := by
  rw [deg_g, fib]
  have := G.degree_lt_card_verts a
  unfold cc
  omega

lemma dl (l : LL G) : (H0 G).degree (Sum.inr (Sum.inl l)) = idx G l + 2 :=
  deg_l G _ _ _ l (idx_lt G l)

lemma dr (j : Fin (NN G)) : (H0 G).degree (Sum.inr (Sum.inr j)) = j.val + 1 := by
  rw [deg_r]
  exact (Fintype.sum_equiv (Fintype.equivFin (LL G)) _
    (fun i : Fin (NN G) => if NN G ≤ i.val + j.val + 1 then 1 else 0) (fun l => rfl)).trans
    (half2 _ _ j.isLt)

omit [DecidableEq α] in
lemma NN_eq : NN G = ∑ a, cc G a := by
  simp [NN]

omit [DecidableEq α] in
lemma n_lt (hn : 0 < Fintype.card α) : Fintype.card α < NN G := by
  have h2 : ∀ a, 2 ≤ cc G a := fun a => by
    have := G.degree_lt_card_verts a
    unfold cc
    omega
  have : ∑ _a : α, 2 ≤ ∑ a, cc G a := Finset.sum_le_sum fun a _ => h2 a
  rw [← NN_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  omega

lemma count_le (d : ℕ) : #(univ.filter fun v => d = (H0 G).degree v) ≤ 3 := by
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [dg, dl, dr]
  have h1 := sum_le_one (fun a : α => Fintype.card α + 1 + (Fintype.equivFin α a).val)
    (fun x y h => (Fintype.equivFin α).injective (Fin.ext (by simpa using h))) d
  have h2 := sum_le_one (fun l : LL G => idx G l + 2)
    (fun x y h => idx_inj G (by simpa using h)) d
  have h3 := sum_le_one (fun j : Fin (NN G) => j.val + 1)
    (fun x y h => Fin.ext (by simpa using h)) d
  exact le_trans (add_le_add h1 (add_le_add h2 h3)) (le_of_eq rfl)

lemma count_ge (hn : 0 < Fintype.card α) :
    3 ≤ #(univ.filter fun v => Fintype.card α + 1 = (H0 G).degree v) := by
  have hN := n_lt G hn
  have hN' : Fintype.card α - 1 < Fintype.card (LL G) := by
    have : Fintype.card α < Fintype.card (LL G) := hN
    omega
  have m1 : (Sum.inl ((Fintype.equivFin α).symm ⟨0, hn⟩) : α ⊕ (LL G ⊕ Fin (NN G))) ∈
      univ.filter fun v => Fintype.card α + 1 = (H0 G).degree v := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dg]
    simp
  have m2 : (Sum.inr (Sum.inl ((Fintype.equivFin (LL G)).symm ⟨Fintype.card α - 1, hN'⟩)) :
      α ⊕ (LL G ⊕ Fin (NN G))) ∈
      univ.filter fun v => Fintype.card α + 1 = (H0 G).degree v := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dl]
    simp only [idx, Equiv.apply_symm_apply]
    omega
  have m3 : (Sum.inr (Sum.inr ⟨Fintype.card α, hN⟩) : α ⊕ (LL G ⊕ Fin (NN G))) ∈
      univ.filter fun v => Fintype.card α + 1 = (H0 G).degree v := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dr]
  have := Finset.two_lt_card.2 ⟨_, m1, _, m2, _, m3, by simp, by simp, by simp⟩
  omega

end spec

lemma main {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h_conn : G.Connected) (h : G.CliqueFree 3) :
    ∃ (β : Type w) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧ degreeSequenceMultiplicity H = 3 := by
  have hn : 0 < Fintype.card α := by
    have := h_conn.nonempty
    exact Fintype.card_pos
  let φ : ULift.{w} (Fin (Fintype.card (α ⊕ (LL G ⊕ Fin (NN G))))) ≃
      α ⊕ (LL G ⊕ Fin (NN G)) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  let I : (H0 G).comap φ ≃g H0 G := Iso.comap φ (H0 G)
  let inst : DecidableRel ((H0 G).comap φ).Adj := fun x y =>
    inferInstanceAs (Decidable ((H0 G).Adj (φ x) (φ y)))
  refine ⟨_, inferInstance, (H0 G).comap φ, inst, (emb G _ _ _).trans I.symm.toEmbedding,
    (cf G _ _ _ h).comap I.toEmbedding.isContained, ?_⟩
  rw [mult_iso I]
  exact mult_eq_three _ (count_le G) _ (count_ge G hn)

end

end DfsT2

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem theorem2 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn: G.Connected)
    (h : G.CliqueFree 3) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧ degreeSequenceMultiplicity H = 3 :=
  DfsT2.main G h_conn h

end SimpleGraph

#print axioms SimpleGraph.theorem2
