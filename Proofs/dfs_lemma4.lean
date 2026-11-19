import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

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

namespace DfsL3

open SimpleGraph

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

namespace DfsL4

open SimpleGraph

/-- Multiplicity of the degree sequence is an isomorphism invariant. -/
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

lemma min_ge {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W}
    {iV : Fintype V} {rA : DecidableRel A.Adj}
    [Fintype W] [DecidableRel B.Adj] (e : A ≃g B) (m : ℕ) (hne : Nonempty V)
    (h : ∀ w, m ≤ B.degree w) : m ≤ A.minDegree := by
  apply le_minDegree_of_forall_le_degree
  intro v
  rw [← e.degree_eq v]
  exact h (e v)

variable {α γ δ ε : Type*}

def glue (G : SimpleGraph α) (K : SimpleGraph δ) (f : γ ≃ α) (g : ε ≃ δ) (v : α) (u : δ) :
    SimpleGraph (γ ⊕ ε) where
  Adj
    | .inl a, .inl b => G.Adj (f a) (f b)
    | .inr x, .inr y => K.Adj (g x) (g y)
    | .inl a, .inr y => f a = v ∧ g y = u
    | .inr x, .inl b => g x = u ∧ f b = v
  symm := ⟨fun x y h => by
    rcases x with a | a <;> rcases y with b | b
    · exact G.adj_symm h
    · obtain ⟨h1, h2⟩ := h
      exact And.intro h2 h1
    · obtain ⟨h1, h2⟩ := h
      exact And.intro h2 h1
    · exact K.adj_symm h⟩
  loopless := ⟨fun x h => by
    rcases x with a | a
    · exact G.irrefl h
    · exact K.irrefl h⟩

variable (G : SimpleGraph α) (K : SimpleGraph δ) (f : γ ≃ α) (g : ε ≃ δ) (v : α) (u : δ)

instance instDec [DecidableRel G.Adj] [DecidableRel K.Adj] [DecidableEq α] [DecidableEq δ] :
    DecidableRel (glue G K f g v u).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj (f a) (f b)))
  | .inr x, .inr y => inferInstanceAs (Decidable (K.Adj (g x) (g y)))
  | .inl a, .inr y => inferInstanceAs (Decidable (f a = v ∧ g y = u))
  | .inr x, .inl b => inferInstanceAs (Decidable (g x = u ∧ f b = v))

def emb : G ↪g glue G K f g v u where
  toFun w := Sum.inl (f.symm w)
  inj' := fun a b h => f.symm.injective (Sum.inl_injective h)
  map_rel_iff' := by
    intro a b
    show G.Adj (f (f.symm a)) (f (f.symm b)) ↔ G.Adj a b
    simp only [Equiv.apply_symm_apply]

lemma glue_cf (hG : G.CliqueFree 3) (hK : K.CliqueFree 3) :
    (glue G K f g v u).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 hs
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
  · exact hG {f a, f b, f c} (is3Clique_iff.2 ⟨_, _, _, hab, hac, hbc, rfl⟩)
  · change G.Adj (f a) (f b) at hab
    obtain ⟨h1, -⟩ := hac
    obtain ⟨h2, -⟩ := hbc
    rw [h1, h2] at hab
    exact G.irrefl hab
  · change G.Adj (f a) (f c) at hac
    obtain ⟨h1, -⟩ := hab
    obtain ⟨-, h2⟩ := hbc
    rw [h1, h2] at hac
    exact G.irrefl hac
  · change K.Adj (g b) (g c) at hbc
    obtain ⟨-, h1⟩ := hab
    obtain ⟨-, h2⟩ := hac
    rw [h1, h2] at hbc
    exact K.irrefl hbc
  · change G.Adj (f b) (f c) at hbc
    obtain ⟨-, h1⟩ := hab
    obtain ⟨-, h2⟩ := hac
    rw [h1, h2] at hbc
    exact G.irrefl hbc
  · change K.Adj (g a) (g c) at hac
    obtain ⟨h1, -⟩ := hab
    obtain ⟨-, h2⟩ := hbc
    rw [h1, h2] at hac
    exact K.irrefl hac
  · change K.Adj (g a) (g b) at hab
    obtain ⟨h1, -⟩ := hac
    obtain ⟨h2, -⟩ := hbc
    rw [h1, h2] at hab
    exact K.irrefl hab
  · exact hK {g a, g b, g c} (is3Clique_iff.2 ⟨_, _, _, hab, hac, hbc, rfl⟩)

section deg

variable [Fintype α] [Fintype γ] [Fintype δ] [Fintype ε] [DecidableEq α] [DecidableEq δ]
  [DecidableRel G.Adj] [DecidableRel K.Adj]

lemma deg_inl (a : γ) :
    (glue G K f g v u).degree (Sum.inl a) = G.degree (f a) + if f a = v then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree (G := glue G K f g v u),
    neighborFinset_eq_filter (G := glue G K f g v u), Finset.card_filter, Fintype.sum_sum_type]
  congr 1
  · rw [← card_neighborFinset_eq_degree (G := G), neighborFinset_eq_filter (G := G),
      Finset.card_filter]
    exact Fintype.sum_equiv f _ _ (fun b => rfl)
  · show (∑ y : ε, if (f a = v ∧ g y = u) then 1 else 0) = _
    by_cases h : f a = v
    · rw [if_pos h, Fintype.sum_equiv g _ (fun z => if z = u then 1 else 0)
        (fun y => by simp [h])]
      simp
    · rw [if_neg h]
      simp [h]

end deg

lemma deg_eq_of_eq {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] {x y : V}
    (h : x = y) : G.degree x = G.degree y := by
  subst h
  rfl

lemma not_inl (a : γ) (h : Sum.inl a ∈ Set.compl (Set.range (emb G K f g v u))) : False :=
  h ⟨f a, congrArg Sum.inl (f.symm_apply_apply a)⟩

def jEquiv : (Set.compl (Set.range (emb G K f g v u))) ≃ δ where
  toFun
    | ⟨.inl a, h⟩ => (not_inl G K f g v u a h).elim
    | ⟨.inr x, _⟩ => g x
  invFun y := ⟨Sum.inr (g.symm y), by
    rintro ⟨w, hw⟩
    exact Sum.inl_ne_inr hw⟩
  left_inv := by
    rintro ⟨a | x, h⟩
    · exact (not_inl G K f g v u a h).elim
    · exact Subtype.ext (congrArg Sum.inr (g.symm_apply_apply x))
  right_inv := by
    intro y
    show g (g.symm y) = y
    exact g.apply_symm_apply y

def jIso : (glue G K f g v u).induce (Set.compl (Set.range (emb G K f g v u))) ≃g K where
  toEquiv := jEquiv G K f g v u
  map_rel_iff' := by
    rintro ⟨a | x, ha⟩ ⟨b | y, hb⟩
    · exact (not_inl G K f g v u a ha).elim
    · exact (not_inl G K f g v u a ha).elim
    · exact (not_inl G K f g v u b hb).elim
    · exact Iff.rfl

open scoped Classical in
lemma main {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h_conn : G.Connected) (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type w) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      degreeSequenceMultiplicity J = 3 ∧ J.minDegree ≥ 2 * Fintype.card α := by
  have hN : 0 < Fintype.card α := by
    have := h_conn.nonempty
    exact Fintype.card_pos
  obtain ⟨K, instK, hbip, hmin, hmult⟩ := SimpleGraph.lemma3 (2 * Fintype.card α) (by omega)
  obtain ⟨f, -⟩ : ∃ f : ULift.{w} (Fin (Fintype.card α)) ≃ α, True :=
    ⟨Equiv.ulift.trans (Fintype.equivFin α).symm, trivial⟩
  obtain ⟨g, -⟩ : ∃ g : ULift.{w} (Fin (8 * (2 * Fintype.card α))) ≃
      Fin (8 * (2 * Fintype.card α)), True := ⟨Equiv.ulift, trivial⟩
  obtain ⟨u, -⟩ : ∃ u : Fin (8 * (2 * Fintype.card α)), True := ⟨⟨0, by omega⟩, trivial⟩
  have hK : K.CliqueFree 3 := SimpleGraph.Colorable.cliqueFree hbip (by decide)
  refine ⟨ULift.{w} (Fin (Fintype.card α)) ⊕ ULift.{w} (Fin (8 * (2 * Fintype.card α))),
    inferInstance, glue G K f g v u, instDec G K f g v u, emb G K f g v u,
    glue_cf G K f g v u h₁ hK, ?_, ?_, ?_⟩
  · show (glue G K f g v u).degree (Sum.inl (f.symm v)) = _
    rw [deg_inl, deg_eq_of_eq G (f.apply_symm_apply v)]
    simp
  · intro w hw
    show (glue G K f g v u).degree (Sum.inl (f.symm w)) = _
    rw [deg_inl, deg_eq_of_eq G (f.apply_symm_apply w)]
    simp [hw]
  · intro J
    refine ⟨(mult_iso (jIso G K f g v u)).trans hmult, ?_⟩
    exact min_ge (jIso G K f g v u) _ ⟨(jIso G K f g v u).symm u⟩
      (fun x => by have := K.minDegree_le_degree x; omega)

end DfsL4

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

open scoped Classical in
lemma lemma4 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn: G.Connected)
    (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      degreeSequenceMultiplicity J = 3 ∧ J.minDegree ≥ 2 * Fintype.card α :=
  DfsL4.main G h_conn h₁ v

end SimpleGraph

#print axioms SimpleGraph.lemma4
