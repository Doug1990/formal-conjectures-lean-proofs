import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
Independence.lean and LargestInducedTree.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture200

open SimpleGraph Finset

/-! The counterexample (q = 5): C = {0,1,2,3,4} induces K₅ minus 01; x = 5, y = 6 are
complete to C; z = 7 is adjacent to 0, 1; pendants 8, 9, 10 hang at 2, 3, 4. -/

def E : List (ℕ × ℕ) := [(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),
  (0,5),(1,5),(2,5),(3,5),(4,5),(0,6),(1,6),(2,6),(3,6),(4,6),
  (0,7),(1,7),(2,8),(3,9),(4,10)]

def adjF (i j : Fin 11) : Prop := (i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_irrefl : ∀ i : Fin 11, ¬ adjF i i := by decide

def G : SimpleGraph (Fin 11) where
  Adj := adjF
  symm := ⟨fun x y h => by unfold adjF at *; exact h.symm⟩
  loopless := ⟨fun x h => adjF_irrefl x h⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma connected : G.Connected := by
  have A : ∀ i j : Fin 11, adjF i j → G.Reachable i j := fun i j h => Adj.reachable h
  have hR : ∀ i : Fin 11, G.Reachable 0 i := by
    have r2 := A 0 2 (by decide)
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact r2.trans (A 2 1 (by decide))
    · exact r2
    · exact A 0 3 (by decide)
    · exact A 0 4 (by decide)
    · exact A 0 5 (by decide)
    · exact A 0 6 (by decide)
    · exact A 0 7 (by decide)
    · exact r2.trans (A 2 8 (by decide))
    · exact (A 0 3 (by decide)).trans (A 3 9 (by decide))
    · exact (A 0 4 (by decide)).trans (A 4 10 (by decide))
  rw [connected_iff]
  exact ⟨fun u v => (hR u).symm.trans (hR v), ⟨0⟩⟩

/-! ### Acyclicity tools -/

lemma bridge_cut {W : Type*} {F : SimpleGraph W} {a b : W} (S : Set W) (ha : a ∈ S)
    (hb : b ∉ S) (h : ∀ x y, F.Adj x y → x ∈ S → y ∉ S → s(x, y) = s(a, b)) :
    F.IsBridge s(a, b) := by
  rw [isBridge_iff]
  intro hr
  have p := hr.some
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  exact hadj.2 (by simpa using h _ _ hadj.1 hd1 hd2)

lemma star_acyc {W : Type*} (H : SimpleGraph W) (c : W)
    (h : ∀ x y, H.Adj x y → x = c ∨ y = c) : H.IsAcyclic := by
  have key : ∀ b, H.Adj c b → H.IsBridge s(c, b) := by
    intro b hb
    refine bridge_cut {z | z ≠ b} (H.ne_of_adj hb) (by simp) ?_
    intro x y hxy hx hy
    simp only [Set.mem_ofPred_eq, not_not] at hx hy
    subst hy
    rcases h x y hxy with e | e
    · rw [e]
    · exact absurd e.symm (H.ne_of_adj hb)
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rcases h a b hab with rfl | rfl
  · exact key b hab
  · rw [Sym2.eq_swap]
    exact key a hab.symm

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

/-! ### `tree(G) ≥ 4`: the claw `{0,5,6,7}` -/

def S4 : Finset (Fin 11) := {0, 5, 6, 7}

lemma claw_adj : ∀ x y : Fin 11, x ∈ S4 → y ∈ S4 → adjF x y → x = 0 ∨ y = 0 := by decide

lemma claw_c : ∀ x : Fin 11, x ∈ S4 → x ≠ 0 → adjF 0 x := by decide

lemma claw_tree : (G.induce (S4 : Set (Fin 11))).IsTree := by
  have h0 : (0 : Fin 11) ∈ S4 := by decide
  refine ⟨?_, ?_⟩
  · rw [connected_iff]
    refine ⟨?_, ⟨⟨0, h0⟩⟩⟩
    have hr : ∀ x : ↑(S4 : Set (Fin 11)), (G.induce (S4 : Set (Fin 11))).Reachable ⟨0, h0⟩ x := by
      rintro ⟨x, hx⟩
      by_cases e : x = 0
      · subst e; exact Reachable.refl _
      · exact Adj.reachable (show (G.induce (S4 : Set (Fin 11))).Adj ⟨0, h0⟩ ⟨x, hx⟩ from
          claw_c x hx e)
    intro x y
    exact (hr x).symm.trans (hr y)
  · apply star_acyc _ ⟨0, h0⟩
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rcases claw_adj x y hx hy h with e | e
    · left; exact Subtype.ext e
    · right; exact Subtype.ext e

/-! ### `tree(G) ≤ 4` via 0/1 indicators and `omega` -/

def ind (s : Finset (Fin 11)) (n : ℕ) : ℕ :=
  if h : n < 11 then (if (⟨n, h⟩ : Fin 11) ∈ s then 1 else 0) else 0

lemma ind_fin (s : Finset (Fin 11)) (i : Fin 11) : ind s i.val = if i ∈ s then 1 else 0 := by
  unfold ind
  rw [dif_pos i.isLt]

lemma ind_le (s : Finset (Fin 11)) (n : ℕ) : ind s n ≤ 1 := by
  unfold ind
  split_ifs <;> omega

lemma card_ind (s : Finset (Fin 11)) : s.card = ind s 0 + ind s 1 + ind s 2 + ind s 3 +
    ind s 4 + ind s 5 + ind s 6 + ind s 7 + ind s 8 + ind s 9 + ind s 10 := by
  have h1 : s.card = ∑ i : Fin 11, ind s i.val := by
    calc s.card = ∑ i : Fin 11, (if i ∈ s then 1 else 0) := by simp
      _ = ∑ i : Fin 11, ind s i.val := by simp only [ind_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => ind s n) 11] at h1
  simp only [sum_range_succ, sum_range_zero, zero_add] at h1
  exact h1

lemma arith200 (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 : ℕ)
    (b0 : g0 ≤ 1) (b1 : g1 ≤ 1) (b2 : g2 ≤ 1) (b3 : g3 ≤ 1) (b4 : g4 ≤ 1) (b5 : g5 ≤ 1)
    (b6 : g6 ≤ 1) (b7 : g7 ≤ 1)
    (t1 : g2 + g3 + g4 ≤ 2) (t2 : g0 + g2 + g3 ≤ 2) (t3 : g0 + g2 + g4 ≤ 2)
    (t4 : g0 + g3 + g4 ≤ 2) (t5 : g1 + g2 + g3 ≤ 2) (t6 : g1 + g2 + g4 ≤ 2)
    (t7 : g1 + g3 + g4 ≤ 2)
    (x1 : g5 + g0 + g2 ≤ 2) (x2 : g5 + g0 + g3 ≤ 2) (x3 : g5 + g0 + g4 ≤ 2)
    (x4 : g5 + g1 + g2 ≤ 2) (x5 : g5 + g1 + g3 ≤ 2) (x6 : g5 + g1 + g4 ≤ 2)
    (x7 : g5 + g2 + g3 ≤ 2) (x8 : g5 + g2 + g4 ≤ 2) (x9 : g5 + g3 + g4 ≤ 2)
    (y1 : g6 + g0 + g2 ≤ 2) (y2 : g6 + g0 + g3 ≤ 2) (y3 : g6 + g0 + g4 ≤ 2)
    (y4 : g6 + g1 + g2 ≤ 2) (y5 : g6 + g1 + g3 ≤ 2) (y6 : g6 + g1 + g4 ≤ 2)
    (y7 : g6 + g2 + g3 ≤ 2) (y8 : g6 + g2 + g4 ≤ 2) (y9 : g6 + g3 + g4 ≤ 2)
    (q1 : g0 + g5 + g1 + g6 ≤ 3) (q2 : g0 + g5 + g1 + g7 ≤ 3) (q3 : g0 + g6 + g1 + g7 ≤ 3)
    (q4 : g0 + g2 + g1 + g7 ≤ 3) (q5 : g0 + g3 + g1 + g7 ≤ 3) (q6 : g0 + g4 + g1 + g7 ≤ 3)
    (n5 : g5 ≤ g0 + g1 + g2 + g3 + g4) (n6 : g6 ≤ g0 + g1 + g2 + g3 + g4)
    (n7 : g7 ≤ g0 + g1) (n8 : g8 ≤ g2) (n9 : g9 ≤ g3) (n10 : g10 ≤ g4) :
    g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7 + g8 + g9 + g10 ≤ 4 := by
  have e0 : g0 = 0 ∨ g0 = 1 := by omega
  have e1 : g1 = 0 ∨ g1 = 1 := by omega
  have e2 : g2 = 0 ∨ g2 = 1 := by omega
  have e3 : g3 = 0 ∨ g3 = 1 := by omega
  have e4 : g4 = 0 ∨ g4 = 1 := by omega
  rcases e0 with rfl | rfl <;> rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;>
    rcases e3 with rfl | rfl <;> rcases e4 with rfl | rfl <;> omega

lemma tree_card_le (s : Finset (Fin 11)) (hs : (G.induce (s : Set (Fin 11))).IsTree) :
    s.card ≤ 4 := by
  by_contra hlt
  have h5 : 5 ≤ s.card := by omega
  have adjI : ∀ i j : Fin 11, (hi : i ∈ s) → (hj : j ∈ s) → adjF i j →
      (G.induce (s : Set _)).Adj ⟨i, hi⟩ ⟨j, hj⟩ := fun i j _ _ h => h
  have tri : ∀ a b c : Fin 11, adjF a b → adjF b c → adjF c a →
      ind s a.val + ind s b.val + ind s c.val ≤ 2 := by
    intro a b c h1 h2 h3
    rw [ind_fin, ind_fin, ind_fin]
    split_ifs with ha hb hc <;> first | omega |
      exact absurd hs.isAcyclic (not_acyc_tri _ (adjI a b ha hb h1) (adjI b c hb hc h2)
        (adjI c a hc ha h3))
  have c4 : ∀ a b c d : Fin 11, adjF a b → adjF b c → adjF c d → adjF d a → a ≠ c → b ≠ d →
      ind s a.val + ind s b.val + ind s c.val + ind s d.val ≤ 3 := by
    intro a b c d h1 h2 h3 h4 hac hbd
    rw [ind_fin, ind_fin, ind_fin, ind_fin]
    split_ifs with ha hb hc hd <;> first | omega |
      exact absurd hs.isAcyclic (not_acyc_c4 _ (adjI a b ha hb h1) (adjI b c hb hc h2)
        (adjI c d hc hd h3) (adjI d a hd ha h4) (fun e => hac (congrArg Subtype.val e))
        (fun e => hbd (congrArg Subtype.val e)))
  have reach_adj : ∀ x y : ↑(s : Set (Fin 11)), (G.induce (s : Set (Fin 11))).Reachable x y →
      x ≠ y → ∃ z, (G.induce (s : Set (Fin 11))).Adj x z := by
    intro x y hr hxy
    have p := hr.some
    cases p with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  have nb : ∀ v ∈ s, ∃ w ∈ s, adjF v w := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < s.card)
    obtain ⟨u, hu, huv⟩ : ∃ u ∈ s, u ≠ v := by
      by_cases e : a = v
      · exact ⟨b, hb, fun e' => hab (e.trans e'.symm)⟩
      · exact ⟨a, ha, e⟩
    obtain ⟨z, hz⟩ := reach_adj ⟨v, hv⟩ ⟨u, hu⟩ (hs.connected.preconnected _ _)
      (fun e => huv (congrArg Subtype.val e).symm)
    exact ⟨z.1, z.2, hz⟩
  have nb1 : ∀ v w1 : Fin 11, (∀ u, adjF v u → u = w1) → ind s v.val ≤ ind s w1.val := by
    intro v w1 hN
    rw [ind_fin s v]
    split_ifs with hv
    · obtain ⟨w, hw, hadj⟩ := nb v hv
      have hw1 : ind s w.val = 1 := by rw [ind_fin, if_pos hw]
      have e := hN w hadj
      subst e
      omega
    · omega
  have nb2 : ∀ v w1 w2 : Fin 11, (∀ u, adjF v u → u = w1 ∨ u = w2) →
      ind s v.val ≤ ind s w1.val + ind s w2.val := by
    intro v w1 w2 hN
    rw [ind_fin s v]
    split_ifs with hv
    · obtain ⟨w, hw, hadj⟩ := nb v hv
      have hw1 : ind s w.val = 1 := by rw [ind_fin, if_pos hw]
      rcases hN w hadj with e | e <;> subst e <;> omega
    · omega
  have nb5 : ∀ v w1 w2 w3 w4 w5 : Fin 11,
      (∀ u, adjF v u → u = w1 ∨ u = w2 ∨ u = w3 ∨ u = w4 ∨ u = w5) →
      ind s v.val ≤ ind s w1.val + ind s w2.val + ind s w3.val + ind s w4.val + ind s w5.val := by
    intro v w1 w2 w3 w4 w5 hN
    rw [ind_fin s v]
    split_ifs with hv
    · obtain ⟨w, hw, hadj⟩ := nb v hv
      have hw1 : ind s w.val = 1 := by rw [ind_fin, if_pos hw]
      rcases hN w hadj with e | e | e | e | e <;> subst e <;> omega
    · omega
  have hc := card_ind s
  have b0 := ind_le s 0
  have b1 := ind_le s 1
  have b2 := ind_le s 2
  have b3 := ind_le s 3
  have b4 := ind_le s 4
  have b5 := ind_le s 5
  have b6 := ind_le s 6
  have b7 := ind_le s 7
  have b8 := ind_le s 8
  have b9 := ind_le s 9
  have b10 := ind_le s 10
  have t1 : ind s 2 + ind s 3 + ind s 4 ≤ 2 := tri 2 3 4 (by decide) (by decide) (by decide)
  have t2 : ind s 0 + ind s 2 + ind s 3 ≤ 2 := tri 0 2 3 (by decide) (by decide) (by decide)
  have t3 : ind s 0 + ind s 2 + ind s 4 ≤ 2 := tri 0 2 4 (by decide) (by decide) (by decide)
  have t4 : ind s 0 + ind s 3 + ind s 4 ≤ 2 := tri 0 3 4 (by decide) (by decide) (by decide)
  have t5 : ind s 1 + ind s 2 + ind s 3 ≤ 2 := tri 1 2 3 (by decide) (by decide) (by decide)
  have t6 : ind s 1 + ind s 2 + ind s 4 ≤ 2 := tri 1 2 4 (by decide) (by decide) (by decide)
  have t7 : ind s 1 + ind s 3 + ind s 4 ≤ 2 := tri 1 3 4 (by decide) (by decide) (by decide)
  have x1 : ind s 5 + ind s 0 + ind s 2 ≤ 2 := tri 5 0 2 (by decide) (by decide) (by decide)
  have x2 : ind s 5 + ind s 0 + ind s 3 ≤ 2 := tri 5 0 3 (by decide) (by decide) (by decide)
  have x3 : ind s 5 + ind s 0 + ind s 4 ≤ 2 := tri 5 0 4 (by decide) (by decide) (by decide)
  have x4 : ind s 5 + ind s 1 + ind s 2 ≤ 2 := tri 5 1 2 (by decide) (by decide) (by decide)
  have x5 : ind s 5 + ind s 1 + ind s 3 ≤ 2 := tri 5 1 3 (by decide) (by decide) (by decide)
  have x6 : ind s 5 + ind s 1 + ind s 4 ≤ 2 := tri 5 1 4 (by decide) (by decide) (by decide)
  have x7 : ind s 5 + ind s 2 + ind s 3 ≤ 2 := tri 5 2 3 (by decide) (by decide) (by decide)
  have x8 : ind s 5 + ind s 2 + ind s 4 ≤ 2 := tri 5 2 4 (by decide) (by decide) (by decide)
  have x9 : ind s 5 + ind s 3 + ind s 4 ≤ 2 := tri 5 3 4 (by decide) (by decide) (by decide)
  have y1 : ind s 6 + ind s 0 + ind s 2 ≤ 2 := tri 6 0 2 (by decide) (by decide) (by decide)
  have y2 : ind s 6 + ind s 0 + ind s 3 ≤ 2 := tri 6 0 3 (by decide) (by decide) (by decide)
  have y3 : ind s 6 + ind s 0 + ind s 4 ≤ 2 := tri 6 0 4 (by decide) (by decide) (by decide)
  have y4 : ind s 6 + ind s 1 + ind s 2 ≤ 2 := tri 6 1 2 (by decide) (by decide) (by decide)
  have y5 : ind s 6 + ind s 1 + ind s 3 ≤ 2 := tri 6 1 3 (by decide) (by decide) (by decide)
  have y6 : ind s 6 + ind s 1 + ind s 4 ≤ 2 := tri 6 1 4 (by decide) (by decide) (by decide)
  have y7 : ind s 6 + ind s 2 + ind s 3 ≤ 2 := tri 6 2 3 (by decide) (by decide) (by decide)
  have y8 : ind s 6 + ind s 2 + ind s 4 ≤ 2 := tri 6 2 4 (by decide) (by decide) (by decide)
  have y9 : ind s 6 + ind s 3 + ind s 4 ≤ 2 := tri 6 3 4 (by decide) (by decide) (by decide)
  have q1 : ind s 0 + ind s 5 + ind s 1 + ind s 6 ≤ 3 :=
    c4 0 5 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q2 : ind s 0 + ind s 5 + ind s 1 + ind s 7 ≤ 3 :=
    c4 0 5 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q3 : ind s 0 + ind s 6 + ind s 1 + ind s 7 ≤ 3 :=
    c4 0 6 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q4 : ind s 0 + ind s 2 + ind s 1 + ind s 7 ≤ 3 :=
    c4 0 2 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q5 : ind s 0 + ind s 3 + ind s 1 + ind s 7 ≤ 3 :=
    c4 0 3 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q6 : ind s 0 + ind s 4 + ind s 1 + ind s 7 ≤ 3 :=
    c4 0 4 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have n5 : ind s 5 ≤ ind s 0 + ind s 1 + ind s 2 + ind s 3 + ind s 4 :=
    nb5 5 0 1 2 3 4 (by decide)
  have n6 : ind s 6 ≤ ind s 0 + ind s 1 + ind s 2 + ind s 3 + ind s 4 :=
    nb5 6 0 1 2 3 4 (by decide)
  have n7 : ind s 7 ≤ ind s 0 + ind s 1 := nb2 7 0 1 (by decide)
  have n8 : ind s 8 ≤ ind s 2 := nb1 8 2 (by decide)
  have n9 : ind s 9 ≤ ind s 3 := nb1 9 3 (by decide)
  have n10 : ind s 10 ≤ ind s 4 := nb1 10 4 (by decide)
  have key := arith200 _ _ _ _ _ _ _ _ _ _ _ b0 b1 b2 b3 b4 b5 b6 b7 t1 t2 t3 t4 t5 t6 t7
    x1 x2 x3 x4 x5 x6 x7 x8 x9 y1 y2 y3 y4 y5 y6 y7 y8 y9 q1 q2 q3 q4 q5 q6 n5 n6 n7 n8 n9 n10
  rw [hc] at h5
  exact absurd (h5.trans key) (by norm_num)

lemma tree_eq : largestInducedTreeSize G = 4 := by
  unfold largestInducedTreeSize
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨s, rfl, hs⟩
    exact tree_card_le s hs
  · apply le_csSup
    · refine ⟨11, ?_⟩
      rintro _ ⟨t, rfl, -⟩
      simpa using card_le_univ t
    · exact ⟨S4, by decide, claw_tree⟩

/-! ### `⌈1 + l_avg⌉ = 4` -/

def gc (v x : Fin 11) : ℕ :=
  if v.val < 2 then (if x.val = 6 then 1 else if x.val = 7 then 2 else 0)
  else if v.val < 5 then (if 8 ≤ x.val then 2 else if x.val = 1 ∨ x.val = 6 then 1 else 0)
  else (if x.val = 1 then 1 else 0)

lemma gc_lt : ∀ v x : Fin 11, gc v x < 3 := by decide

set_option maxRecDepth 100000 in
lemma gc_clique : ∀ v x y : Fin 11, adjF v x → adjF v y → x ≠ y → gc v x = gc v y →
    adjF x y := by decide

lemma indepNum_induce_le {W : Type*} [Fintype W] (H : SimpleGraph W) (S : Set W) (k : ℕ)
    (h : ∀ t : Finset W, (↑t ⊆ S) → H.IsIndepSet (t : Set W) → t.card ≤ k) :
    (H.induce S).indepNum ≤ k := by
  obtain ⟨s, hs⟩ := (H.induce S).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  rw [← card_map (Function.Embedding.subtype _)]
  apply h
  · intro x hx
    rw [mem_coe, mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    rw [mem_coe, mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun e => hxy (by rw [e])
    exact hs.isIndepSet (mem_coe.2 hx') (mem_coe.2 hy') hne

lemma inc_le (v : Fin 11) : indepNeighborsCard G v ≤ 3 := by
  unfold indepNeighborsCard
  apply indepNum_induce_le
  intro t hsub hind
  have hle := Finset.card_le_card_of_injOn (gc v) (t := range 3) (s := t)
    (fun i _ => mem_coe.2 (mem_range.2 (gc_lt _ _))) ?_
  · rw [card_range] at hle
    exact hle
  · intro x hx y hy hg
    by_contra e
    exact hind hx hy e (gc_clique _ x y (hsub hx) (hsub hy) e hg)

def wit (v : Fin 11) : Finset (Fin 11) :=
  match v.val with
  | 0 => {5, 6, 7}
  | 1 => {5, 6, 7}
  | 2 => {5, 6, 8}
  | 3 => {5, 6, 9}
  | 4 => {5, 6, 10}
  | 5 => {0, 1}
  | 6 => {0, 1}
  | 7 => {0, 1}
  | 8 => {2}
  | 9 => {3}
  | _ => {4}

lemma wit_adj : ∀ v : Fin 11, ∀ x ∈ wit v, adjF v x := by decide

lemma wit_ind : ∀ v : Fin 11, ∀ x ∈ wit v, ∀ y ∈ wit v, ¬ adjF x y := by decide

lemma wit_sum : ∑ v : Fin 11, (wit v).card = 24 := by decide

lemma inc_ge (v : Fin 11) : (wit v).card ≤ indepNeighborsCard G v := by
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

lemma sum_ge : 24 ≤ ∑ v : Fin 11, indepNeighborsCard G v :=
  calc 24 = ∑ v : Fin 11, (wit v).card := wit_sum.symm
    _ ≤ _ := sum_le_sum fun v _ => inc_ge v

lemma sum_le : ∑ v : Fin 11, indepNeighborsCard G v ≤ 33 :=
  calc ∑ v : Fin 11, indepNeighborsCard G v ≤ ∑ _v : Fin 11, 3 := sum_le_sum fun v _ => inc_le v
    _ = 33 := by simp

lemma ceil_eq : ⌈1 + averageIndepNeighbors G⌉ = 4 := by
  rw [Int.ceil_eq_iff]
  unfold averageIndepNeighbors indepNeighbors
  have h11 : (Fintype.card (Fin 11) : ℝ) = 11 := by simp
  rw [h11]
  have A : (24 : ℝ) ≤ ∑ v : Fin 11, (indepNeighborsCard G v : ℝ) := by exact_mod_cast sum_ge
  have B : ∑ v : Fin 11, (indepNeighborsCard G v : ℝ) ≤ 33 := by exact_mod_cast sum_le
  have C1 : 2 < (∑ v : Fin 11, (indepNeighborsCard G v : ℝ)) / 11 := by
    rw [lt_div_iff₀ (by norm_num)]; linarith
  have C2 : (∑ v : Fin 11, (indepNeighborsCard G v : ℝ)) / 11 ≤ 3 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  constructor
  · push_cast; linarith
  · push_cast; linarith

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

lemma ham_false {a b : Fin 11} (p : G.Walk a b) (hp : p.IsHamiltonian) : False := by
  have hpath := hp.isPath
  have key : ∀ v : Fin 11, (∀ u w, G.Adj v u → G.Adj v w → u = w) → v = a ∨ v = b := by
    intro v hv
    by_contra hc
    rw [not_or] at hc
    obtain ⟨u, w, hne, h1, h2⟩ := two_nbrs p hpath v (hp.mem_support v) hc.1 hc.2
    exact hne (hv u w h1 h2)
  have p8 := key 8 (by decide)
  have p9 := key 9 (by decide)
  have p10 := key 10 (by decide)
  rcases p8 with h8 | h8 <;> rcases p9 with h9 | h9 <;> rcases p10 with h10 | h10 <;>
    first
    | exact absurd (h8.trans h9.symm) (by decide)
    | exact absurd (h8.trans h10.symm) (by decide)
    | exact absurd (h9.trans h10.symm) (by decide)

theorem conjecture200 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (largestInducedTreeSize G : ℝ) = ⌈1 + averageIndepNeighbors G⌉ →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  intro h
  have heq : (largestInducedTreeSize G : ℝ) = ⌈1 + averageIndepNeighbors G⌉ := by
    rw [tree_eq, ceil_eq]
    norm_num
  obtain ⟨a, b, p, hp⟩ := h (Fin 11) G connected heq
  exact ham_false p hp

end WrittenOnTheWallII.GraphConjecture200

#print axioms WrittenOnTheWallII.GraphConjecture200.conjecture200
