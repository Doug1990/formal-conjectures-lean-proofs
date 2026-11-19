import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
Induced.lean, Independence.lean, VertexDistance.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture63

open SimpleGraph Finset

/-! Counterexample `C₅[K₄]` on `Fin 20`: clique `i / 4`, cliques adjacent cyclically. -/

def adjF (i j : Fin 20) : Prop :=
  i.val ≠ j.val ∧ (i.val / 4 = j.val / 4 ∨ (i.val / 4 + 1) % 5 = j.val / 4 ∨
    (j.val / 4 + 1) % 5 = i.val / 4)

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

def G : SimpleGraph (Fin 20) where
  Adj := adjF
  symm := ⟨fun x y h => by unfold adjF at *; omega⟩
  loopless := ⟨fun x h => by unfold adjF at h; omega⟩

def midN (v w : ℕ) : ℕ :=
  4 * (if (v / 4 + 2) % 5 = w / 4 then (v / 4 + 1) % 5 else (w / 4 + 1) % 5)

lemma midN_lt (v w : ℕ) : midN v w < 20 := by
  unfold midN; split_ifs <;> omega

def mid (v w : Fin 20) : Fin 20 := ⟨midN v.val w.val, midN_lt _ _⟩

lemma mid_adj (v w : Fin 20) (h : ¬ adjF v w) : adjF v (mid v w) ∧ adjF (mid v w) w := by
  have e : (mid v w).val = midN v.val w.val := rfl
  have hv := v.isLt
  have hw := w.isLt
  unfold adjF at *
  rw [e]
  unfold midN
  split_ifs <;> omega

lemma connected : G.Connected := by
  rw [connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  by_cases h : adjF u v
  · exact (show G.Adj u v from h).reachable
  · obtain ⟨h1, h2⟩ := mid_adj u v h
    exact (show G.Adj u (mid u v) from h1).reachable.trans
      (show G.Adj (mid u v) v from h2).reachable

lemma dist_two (v w : Fin 20) (hne : v ≠ w) (h : ¬ adjF v w) : G.dist v w = 2 := by
  obtain ⟨h1, h2⟩ := mid_adj v w h
  have hle : G.dist v w ≤ 2 := by
    have := dist_le (Walk.cons (show G.Adj v (mid v w) from h1)
      (Walk.cons (show G.Adj (mid v w) w from h2) Walk.nil))
    simpa using this
  have h0 : G.dist v w ≠ 0 := by
    intro e
    rcases dist_eq_zero_iff_eq_or_not_reachable.1 e with e | e
    · exact hne e
    · exact e (connected.preconnected v w)
  have h1' : G.dist v w ≠ 1 := by
    intro e
    rw [dist_eq_one_iff_adj] at e
    exact h e
  omega

def T (v : Fin 20) : Finset (Fin 20) := univ.filter (fun w => ¬ adjF v w)

lemma T_card : ∀ v : Fin 20, (T v).card = 9 := by decide

lemma distEven_ge (v : Fin 20) : 9 ≤ G.distEven v := by
  rw [← T_card v]
  unfold distEven
  apply card_le_card
  intro w hw
  rw [T, mem_filter] at hw
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  by_cases e : v = w
  · subst e; simp
  · rw [dist_two v w e hw.2]; exact even_two

/-! ### `b G ≥ 4` -/

def S4 : Finset (Fin 20) :=
  univ.filter (fun i : Fin 20 => i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9)

lemma mem_S4 (i : Fin 20) (h : i ∈ S4) : i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9 :=
  (mem_filter.1 h).2

lemma b_ge : (4 : ℝ) ≤ b G := by
  have hbip : (G.induce (S4 : Set (Fin 20))).IsBipartite := by
    refine ⟨Coloring.mk (fun x => (if x.1.val % 2 = 0 then 0 else 1 : Fin 2)) ?_⟩
    intro x y hxy
    have hx := mem_S4 _ (mem_coe.1 x.2)
    have hy := mem_S4 _ (mem_coe.1 y.2)
    have h : adjF x.1 y.1 := hxy
    unfold adjF at h
    split_ifs <;> first | decide | (exfalso; omega)
  have hcard : S4.card = 4 := by decide
  unfold b largestInducedBipartiteSubgraphSize
  have : 4 ≤ sSup { n | ∃ s : Finset (Fin 20),
      (G.induce (s : Set _)).IsBipartite ∧ s.card = n } := by
    apply le_csSup
    · refine ⟨Fintype.card (Fin 20), ?_⟩
      rintro _ ⟨t, -, rfl⟩
      exact card_le_univ t
    · exact ⟨S4, hbip, hcard⟩
  exact_mod_cast this

/-! ### Largest induced forest `≤ 4` -/

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

lemma not_acyc_c5 {W : Type*} (H : SimpleGraph W) {a b c d e : W} (hab : H.Adj a b)
    (hbc : H.Adj b c) (hcd : H.Adj c d) (hde : H.Adj d e) (hea : H.Adj e a)
    (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e) : ¬ H.IsAcyclic := by
  intro h
  rw [isAcyclic_iff_forall_adj_isBridge] at h
  have hb := h hab
  rw [isBridge_iff] at hb
  apply hb
  have hab' : a ≠ b := H.ne_of_adj hab
  have e1 : (H.deleteEdges {s(a, b)}).Adj a e :=
    del_adj hea.symm (fun ⟨_, y⟩ => hbe y.symm) (fun ⟨x, _⟩ => hab' x)
  have e2 : (H.deleteEdges {s(a, b)}).Adj e d :=
    del_adj hde.symm (fun ⟨_, y⟩ => hbd y.symm) (fun ⟨x, _⟩ => hbe x.symm)
  have e3 : (H.deleteEdges {s(a, b)}).Adj d c :=
    del_adj hcd.symm (fun ⟨x, _⟩ => had x.symm) (fun ⟨_, y⟩ => hac y.symm)
  have e4 : (H.deleteEdges {s(a, b)}).Adj c b :=
    del_adj hbc.symm (fun ⟨x, _⟩ => hac x.symm) (fun ⟨_, y⟩ => hab' y.symm)
  exact e1.reachable.trans (e2.reachable.trans (e3.reachable.trans e4.reachable))

def F (s : Finset (Fin 20)) (c : ℕ) : Finset (Fin 20) := s.filter (fun i => i.val / 4 = c)

lemma mem_F {s : Finset (Fin 20)} {c : ℕ} {i : Fin 20} : i ∈ F s c ↔ i ∈ s ∧ i.val / 4 = c :=
  mem_filter

lemma forest_le : G.largestInducedForestSize ≤ 4 := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro _ ⟨s, hs, rfl⟩
  have adjI : ∀ i j : Fin 20, (hi : i ∈ s) → (hj : j ∈ s) → adjF i j →
      (G.induce (s : Set _)).Adj ⟨i, hi⟩ ⟨j, hj⟩ := fun i j _ _ h => h
  have hsum : s.card = ∑ c ∈ range 5, (F s c).card :=
    card_eq_sum_card_fiberwise (fun i _ => mem_range.2 (by have := i.isLt; omega))
  simp only [sum_range_succ, sum_range_zero, zero_add] at hsum
  have hc3 : ∀ c, (F s c).card ≤ 2 := by
    intro c
    by_contra hlt
    have h3 : 2 < (F s c).card := by omega
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.1 h3
    rw [mem_F] at ha hb hd
    have nab : a.val ≠ b.val := fun e => hab (Fin.ext e)
    have nad : a.val ≠ d.val := fun e => had (Fin.ext e)
    have nbd : b.val ≠ d.val := fun e => hbd (Fin.ext e)
    exact not_acyc_tri _ (adjI a b ha.1 hb.1 (by unfold adjF; omega))
      (adjI b d hb.1 hd.1 (by unfold adjF; omega))
      (adjI d a hd.1 ha.1 (by unfold adjF; omega)) hs
  have hc2 : ∀ c c', c < 5 → c' < 5 → ((c + 1) % 5 = c' ∨ (c' + 1) % 5 = c) →
      2 ≤ (F s c).card → (F s c').card = 0 := by
    intro c c' hc hc' hcc h2
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h2
    by_contra h0
    obtain ⟨d, hd⟩ := card_pos.1 (Nat.pos_of_ne_zero h0)
    rw [mem_F] at ha hb hd
    have nab : a.val ≠ b.val := fun e => hab (Fin.ext e)
    exact not_acyc_tri _ (adjI a b ha.1 hb.1 (by unfold adjF; omega))
      (adjI b d hb.1 hd.1 (by unfold adjF; omega))
      (adjI d a hd.1 ha.1 (by unfold adjF; omega)) hs
  have h5 : ¬ ∀ c < 5, 1 ≤ (F s c).card := by
    intro hall
    obtain ⟨x0, h0⟩ := card_pos.1 (hall 0 (by norm_num))
    obtain ⟨x1, h1⟩ := card_pos.1 (hall 1 (by norm_num))
    obtain ⟨x2, h2⟩ := card_pos.1 (hall 2 (by norm_num))
    obtain ⟨x3, h3⟩ := card_pos.1 (hall 3 (by norm_num))
    obtain ⟨x4, h4⟩ := card_pos.1 (hall 4 (by norm_num))
    rw [mem_F] at h0 h1 h2 h3 h4
    exact not_acyc_c5 _ (adjI x0 x1 h0.1 h1.1 (by unfold adjF; omega))
      (adjI x1 x2 h1.1 h2.1 (by unfold adjF; omega))
      (adjI x2 x3 h2.1 h3.1 (by unfold adjF; omega))
      (adjI x3 x4 h3.1 h4.1 (by unfold adjF; omega))
      (adjI x4 x0 h4.1 h0.1 (by unfold adjF; omega))
      (fun e => by simp only [Subtype.mk.injEq] at e; subst e; omega)
      (fun e => by simp only [Subtype.mk.injEq] at e; subst e; omega)
      (fun e => by simp only [Subtype.mk.injEq] at e; subst e; omega)
      (fun e => by simp only [Subtype.mk.injEq] at e; subst e; omega) hs
  have t0 := hc3 0
  have t1 := hc3 1
  have t2 := hc3 2
  have t3 := hc3 3
  have t4 := hc3 4
  have a01 := hc2 0 1 (by norm_num) (by norm_num) (by norm_num)
  have a12 := hc2 1 2 (by norm_num) (by norm_num) (by norm_num)
  have a23 := hc2 2 3 (by norm_num) (by norm_num) (by norm_num)
  have a34 := hc2 3 4 (by norm_num) (by norm_num) (by norm_num)
  have a40 := hc2 4 0 (by norm_num) (by norm_num) (by norm_num)
  have b10 := hc2 1 0 (by norm_num) (by norm_num) (by norm_num)
  have b21 := hc2 2 1 (by norm_num) (by norm_num) (by norm_num)
  have b32 := hc2 3 2 (by norm_num) (by norm_num) (by norm_num)
  have b43 := hc2 4 3 (by norm_num) (by norm_num) (by norm_num)
  have b04 := hc2 0 4 (by norm_num) (by norm_num) (by norm_num)
  have h5' : ¬ (1 ≤ (F s 0).card ∧ 1 ≤ (F s 1).card ∧ 1 ≤ (F s 2).card ∧
      1 ≤ (F s 3).card ∧ 1 ≤ (F s 4).card) := by
    rintro ⟨q0, q1, q2, q3, q4⟩
    apply h5
    intro c hc
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) with
      rfl | rfl | rfl | rfl | rfl <;> assumption
  omega

theorem conjecture63 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      let minDistEven := (Finset.univ.image (G.distEven ·)).min' (by simp)
      ⌈((minDistEven : ℝ) + G.b + 1) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  intro h
  have H : (⌈((((Finset.univ.image (G.distEven ·)).min' (by simp) : ℕ) : ℝ) + G.b + 1) / 3⌉
      : ℝ) ≤ (G.largestInducedForestSize : ℝ) := h (Fin 20) G connected
  have hf : (G.largestInducedForestSize : ℝ) ≤ 4 := by exact_mod_cast forest_le
  have hb := b_ge
  have hm9 : 9 ≤ (Finset.univ.image (G.distEven ·)).min' (by simp) := by
    apply Finset.le_min'
    intro y hy
    obtain ⟨v, -, rfl⟩ := mem_image.1 hy
    exact distEven_ge v
  have hm : (9 : ℝ) ≤ (((Finset.univ.image (G.distEven ·)).min' (by simp) : ℕ) : ℝ) := by
    exact_mod_cast hm9
  have h4 : (4 : ℤ) < ⌈((((Finset.univ.image (G.distEven ·)).min' (by simp) : ℕ) : ℝ)
      + G.b + 1) / 3⌉ := by
    rw [Int.lt_ceil]
    push_cast
    linarith
  have h' : ⌈((((Finset.univ.image (G.distEven ·)).min' (by simp) : ℕ) : ℝ)
      + G.b + 1) / 3⌉ ≤ (4 : ℤ) := by
    have := H.trans hf
    exact_mod_cast this
  omega

end WrittenOnTheWallII.GraphConjecture63

#print axioms WrittenOnTheWallII.GraphConjecture63.conjecture63
