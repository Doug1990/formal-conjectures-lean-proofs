import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SpanningTree.lean). -/
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset List

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture5

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

omit [Fintype V] [DecidableEq V] [Nontrivial V] in
lemma parent_ex {G : SimpleGraph V} (hc : G.Connected) {v w : V} (hw : w ≠ v) :
    ∃ u, G.Adj w u ∧ G.dist v u + 1 = G.dist v w := by
  obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist w v
  cases q with
  | nil => exact absurd rfl hw
  | @cons _ u _ h q' =>
    refine ⟨u, h, ?_⟩
    have h1 : G.dist u v ≤ q'.length := dist_le q'
    have h2 : G.dist w v ≤ G.dist w u + G.dist u v := hc.dist_triangle
    have h3 : G.dist w u ≤ 1 := by
      have := dist_le (Walk.cons h Walk.nil)
      simpa using this
    simp only [Walk.length_cons] at hq
    rw [show G.dist v u = G.dist u v from dist_comm, show G.dist v w = G.dist w v from dist_comm]
    omega

omit [DecidableEq V] [Nontrivial V] in
lemma Ls_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ Ls G := by
  unfold Ls
  apply Real.sSup_nonneg
  rintro _ ⟨T, -, rfl⟩
  exact Nat.cast_nonneg _

omit [DecidableEq V] in
/-- BFS-type spanning tree: every vertex on the outermost sphere around `v` is a leaf. -/
lemma key (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (v : V) (r : ℕ)
    (hr : 1 ≤ r) (hle : ∀ w, G.dist v w ≤ r) (s : Finset V) (hs : ∀ w ∈ s, G.dist v w = r) :
    (s.card : ℝ) ≤ Ls G := by
  have hp0 : ∀ w, w ≠ v → ∃ u, G.Adj w u ∧ G.dist v u + 1 = G.dist v w :=
    fun w hw => parent_ex hc hw
  choose! p hp using hp0
  let H : SimpleGraph V := SimpleGraph.fromRel (fun a b => G.Adj a b ∧
    ((G.dist v a < r ∧ G.dist v b < r) ∨ (G.dist v a = r ∧ b = p a)))
  have hHG : H ≤ G := by
    intro a b hab
    rcases hab with ⟨_, h | h⟩
    · exact h.1
    · exact h.1.symm
  have hreach : ∀ k w, G.dist v w = k → H.Reachable v w := by
    intro k
    induction k with
    | zero =>
      intro w hw
      rw [hc.dist_eq_zero_iff] at hw
      subst hw
      exact Reachable.refl _
    | succ k ih =>
      intro w hw
      have hwv : w ≠ v := by
        rintro rfl
        simp at hw
      obtain ⟨hadj, hd⟩ := hp w hwv
      have hu : H.Reachable v (p w) := ih _ (by omega)
      refine hu.trans (Adj.reachable ?_)
      refine ⟨fun h => ?_, ?_⟩
      · rw [h] at hd
        omega
      · rcases Nat.lt_or_ge (G.dist v w) r with h | h
        · exact Or.inl ⟨hadj.symm, Or.inl ⟨by omega, h⟩⟩
        · exact Or.inr ⟨hadj, Or.inr ⟨le_antisymm (hle w) h, rfl⟩⟩
  have hHc : H.Connected :=
    (connected_iff_exists_forall_reachable H).mpr ⟨v, fun w => hreach _ w rfl⟩
  obtain ⟨T, hTH, hT⟩ := hHc.exists_isTree_le
  let T' : G.Subgraph := SimpleGraph.toSubgraph T (hTH.trans hHG)
  have hspan : T'.IsSpanning := SimpleGraph.toSubgraph.isSpanning T _
  have htree : T'.coe.IsTree :=
    (Subgraph.spanningCoeEquivCoeOfSpanning T' hspan).isTree_iff.mp hT
  have hleaf : ∀ w ∈ s, ∃! u, T'.Adj w u := by
    intro w hw
    have hwr := hs w hw
    have uniq : ∀ z, T.Adj w z → z = p w := by
      intro z hz
      obtain ⟨-, h1 | h1⟩ := hTH hz
      · rcases h1.2 with h2 | h2
        · omega
        · exact h2.2
      · rcases h1.2 with h2 | h2
        · omega
        · have hzv : z ≠ v := by
            rintro rfl
            have := h2.1
            simp at this
            omega
          have := (hp z hzv).2
          rw [← h2.2] at this
          omega
    obtain ⟨x, hx⟩ := exists_ne w
    obtain ⟨q⟩ := hT.connected.preconnected w x
    cases q with
    | nil => exact absurd rfl hx
    | @cons _ u _ h _ =>
      refine ⟨u, h, fun y hy => ?_⟩
      rw [uniq y hy, uniq u h]
  unfold Ls
  refine le_trans ?_ (le_csSup ?_ (Set.mem_image_of_mem _ (?_ : T' ∈ _)))
  · beta_reduce
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have e : ∀ (i1 : Fintype ↑T'.verts), w ∈ @Set.toFinset _ T'.verts i1 :=
        fun i1 => Set.mem_toFinset.mpr (hspan w)
      exact e _
    · have e2 : ∀ (i2 : Fintype ↑(T'.neighborSet w)), @Subgraph.degree _ _ T' w i2 = 1 :=
        fun i2 => Subgraph.degree_eq_one_iff_existsUnique_adj.mpr (hleaf w hw)
      exact e2 _
  · refine ⟨Fintype.card V, ?_⟩
    rintro _ ⟨T, -, rfl⟩
    beta_reduce
    exact_mod_cast Finset.card_le_univ _
  · exact ⟨hspan, htree⟩

open scoped Classical in
theorem conjecture5 (G : SimpleGraph V) (h_conn : G.Connected) :
    letI centers := { v : V | G.eccent v = G.radius }
    letI r_nat := G.radius.toNat
    letI sphere_verts (v : V) : Set V := { w | G.dist v w = r_nat }
    letI sphere_size (v : V) : ℝ := ↑(Finset.univ.filter (fun w => w ∈ sphere_verts v)).card
    letI max_sphere_size := sSup (sphere_size '' centers)
    max_sphere_size ≤ Ls G := by
  apply Real.sSup_le
  · rintro _ ⟨v, hv, rfl⟩
    beta_reduce
    have hv' : G.eccent v = G.radius := hv
    obtain ⟨w0, hw0⟩ := G.exists_edist_eq_eccent_of_finite v
    have hd0 : (G.dist v w0 : ℕ∞) = G.edist v w0 := (h_conn v w0).coe_dist_eq_edist
    have hrad : G.radius.toNat = G.dist v w0 := by
      rw [← hv', ← hw0, ← hd0, ENat.toNat_natCast]
    refine key G h_conn v (G.dist v w0) ?_ ?_ _ ?_
    · have hne := G.eccent_ne_zero v
      rw [← hw0, ← hd0] at hne
      have : G.dist v w0 ≠ 0 := by exact_mod_cast hne
      omega
    · intro w
      have h1 : G.edist v w ≤ G.eccent v := edist_le_eccent
      rw [← (h_conn v w).coe_dist_eq_edist, ← hw0, ← hd0] at h1
      exact_mod_cast h1
    · intro w hw
      have := (Finset.mem_filter.mp hw).2
      rw [← hrad]
      exact this
  · exact Ls_nonneg G

end WrittenOnTheWallII.GraphConjecture5

#print axioms WrittenOnTheWallII.GraphConjecture5.conjecture5
