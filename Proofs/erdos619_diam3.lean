import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Preorder.Finite

open SimpleGraph

namespace Erdos619

/-- If adding the edge `uv` to a triangle-free `H` creates a triangle, then `u` and `v`
have a common neighbour in `H`. -/
lemma common_nbr {V : Type*} (H : SimpleGraph V) (hH : H.CliqueFree 3) (u v : V)
    (huv : u ≠ v) (hn : ¬ H.Adj u v)
    (hmax : ¬ (H ⊔ SimpleGraph.fromRel (fun x y => x = u ∧ y = v)).CliqueFree 3) :
    ∃ w, H.Adj u w ∧ H.Adj w v := by
  classical
  obtain ⟨s, hs⟩ := not_forall.1 hmax
  obtain ⟨a, b, c, h1, h2, h3, -⟩ := is3Clique_iff.1 (not_not.1 hs)
  clear hmax hs
  simp only [sup_adj, fromRel_adj] at h1 h2 h3
  rcases h1 with h1 | ⟨n1, ⟨e1, f1⟩ | ⟨e1, f1⟩⟩ <;>
  rcases h2 with h2 | ⟨n2, ⟨e2, f2⟩ | ⟨e2, f2⟩⟩ <;>
  rcases h3 with h3 | ⟨n3, ⟨e3, f3⟩ | ⟨e3, f3⟩⟩ <;>
  subst_vars <;>
  first
    | exact (hH _ (is3Clique_triple_iff.2 ⟨h1, h2, h3⟩)).elim
    | exact ⟨a, ‹_›, ‹_›⟩ | exact ⟨a, H.adj_symm ‹_›, ‹_›⟩
    | exact ⟨a, ‹_›, H.adj_symm ‹_›⟩ | exact ⟨a, H.adj_symm ‹_›, H.adj_symm ‹_›⟩
    | exact ⟨b, ‹_›, ‹_›⟩ | exact ⟨b, H.adj_symm ‹_›, ‹_›⟩
    | exact ⟨b, ‹_›, H.adj_symm ‹_›⟩ | exact ⟨b, H.adj_symm ‹_›, H.adj_symm ‹_›⟩
    | exact ⟨c, ‹_›, ‹_›⟩ | exact ⟨c, H.adj_symm ‹_›, ‹_›⟩
    | exact ⟨c, ‹_›, H.adj_symm ‹_›⟩ | exact ⟨c, H.adj_symm ‹_›, H.adj_symm ‹_›⟩
    | (exfalso; simp_all)

theorem erdos_619.variants.add_edges_diam_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ 3 := by
  have _unused := hG
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ H.CliqueFree 3}
  obtain ⟨H, ⟨hGH, hH⟩, hmax⟩ := S.toFinite.exists_maximal ⟨G, le_rfl, hG'⟩
  have key : ∀ u v, u ≠ v → ¬ H.Adj u v → ∃ w, H.Adj u w ∧ H.Adj w v := by
    intro u v huv hn
    apply common_nbr H hH u v huv hn
    intro hfree
    have hle : H ≤ H ⊔ SimpleGraph.fromRel (fun x y => x = u ∧ y = v) := le_sup_left
    have h2 := hmax ⟨hGH.trans hle, hfree⟩ hle
    apply hn
    apply h2
    simp only [sup_adj, fromRel_adj]
    exact Or.inr ⟨huv, by simp⟩
  refine ⟨H, hGH, hH, ?_⟩
  refine ediam_le_of_edist_le fun u v => ?_
  by_cases huv : u = v
  · subst huv
    simp
  by_cases hadj : H.Adj u v
  · calc H.edist u v ≤ (Walk.cons hadj Walk.nil).length := edist_le _
      _ ≤ 3 := by exact_mod_cast (show (Walk.cons hadj Walk.nil).length ≤ 3 by simp)
  · obtain ⟨w, h1, h2⟩ := key u v huv hadj
    calc H.edist u v ≤ (Walk.cons h1 (Walk.cons h2 Walk.nil)).length := edist_le _
      _ ≤ 3 := by
        exact_mod_cast (show (Walk.cons h1 (Walk.cons h2 Walk.nil)).length ≤ 3 by simp)

end Erdos619

#print axioms Erdos619.erdos_619.variants.add_edges_diam_three
