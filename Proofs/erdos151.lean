import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Minimal
import Mathlib.Tactic.Linarith

open SimpleGraph Finset

namespace Erdos151

variable {V : Type*}

/-- Restated from the checkout (ErdosProblems/151.lean). -/
def IsBigMaximalClique (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal (fun t : Finset V ↦ G.IsClique (t : Set V)) s ∧ 2 ≤ s.card

def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s, IsBigMaximalClique G s → ∃ v ∈ s, v ∈ T

noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, IsCliqueTransversal G T ∧ T.card = k}

noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

namespace CT

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- If no big maximal clique lies inside `I`, the complement of `I` is a transversal. -/
lemma tau_le (I : Finset (Fin n)) (hI : ∀ s, IsBigMaximalClique G s → ¬ s ⊆ I) :
    cliqueTransversalNumber G ≤ n - I.card := by
  have hT : IsCliqueTransversal G (univ \ I) := by
    intro s hs
    have := hI s hs
    rw [Finset.not_subset] at this
    obtain ⟨v, hv, hvI⟩ := this
    exact ⟨v, hv, by simpa using hvI⟩
  have h1 : cliqueTransversalNumber G ≤ (univ \ I).card := Nat.sInf_le ⟨_, hT, rfl⟩
  rw [Finset.card_univ_sdiff, Fintype.card_fin] at h1
  exact h1

lemma indep_ok (I : Finset (Fin n)) (hI : G.IsIndepSet (I : Set (Fin n))) :
    ∀ s, IsBigMaximalClique G s → ¬ s ⊆ I := by
  intro s ⟨hmax, h2⟩ hsub
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.1 h2
  exact hI (hsub hu) (hsub hw) huw (hmax.prop hu hw huw)

lemma nbhd_ok [DecidableRel G.Adj] (v : Fin n) :
    ∀ s, IsBigMaximalClique G s → ¬ s ⊆ G.neighborFinset v := by
  intro s ⟨hmax, _⟩ hsub
  have hvs : v ∉ s := fun h => G.irrefl ((G.mem_neighborFinset v v).1 (hsub h))
  have hcl : G.IsClique ((insert v s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert, SimpleGraph.isClique_insert]
    exact ⟨hmax.prop, fun b hb _ => (G.mem_neighborFinset v b).1 (hsub hb)⟩
  have := hmax.2 hcl (Finset.subset_insert v s)
  exact hvs (this (mem_insert_self v s))

end CT

open CT in
theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  classical
  have hbdd : BddAbove {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ s, G.IsNIndepSet k s} := by
    refine ⟨n, fun k hk => ?_⟩
    obtain ⟨s, hs⟩ := hk ⊥ (cliqueFree_bot (by norm_num))
    rw [← hs.card_eq]
    simpa using card_le_univ s
  have hne : ({k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ s, G.IsNIndepSet k s} : Set ℕ).Nonempty :=
    ⟨0, fun G _ => ⟨∅, ⟨by simp [SimpleGraph.IsIndepSet], by simp⟩⟩⟩
  obtain ⟨I, hI⟩ := Nat.sSup_mem hne hbdd G hG
  have := tau_le G I (indep_ok G I hI.isIndepSet)
  rw [hI.card_eq] at this
  exact this

open CT in
theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  have h4 : s * s ≤ n := hs ▸ Nat.sqrt_le n
  rw [← hs]
  obtain ⟨S, hS, hmaxS⟩ := Finset.exists_max_image
    ((univ : Finset (Fin n)).powerset.filter (fun I : Finset (Fin n) => G.IsIndepSet (↑I : Set (Fin n))))
    Finset.card ⟨∅, by simp [SimpleGraph.IsIndepSet]⟩
  have hSi : G.IsIndepSet (S : Set (Fin n)) := (mem_filter.1 hS).2
  by_cases hc : s ≤ S.card
  · exact (tau_le G S (indep_ok G S hSi)).trans (by omega)
  push Not at hc
  have hdom : ∀ x : Fin n, ∃ v ∈ S, x = v ∨ G.Adj v x := by
    intro x
    by_contra hx
    push Not at hx
    have hxS : x ∉ S := fun h => (hx x h).1 rfl
    have hind : G.IsIndepSet (insert x (S : Set (Fin n))) := by
      unfold SimpleGraph.IsIndepSet
      rw [Set.pairwise_insert]
      exact ⟨hSi, fun b hb _ => ⟨fun h => (hx b hb).2 h.symm, (hx b hb).2⟩⟩
    have := hmaxS (insert x S) (by simpa using hind)
    rw [Finset.card_insert_of_notMem hxS] at this
    omega
  by_contra hlt
  push Not at hlt
  have hdeg : ∀ v ∈ S, (G.neighborFinset v).card < s := by
    intro v _
    by_contra hv
    push Not at hv
    have := tau_le G _ (nbhd_ok G v)
    omega
  have hcov : (univ : Finset (Fin n)) ⊆
      S.biUnion (fun v => insert v (G.neighborFinset v)) := by
    intro x _
    obtain ⟨v, hv, hx⟩ := hdom x
    rw [Finset.mem_biUnion]
    refine ⟨v, hv, ?_⟩
    rcases hx with rfl | h
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem ((G.mem_neighborFinset v x).2 h)
  have h1 := (card_le_card hcov).trans card_biUnion_le
  rw [card_univ, Fintype.card_fin] at h1
  have h2 : ∑ v ∈ S, (insert v (G.neighborFinset v)).card ≤ ∑ _v ∈ S, s := by
    apply sum_le_sum
    intro v hv
    exact (card_insert_le _ _).trans (hdeg v hv)
  rw [sum_const, smul_eq_mul] at h2
  have h3 : S.card * s + s ≤ s * s := by nlinarith
  omega

end Erdos151

#print axioms Erdos151.erdos_151.variants.sqrt_bound
#print axioms Erdos151.erdos_151.variants.cliqueFree_three
