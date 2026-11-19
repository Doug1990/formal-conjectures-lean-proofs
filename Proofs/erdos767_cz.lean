import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

open SimpleGraph

namespace Erdos767

/-- Restated from the checkout (ErdosProblems/767.lean). -/
def HasCycleWithIncidentChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

open scoped Classical in
/-- Restated from the checkout (ErdosProblems/767.lean). -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n),
    ¬ HasCycleWithIncidentChords G k ∧ G.edgeFinset.card = m}

namespace CZ

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- A cycle with at least `k` chords at its base vertex gives the structure. -/
theorem of_card {T : Finset V} (hT : k ≤ T.card) {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    (h : ∀ z ∈ T, c.IsChord s(v, z)) : HasCycleWithIncidentChords G k := by
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq hT
  refine ⟨v, c, hc, fun i => (U.equivFin.symm (Fin.cast hU.symm i)).val, ?_, ?_⟩
  · intro i j hij
    have := U.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.cast_injective _ this
  · intro i
    exact h _ (hUT (U.equivFin.symm (Fin.cast hU.symm i)).property)

/-- A path `q` from `v` to a neighbour `y` of `v` whose support contains a set `N` of
at least `k + 2` neighbours of `v` closes up to a cycle with `k` chords at `v`. -/
theorem cyc {v y : V} (q : G.Walk v y) (hq : q.IsPath) (hvy : G.Adj v y) (N : Finset V)
    (hN : ∀ z ∈ N, G.Adj v z ∧ z ∈ q.support) (hk : k + 2 ≤ N.card) :
    HasCycleWithIncidentChords G k := by
  cases q with
  | nil => exact absurd hvy G.irrefl
  | @cons _ x _ hx q' =>
    rw [Walk.cons_isPath_iff] at hq
    obtain ⟨hq', hvq'⟩ := hq
    have hxy : x ≠ y := by
      rintro rfl
      rw [Walk.isPath_iff_nil, ← Walk.eq_nil_iff_nil] at hq'
      subst hq'
      have hsub : N ⊆ {x} := by
        intro z hz
        obtain ⟨hadj, hzs⟩ := hN z hz
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hzs
        rcases hzs with rfl | rfl
        · exact absurd hadj G.irrefl
        · simp
      have := Finset.card_le_card hsub
      simp at this
      omega
    have hcyc : (Walk.cons hvy (Walk.cons hx q').reverse).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      refine ⟨((Walk.cons_isPath_iff _ _).mpr ⟨hq', hvq'⟩).reverse, ?_⟩
      rw [Walk.edges_reverse, List.mem_reverse, Walk.edges_cons, List.mem_cons]
      rintro (h | h)
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨-, h⟩ | ⟨h, -⟩
        · exact hxy h.symm
        · exact G.ne_of_adj hx h
      · exact hvq' (q'.fst_mem_support_of_mem_edges h)
    refine of_card (T := (N.erase y).erase x) ?_ hcyc ?_
    · have h1 := Finset.pred_card_le_card_erase (s := N) (a := y)
      have h2 := Finset.pred_card_le_card_erase (s := N.erase y) (a := x)
      omega
    · intro z hz
      simp only [Finset.mem_erase] at hz
      obtain ⟨hzx, hzy, hzN⟩ := hz
      obtain ⟨hadj, hzs⟩ := hN z hzN
      rw [Walk.isChord_sym2Mk]
      refine ⟨hadj, ?_, Walk.start_mem_support _, ?_⟩
      · rw [Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse,
          Walk.edges_cons, List.mem_cons]
        rintro (h | h | h)
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨-, h⟩ | ⟨h, -⟩
          · exact hzy h
          · exact G.ne_of_adj hvy h
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨-, h⟩ | ⟨h, -⟩
          · exact hzx h
          · exact G.ne_of_adj hx h
        · exact hvq' (q'.fst_mem_support_of_mem_edges h)
      · rw [Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse]
        exact Or.inr hzs

/-- LONGEST-PATH LEMMA: without the structure, every nonempty vertex set `S` has a
vertex with at most `k + 1` neighbours inside `S`. -/
theorem low_deg [Fintype V] (hG : ¬ HasCycleWithIncidentChords G k) (S : Finset V)
    (hS : S.Nonempty) : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ k + 1 := by
  by_contra hcon
  push Not at hcon
  let P : ℕ → Prop := fun n => ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
    (∀ x ∈ p.support, x ∈ S) ∧ p.length = n
  have hP0 : P 0 := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨s, s, Walk.nil, Walk.IsPath.nil, by simpa using hs, rfl⟩
  obtain ⟨a, b, p, hp, hpS, hpl⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) hP0
  have hmax : ∀ (a' b' : V) (p' : G.Walk a' b'), p'.IsPath → (∀ x ∈ p'.support, x ∈ S) →
      p'.length ≤ Nat.findGreatest P (Fintype.card V) := by
    intro a' b' p' h1 h2
    exact Nat.le_findGreatest (le_of_lt h1.length_lt) ⟨a', b', p', h1, h2, rfl⟩
  have hNsupp : ∀ z ∈ S.filter (G.Adj a), z ∈ p.support := by
    intro z hz
    rw [Finset.mem_filter] at hz
    by_contra hzp
    have := hmax z b (Walk.cons hz.2.symm p) (hp.cons hzp) (by
      intro x hx
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hz.1
      · exact hpS x hx)
    rw [Walk.length_cons] at this
    omega
  have hca := hcon a (hpS a p.start_mem_support)
  obtain ⟨y, hyN, hymax⟩ := Finset.exists_max_image (S.filter (G.Adj a))
    (fun z => if h : z ∈ p.support then (p.takeUntil z h).length else 0)
    (Finset.card_pos.mp (by omega))
  have hy := hNsupp y hyN
  apply hG
  refine cyc (p.takeUntil y hy) (hp.takeUntil hy) (Finset.mem_filter.mp hyN).2
    (S.filter (G.Adj a)) ?_ (by omega)
  intro z hz
  refine ⟨(Finset.mem_filter.mp hz).2, ?_⟩
  have hz' := hNsupp z hz
  have hle := hymax z hz
  simp only [dif_pos hy, dif_pos hz'] at hle
  have hpre : (p.takeUntil z hz').support <+: (p.takeUntil y hy).support :=
    List.prefix_of_prefix_length_le (p.support_takeUntil_prefix_support hz')
      (p.support_takeUntil_prefix_support hy) (by simp only [Walk.length_support]; omega)
  exact hpre.subset (Walk.end_mem_support _)

/-- Degeneracy count: edges inside `S` number at most `(k + 1)|S|`. -/
theorem edges_le [Fintype V] (hG : ¬ HasCycleWithIncidentChords G k) :
    ∀ n (S : Finset V), S.card = n →
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)).card ≤ (k + 1) * n := by
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    rw [Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ h
    exact absurd (h _ (Sym2.out_fst_mem e)) (by simp)
  | succ n ih =>
    intro S hS
    obtain ⟨v, hv, hdeg⟩ := low_deg hG S (Finset.card_pos.mp (by omega))
    have hsub : G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S) ⊆
        G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S.erase v) ∪
          (S.filter (G.Adj v)).image (fun z => s(v, z)) := by
      intro e
      induction e using Sym2.ind with
      | h a b =>
        intro he
        simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff] at he
        obtain ⟨hab, hS'⟩ := he
        have ha : a ∈ S := hS' a (Or.inl rfl)
        have hb : b ∈ S := hS' b (Or.inr rfl)
        rw [Finset.mem_union]
        by_cases hav : a = v
        · subst hav
          right
          exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩, rfl⟩
        by_cases hbv : b = v
        · subst hbv
          right
          exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab.symm⟩, Sym2.eq_swap⟩
        left
        simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff,
          Finset.mem_erase]
        refine ⟨hab, ?_⟩
        rintro x (rfl | rfl)
        · exact ⟨hav, ha⟩
        · exact ⟨hbv, hb⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S.erase v))
      ((S.filter (G.Adj v)).image (fun z => s(v, z)))
    have h3 := Finset.card_image_le (s := S.filter (G.Adj v)) (f := fun z => s(v, z))
    have h4 := ih (S.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
    rw [Nat.mul_succ]
    omega

end CZ

/-- Czipszer proved that $g_k(n)\leq (k+1)n$. -/
theorem erdos_767.variants.czipszer (k n : ℕ) : g k n ≤ (k + 1) * n := by
  classical
  apply csSup_le'
  rintro m ⟨G, hG, rfl⟩
  have := CZ.edges_le hG n Finset.univ (by simp)
  simpa using this

end Erdos767

#print axioms Erdos767.erdos_767.variants.czipszer
