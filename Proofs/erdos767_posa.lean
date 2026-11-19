import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
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

end CZ

namespace PO

open scoped Classical

variable {V : Type*} {G : SimpleGraph V}

/-- Number of edges inside `S`. -/
noncomputable def E [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)).card

theorem E_erase [Fintype V] (S : Finset V) (v : V) :
    E G S ≤ E G (S.erase v) + (S.filter (G.Adj v)).card := by
  unfold E
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
  omega

theorem tri [Fintype V] (x y z : V) :
    G.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ ({x, y, z} : Finset V)) ⊆
      ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeSet) := by
  intro e
  induction e using Sym2.ind with
  | h a b =>
    intro he
    simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff] at he
    obtain ⟨hab, hS⟩ := he
    have ha := hS a (Or.inl rfl)
    have hb := hS b (Or.inr rfl)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine Finset.mem_filter.mpr ⟨?_, G.mem_edgeSet.mpr hab⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd hab G.irrefl | simp

theorem E3 [Fintype V] (x y z : V) : E G {x, y, z} ≤ 3 := by
  unfold E
  have h1 := Finset.card_le_card (tri (G := G) x y z)
  have h2 := Finset.card_filter_le ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V))
    (fun e => e ∈ G.edgeSet)
  have h3 := Finset.card_le_three (a := s(x, y)) (b := s(x, z)) (c := s(y, z))
  omega

theorem tri_adj [Fintype V] {x y z : V} (h : 3 ≤ E G {x, y, z}) :
    G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  unfold E at h
  have h1 := Finset.card_le_card (tri (G := G) x y z)
  have h3 := Finset.card_le_three (a := s(x, y)) (b := s(x, z)) (c := s(y, z))
  have h2 : (({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)).filter
      (fun e => e ∈ G.edgeSet)) = {s(x, y), s(x, z), s(y, z)} :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have m : ∀ e ∈ ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)), e ∈ G.edgeSet := by
    intro e he
    rw [← h2] at he
    exact (Finset.mem_filter.mp he).2
  exact ⟨m s(x, y) (by simp), m s(x, z) (by simp), m s(y, z) (by simp)⟩

/-- `K₄` minus an edge (the 4-cycle `p v q r` with chord `pq`) has a chorded cycle. -/
theorem k4 {p v q r : V} (hpv : G.Adj p v) (hvq : G.Adj v q) (hqr : G.Adj q r)
    (hrp : G.Adj r p) (hpq : G.Adj p q) (h1 : p ≠ q) (h2 : p ≠ r) (h3 : v ≠ r) :
    HasCycleWithIncidentChords G 1 := by
  have hpv' := G.ne_of_adj hpv
  have hvq' := G.ne_of_adj hvq
  have hqr' := G.ne_of_adj hqr
  refine CZ.cyc (k := 1) (Walk.cons hpv (Walk.cons hvq (Walk.cons hqr Walk.nil))) ?_
    hrp.symm {v, q, r} ?_ ?_
  · simp [Walk.cons_isPath_iff, hpv', h1, h2, hvq', h3, hqr']
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨hpv, by simp⟩
    · exact ⟨hpq, by simp⟩
    · exact ⟨hrp.symm, by simp⟩
  · rw [Finset.card_eq_three.mpr ⟨v, q, r, hvq', h3, hqr', rfl⟩]

theorem base [Fintype V] (hG : ¬ HasCycleWithIncidentChords G 1) (S : Finset V)
    (hS : S.card = 4) : E G S ≤ 4 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv, hdeg⟩ := CZ.low_deg hG S (Finset.card_pos.mp (by omega))
  have he := E_erase (G := G) S v
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp
    (show (S.erase v).card = 3 by rw [Finset.card_erase_of_mem hv]; omega)
  have h3 : E G (S.erase v) ≤ 3 := hT ▸ E3 x y z
  have htri := tri_adj (G := G) (x := x) (y := y) (z := z) (by rw [← hT]; omega)
  have hd : 1 < (S.filter (G.Adj v)).card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hd
  rw [Finset.mem_filter] at hp hq
  have hpT : p ∈ S.erase v := Finset.mem_erase.mpr ⟨(G.ne_of_adj hp.2).symm, hp.1⟩
  have hqT : q ∈ S.erase v := Finset.mem_erase.mpr ⟨(G.ne_of_adj hq.2).symm, hq.1⟩
  have hT' : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, a ≠ b → G.Adj a b := by
    rw [hT]
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain ⟨t1, t2, t3⟩ := htri
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | exact t1 | exact t2 | exact t3 | exact t1.symm | exact t2.symm | exact t3.symm
  have hc1 : ((S.erase v).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hpT, Finset.card_erase_of_mem hv]; omega
  have hq2 : q ∈ (S.erase v).erase p := Finset.mem_erase.mpr ⟨fun h => hpq h.symm, hqT⟩
  have hc2 : (((S.erase v).erase p).erase q).card = 1 := by
    rw [Finset.card_erase_of_mem hq2]; omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < (((S.erase v).erase p).erase q).card by omega)
  simp only [Finset.mem_erase] at hr
  obtain ⟨hrq, hrp, hrv, hrS⟩ := hr
  have hrT : r ∈ S.erase v := Finset.mem_erase.mpr ⟨hrv, hrS⟩
  exact hG (k4 hp.2.symm hq.2 (hT' q hqT r hrT (fun h => hrq h.symm))
    (hT' r hrT p hpT hrp) (hT' p hpT q hqT hpq) hpq (fun h => hrp h.symm)
    (fun h => hrv h.symm))

theorem upper [Fintype V] (hG : ¬ HasCycleWithIncidentChords G 1) :
    ∀ n, 4 ≤ n → ∀ S : Finset V, S.card = n → E G S ≤ 2 * n - 4 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro S hS; have := base hG S hS; omega
  | succ n hn ih =>
    intro S hS
    obtain ⟨v, hv, hdeg⟩ := CZ.low_deg hG S (Finset.card_pos.mp (by omega))
    have he := E_erase (G := G) S v
    have h4 := ih (S.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
    omega

/-- `K_{2,n-2}` with small side `{0, 1}`. -/
def K (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val < 2 ∧ 2 ≤ j.val) ∨ (j.val < 2 ∧ 2 ≤ i.val)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> omega⟩

theorem K_adj {n : ℕ} (i j : Fin n) :
    (K n).Adj i j ↔ (i.val < 2 ∧ 2 ≤ j.val) ∨ (j.val < 2 ∧ 2 ≤ i.val) := Iff.rfl

theorem K_no (n : ℕ) : ¬ HasCycleWithIncidentChords (K n) 1 := by
  rintro ⟨v, c, hc, f, -, hf⟩
  have key : ∀ x y : Fin n, x.val < 2 → 2 ≤ y.val → y ∈ c.support → s(y, x) ∈ c.edges := by
    intro x y hx hy hyc
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hyc
    by_contra hnot
    have hsub : c.toSubgraph.neighborSet y ⊆ {(⟨1 - x.val, by omega⟩ : Fin n)} := by
      intro z hz
      have hadj : c.toSubgraph.Adj y z := hz
      have hG : (K n).Adj y z := hadj.adj_sub
      have hzx : z ≠ x := by
        rintro rfl
        exact hnot (Walk.adj_toSubgraph_iff_mem_edges.mp hadj)
      have hzx' : z.val ≠ x.val := fun h => hzx (Fin.ext h)
      rw [K_adj] at hG
      rw [Set.mem_singleton_iff, Fin.ext_iff]
      show z.val = 1 - x.val
      omega
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at this
    omega
  have hch := hf 0
  rw [Walk.isChord_sym2Mk] at hch
  obtain ⟨hadj, hne, hv, hw⟩ := hch
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (by rw [Sym2.eq_swap]; exact key v (f 0) h1 h2 hw)
  · exact hne (key (f 0) v h1 h2 hv)

theorem K_card (n : ℕ) (hn : 4 ≤ n) : (K n).edgeFinset.card = 2 * n - 4 := by
  have hsum := (K n).sum_degrees_eq_twice_card_edges
  have hAc : ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < 2)).card = 2 := by
    have : (Finset.univ : Finset (Fin n)).filter (fun j => j.val < 2) =
        {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [this, Finset.card_pair]
    simp [Fin.ext_iff]
  have hBc : ((Finset.univ : Finset (Fin n)).filter (fun j => ¬ j.val < 2)).card = n - 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j => j.val < 2)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hdeg : ∀ i : Fin n, (K n).degree i = if i.val < 2 then n - 2 else 2 := by
    intro i
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    split_ifs with hi
    · rw [← hBc]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, K_adj]
      constructor <;> intro h <;> omega
    · rw [← hAc]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, K_adj]
      constructor <;> intro h <;> omega
  rw [Finset.sum_congr rfl (fun i _ => hdeg i), Finset.sum_ite] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  rw [hAc, hBc] at hsum
  omega

end PO

/-- Pósa proved that $g_1(n)=2n-4$ for $n\geq 4$. -/
theorem erdos_767.variants.posa (n : ℕ) (hn : 4 ≤ n) : g 1 n = 2 * n - 4 := by
  classical
  have ub : ∀ m ∈ {m | ∃ G : SimpleGraph (Fin n),
      ¬ HasCycleWithIncidentChords G 1 ∧ G.edgeFinset.card = m}, m ≤ 2 * n - 4 := by
    rintro m ⟨G, hG, rfl⟩
    have := PO.upper hG n hn Finset.univ (by simp)
    simpa [PO.E] using this
  unfold g
  apply le_antisymm
  · exact csSup_le' ub
  · exact le_csSup ⟨_, ub⟩ ⟨PO.K n, PO.K_no n, PO.K_card n hn⟩

end Erdos767

#print axioms Erdos767.erdos_767.variants.posa
