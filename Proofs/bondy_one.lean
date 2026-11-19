import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace SimpleGraph

/-- restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Connectivity.lean -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

noncomputable def circumference {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup G.cycleLengths

end SimpleGraph

open SimpleGraph

namespace Arxiv.«2606.03696»

variable {V : Type*} [Fintype V] [DecidableEq V]

def offWalk {a b : V} {G : SimpleGraph V} (w : G.Walk a b) : Set V :=
  {v | v ∉ w.support}

/-- A path with vertices g 0, …, g m. -/
def IsP (G : SimpleGraph V) (m : ℕ) (g : ℕ → V) : Prop :=
  (∀ i < m, G.Adj (g i) (g (i + 1))) ∧ ∀ i ≤ m, ∀ j ≤ m, g i = g j → i = j

lemma len_bound {G : SimpleGraph V} {m : ℕ} {g : ℕ → V} (h : IsP G m g) :
    m + 1 ≤ Fintype.card V := by
  have hinj : Set.InjOn g (Finset.range (m + 1) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact h.2 a (by omega) b (by omega) hab
  have := Finset.card_image_of_injOn hinj
  rw [Finset.card_range] at this
  rw [← this]
  exact Finset.card_le_univ _

open Classical in
lemma exists_max (G : SimpleGraph V) [Nonempty V] :
    ∃ m g, IsP G m g ∧ ∀ m' g', IsP G m' g' → m' ≤ m := by
  let Q : ℕ → Prop := fun m => ∃ g, IsP G m g
  have hQ0 : Q 0 := ⟨fun _ => Classical.arbitrary V, fun i hi => by omega,
    fun i hi j hj _ => by omega⟩
  have hspec := Nat.findGreatest_spec (P := Q) (Nat.zero_le (Fintype.card V)) hQ0
  obtain ⟨g, hg⟩ := hspec
  refine ⟨_, g, hg, fun m' g' h' => ?_⟩
  have hb := len_bound h'
  exact Nat.le_findGreatest (by omega) ⟨g', h'⟩

omit [Fintype V] in
lemma head_nbr{G : SimpleGraph V} {m : ℕ} {g : ℕ → V} (h : IsP G m g)
    (hmax : ∀ m' g', IsP G m' g' → m' ≤ m) {y : V} (hy : G.Adj (g 0) y) :
    ∃ i ≤ m, g i = y := by
  by_contra hc
  push Not at hc
  let g' : ℕ → V := fun j => if j = 0 then y else g (j - 1)
  have : IsP G (m + 1) g' := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · simp only [g']
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simpa using hy.symm
      · rw [if_neg (by omega), if_neg (by omega)]
        have := h.1 (i - 1) (by omega)
        rwa [show i - 1 + 1 = i + 1 - 1 by omega] at this
    · simp only [g'] at hij
      split_ifs at hij with h1 h2 h2
      · omega
      · exact absurd hij.symm (hc _ (by omega))
      · exact absurd hij (hc _ (by omega))
      · have := h.2 _ (by omega) _ (by omega) hij
        omega
  have := hmax _ _ this
  omega

omit [Fintype V] in
lemma tail_nbr{G : SimpleGraph V} {m : ℕ} {g : ℕ → V} (h : IsP G m g)
    (hmax : ∀ m' g', IsP G m' g' → m' ≤ m) {y : V} (hy : G.Adj (g m) y) :
    ∃ i ≤ m, g i = y := by
  by_contra hc
  push Not at hc
  let g' : ℕ → V := fun j => if j ≤ m then g j else y
  have : IsP G (m + 1) g' := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · simp only [g']
      by_cases him : i + 1 ≤ m
      · rw [if_pos (by omega), if_pos him]
        exact h.1 i (by omega)
      · rw [if_pos (by omega), if_neg him]
        have : i = m := by omega
        subst this
        exact hy
    · simp only [g'] at hij
      split_ifs at hij with h1 h2 h2
      · exact h.2 _ h1 _ h2 hij
      · exact absurd hij (hc _ h1)
      · exact absurd hij.symm (hc _ h2)
      · omega
  have := hmax _ _ this
  omega

lemma cycle_of_max {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} {g : ℕ → V}
    (h : IsP G m g) (hmax : ∀ m' g', IsP G m' g' → m' ≤ m)
    (hδ : ∀ v, Fintype.card V ≤ 2 * G.degree v) (h3 : 3 ≤ Fintype.card V) :
    ∃ c, IsP G m c ∧ G.Adj (c m) (c 0) ∧ 2 ≤ m := by
  let A := (Finset.range m).filter (fun i => G.Adj (g 0) (g (i + 1)))
  let B := (Finset.range m).filter (fun i => G.Adj (g m) (g i))
  have hA : G.neighborFinset (g 0) ⊆ A.image (fun i => g (i + 1)) := by
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨i, hi, rfl⟩ := head_nbr h hmax hy
    have hi0 : i ≠ 0 := by rintro rfl; exact G.irrefl hy
    refine Finset.mem_image.2 ⟨i - 1, ?_, ?_⟩
    · simp only [A, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rwa [show i - 1 + 1 = i by omega]
    · show g (i - 1 + 1) = g i
      rw [show i - 1 + 1 = i by omega]
  have hB : G.neighborFinset (g m) ⊆ B.image g := by
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨i, hi, rfl⟩ := tail_nbr h hmax hy
    have him : i ≠ m := by rintro rfl; exact G.irrefl hy
    refine Finset.mem_image.2 ⟨i, ?_, rfl⟩
    simp only [B, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hy⟩
  have cA : G.degree (g 0) ≤ A.card := by
    rw [← card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hA).trans Finset.card_image_le
  have cB : G.degree (g m) ≤ B.card := by
    rw [← card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hB).trans Finset.card_image_le
  have hAm : A.card ≤ m := by
    have := Finset.card_le_card (Finset.filter_subset (fun i => G.Adj (g 0) (g (i + 1)))
      (Finset.range m))
    simpa using this
  have hU : (A ∪ B).card ≤ m := by
    have hsub : A ∪ B ⊆ Finset.range m :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have := Finset.card_le_card hsub
    simpa using this
  have hbound := len_bound h
  have hd0 := hδ (g 0)
  have hdm := hδ (g m)
  have hIU := Finset.card_union_add_card_inter A B
  have hne : (A ∩ B).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨i, hi⟩ := hne
  simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨⟨him, hAi⟩, -, hBi⟩ := hi
  let c : ℕ → V := fun j => if j ≤ i then g j else g (m + i + 1 - j)
  refine ⟨c, ⟨fun j hj => ?_, fun a ha b hb hab => ?_⟩, ?_, by omega⟩
  · simp only [c]
    by_cases hji : j < i
    · rw [if_pos (by omega), if_pos (by omega)]
      exact h.1 j (by omega)
    · by_cases hji' : j = i
      · subst hji'
        rw [if_pos le_rfl, if_neg (by omega), show m + j + 1 - (j + 1) = m by omega]
        exact hBi.symm
      · rw [if_neg (by omega), if_neg (by omega),
          show m + i + 1 - j = (m + i - j) + 1 by omega,
          show m + i + 1 - (j + 1) = m + i - j by omega]
        exact (h.1 _ (by omega)).symm
  · simp only [c] at hab
    split_ifs at hab with h1 h2 h2
    · exact h.2 _ (by omega) _ (by omega) hab
    · have := h.2 _ (by omega) _ (by omega) hab; omega
    · have := h.2 _ (by omega) _ (by omega) hab; omega
    · have := h.2 _ (by omega) _ (by omega) hab; omega
  · simp only [c]
    rw [if_neg (by omega), if_pos (Nat.zero_le _), show m + i + 1 - m = i + 1 by omega]
    exact hAi.symm

lemma extend {G : SimpleGraph V} {m : ℕ} {c : ℕ → V} (h : IsP G m c)
    (hcl : G.Adj (c m) (c 0)) (hlt : m + 1 < Fintype.card V)
    (hconn : ∀ u v : V, G.Reachable u v) : ∃ g, IsP G (m + 1) g := by
  let S : Set V := {v | ∃ j ≤ m, c j = v}
  have hv : ∃ v, v ∉ S := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset V) ⊆ (Finset.range (m + 1)).image c := by
      intro v _
      obtain ⟨j, hj, rfl⟩ := hcon v
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    simp at this
    omega
  obtain ⟨v, hvS⟩ := hv
  obtain ⟨p⟩ := hconn (c 0) v
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ⟨0, Nat.zero_le _, rfl⟩ hvS
  obtain ⟨k, hk, hck⟩ := hd1
  have hadj : G.Adj (c k) d.snd := hck ▸ d.adj
  set y := d.snd with hy
  have hyc : ∀ j ≤ m, c j ≠ y := fun j hj e => hd2 ⟨j, hj, e⟩
  let g : ℕ → V := fun j => if j = 0 then y else if j ≤ m + 1 - k then c (k + j - 1)
    else c (j + k - m - 2)
  refine ⟨g, fun j hj => ?_, fun a ha b hb hab => ?_⟩
  · simp only [g]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [if_pos rfl, if_neg (show (0:ℕ) + 1 ≠ 0 by omega),
        if_pos (show 0 + 1 ≤ m + 1 - k by omega), show k + (0 + 1) - 1 = k by omega]
      exact hadj.symm
    · rw [if_neg (show j ≠ 0 by omega), if_neg (show j + 1 ≠ 0 by omega)]
      by_cases h1 : j + 1 ≤ m + 1 - k
      · rw [if_pos (show j ≤ m + 1 - k by omega), if_pos h1,
          show k + (j + 1) - 1 = (k + j - 1) + 1 by omega]
        exact h.1 _ (by omega)
      · by_cases h2 : j = m + 1 - k
        · rw [if_pos (show j ≤ m + 1 - k by omega), if_neg h1, show k + j - 1 = m by omega,
            show j + 1 + k - m - 2 = 0 by omega]
          exact hcl
        · rw [if_neg (show ¬ j ≤ m + 1 - k by omega), if_neg h1,
            show j + 1 + k - m - 2 = (j + k - m - 2) + 1 by omega]
          exact h.1 _ (by omega)
  · simp only [g] at hab
    split_ifs at hab <;>
      first
      | omega
      | exact absurd hab.symm (hyc _ (by omega))
      | exact absurd hab (hyc _ (by omega))
      | (have := h.2 _ (by omega) _ (by omega) hab; omega)

omit [DecidableEq V] in
lemma reach_of_conn{G : SimpleGraph V} (hG : IsKConnected G 1) (u v : V) : G.Reachable u v := by
  have hc := hG.2 ∅ (by simp)
  have hu : u ∈ ((∅ : Finset V) : Set V)ᶜ := by simp
  have hv : v ∈ ((∅ : Finset V) : Set V)ᶜ := by simp
  exact (hc.preconnected ⟨u, hu⟩ ⟨v, hv⟩).map (Embedding.induce _).toHom

omit [DecidableEq V] in
lemma bdd_cycles(G : SimpleGraph V) : BddAbove G.cycleLengths := by
  refine ⟨Fintype.card V, fun k ⟨a, w, hw, hk⟩ => ?_⟩
  have h1 := hw.support_nodup.length_le_card
  have h2 := w.length_support
  rw [List.length_tail, h2] at h1
  omega

theorem bondy_conjecture.variants.one {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsKConnected G 1) (hd : ((Fintype.card V : ℝ)) / 2 ≤ G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v) (hP : P.IsPath) :
    P.support.length + 1 ≤ 1 := by
  exfalso
  have hu : (u : V) ∉ C.support := u.2
  -- C has ≥ 3 vertices, none equal to u
  have hCn : C.length + 1 ≤ Fintype.card V := by
    have hnd : ((u : V) :: C.support.tail).Nodup := by
      refine List.nodup_cons.2 ⟨fun hm => hu (List.mem_of_mem_tail hm), hC.support_nodup⟩
    have := hnd.length_le_card
    rw [List.length_cons, List.length_tail, C.length_support] at this
    omega
  have h3 := hC.three_le_length
  have hδ : ∀ w, Fintype.card V ≤ 2 * G.degree w := by
    intro w
    have h1 : (G.minDegree : ℝ) ≤ G.degree w := by exact_mod_cast G.minDegree_le_degree w
    have : (Fintype.card V : ℝ) ≤ 2 * G.degree w := by linarith
    exact_mod_cast this
  have hconn := reach_of_conn hG
  have : Nonempty V := ⟨a⟩
  obtain ⟨m, g, hg, hmax⟩ := exists_max G
  obtain ⟨c, hc, hcl, hm2⟩ := cycle_of_max hg hmax hδ (by omega)
  have hmn : m + 1 = Fintype.card V := by
    have := len_bound hg
    by_contra hne
    obtain ⟨g', hg'⟩ := extend hc hcl (by omega) hconn
    have := hmax _ _ hg'
    omega
  -- build the Hamiltonian cycle
  let l : List V := (List.range (m + 1)).map c
  have hne : l ≠ [] := by simp [l]
  have hch : l.IsChain G.Adj := by
    simp only [l]
    rw [List.isChain_map, List.isChain_range_succ]
    exact fun i hi => hc.1 i hi
  have hnd : l.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    rw [List.mem_range] at ha hb
    exact hc.2 a (by omega) b (by omega) hab
  have hhead : l.head hne = c 0 := by simp [l]
  have hlast : l.getLast hne = c m := by simp [l, List.getLast_map, List.getLast_range]
  let p := Walk.ofSupport l hne hch
  have hadj : G.Adj (l.getLast hne) (l.head hne) := by rw [hhead, hlast]; exact hcl
  let W := Walk.cons hadj p
  have hpP : p.IsPath := by
    rw [Walk.isPath_def, Walk.support_ofSupport]
    exact hnd
  have hplen : p.length = m := by
    simp only [p, Walk.length_ofSupport, l, List.length_map, List.length_range]
    omega
  have hW : W.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp only [W, Walk.tail_cons, Walk.length_cons]
    exact ⟨(Walk.isPath_copy _ _ _).2 hpP, by omega⟩
  have hmem : Fintype.card V ∈ G.cycleLengths :=
    ⟨_, W, hW, by simp only [W, Walk.length_cons]; omega⟩
  have := le_csSup (bdd_cycles G) hmem
  rw [← circumference, ← hlong] at this
  omega

end Arxiv.«2606.03696»

#print axioms Arxiv.«2606.03696».bondy_conjecture.variants.one
