import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Erdos934

def HasFarEdges {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ u v w x : V, G.Adj u v ∧ G.Adj w x ∧
    ∀ a ∈ ({u, v} : Set V), ∀ b ∈ ({w, x} : Set V), (t : ℕ∞) ≤ G.edist a b

noncomputable def h (t d : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G t}

namespace H1

variable {V : Type*} (G : SimpleGraph V)

lemma one_le_edist {a b : V} : (1 : ℕ∞) ≤ G.edist a b ↔ a ≠ b := by
  rw [Order.one_le_iff_ne_zero, ne_eq, SimpleGraph.edist_eq_zero_iff]

lemma far_iff : HasFarEdges G 1 ↔ ∃ u v w x, G.Adj u v ∧ G.Adj w x ∧
    u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x := by
  unfold HasFarEdges
  simp only [Nat.cast_one, one_le_edist]
  constructor
  · rintro ⟨u, v, w, x, h1, h2, h⟩
    exact ⟨u, v, w, x, h1, h2, h u (by simp) w (by simp), h u (by simp) x (by simp),
      h v (by simp) w (by simp), h v (by simp) x (by simp)⟩
  · rintro ⟨u, v, w, x, h1, h2, a, b, c, e⟩
    refine ⟨u, v, w, x, h1, h2, ?_⟩
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> assumption

lemma card_star [Finite V] (u : V) (hu : ∀ a b, G.Adj a b → a = u ∨ b = u) :
    G.edgeSet.ncard ≤ (G.neighborSet u).ncard := by
  have hsub : G.edgeSet ⊆ (fun w => s(u, w)) '' G.neighborSet u := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases hu a b he with rfl | rfl
      · exact ⟨b, he, rfl⟩
      · exact ⟨a, he.symm, Sym2.eq_swap⟩
  exact (Set.ncard_le_ncard hsub).trans Set.ncard_image_le

lemma card_tri [Finite V] {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (I : ∀ a b c e, G.Adj a b → G.Adj c e → a = c ∨ a = e ∨ b = c ∨ b = e) :
    G.edgeSet.ncard ≤ 3 := by
  have nuv := G.ne_of_adj huv
  have nuw := G.ne_of_adj huw
  have nvw := G.ne_of_adj hvw
  have hsub : G.edgeSet ⊆ {s(u, v), s(u, w), s(v, w)} := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      have h1 := I a b u v he huv
      have h2 := I a b u w he huw
      have h3 := I a b v w he hvw
      have nab := G.ne_of_adj he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
      rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
        rcases h3 with h3 | h3 | h3 | h3 <;> subst_vars <;> simp_all
  have e1 := Set.ncard_le_ncard hsub
  have e2 := Set.ncard_insert_le (s(u, v)) ({s(u, w), s(v, w)} : Set (Sym2 V))
  have e3 := Set.ncard_insert_le (s(u, w)) ({s(v, w)} : Set (Sym2 V))
  rw [Set.ncard_singleton] at e3
  omega

lemma upper {n d : ℕ} (hd : d ≠ 2) (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d) (hE : d + 1 ≤ G.edgeSet.ncard) :
    HasFarEdges G 1 := by
  rw [far_iff]
  by_contra hno
  have I : ∀ a b c e, G.Adj a b → G.Adj c e → a = c ∨ a = e ∨ b = c ∨ b = e := by
    intro a b c e h1 h2
    by_contra hc
    simp only [not_or] at hc
    exact hno ⟨a, b, c, e, h1, h2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  obtain ⟨e0, he0⟩ := Set.nonempty_of_ncard_ne_zero (s := G.edgeSet) (by omega)
  induction e0 using Sym2.ind with
  | h u v =>
  rw [SimpleGraph.mem_edgeSet] at he0
  by_cases hA : ∀ a b, G.Adj a b → a = u ∨ b = u
  · have := card_star G u hA; have := hdeg u; omega
  by_cases hB : ∀ a b, G.Adj a b → a = v ∨ b = v
  · have := card_star G v hB; have := hdeg v; omega
  push Not at hA hB
  obtain ⟨a, b, hab, hau, hbu⟩ := hA
  obtain ⟨a', b', hab', hav, hbv⟩ := hB
  obtain ⟨w, hvw, hwu⟩ : ∃ w, G.Adj v w ∧ w ≠ u := by
    rcases I a b u v hab he0 with h | h | h | h
    · exact absurd h hau
    · exact ⟨b, by rw [← h]; exact hab, hbu⟩
    · exact absurd h hbu
    · exact ⟨a, by rw [← h]; exact hab.symm, hau⟩
  obtain ⟨x, hux, hxv⟩ : ∃ x, G.Adj u x ∧ x ≠ v := by
    rcases I a' b' u v hab' he0 with h | h | h | h
    · exact ⟨b', by rw [← h]; exact hab', hbv⟩
    · exact absurd h hav
    · exact ⟨a', by rw [← h]; exact hab'.symm, hav⟩
    · exact absurd h hbv
  have hwx : w = x := by
    rcases I v w u x hvw hux with h | h | h | h
    · exact absurd h (G.ne_of_adj he0).symm
    · exact absurd h.symm hxv
    · exact absurd h hwu
    · exact h
  subst hwx
  have h3 := card_tri G he0 hux hvw I
  have hdu : 2 ≤ (G.neighborSet u).ncard := by
    rw [← Set.ncard_pair (G.ne_of_adj hvw)]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact he0
    · exact hux
  have := hdeg u
  omega

def star (d : ℕ) : SimpleGraph (Fin (d + 1)) := SimpleGraph.fromRel (fun i _ => i = 0)

lemma star_adj {d : ℕ} {i j : Fin (d + 1)} : (star d).Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0) := by
  simp [star]

lemma star_deg (d : ℕ) : ∀ v, ((star d).neighborSet v).ncard ≤ d := by
  intro v
  by_cases hv : v = 0
  · subst hv
    have hsub : (star d).neighborSet 0 ⊆
        (↑((Finset.univ : Finset (Fin (d + 1))).erase 0) : Set (Fin (d + 1))) := by
      intro j hj
      rw [SimpleGraph.mem_neighborSet, star_adj] at hj
      simp [hj.1.symm]
    calc _ ≤ (↑((Finset.univ : Finset (Fin (d + 1))).erase 0) : Set (Fin (d + 1))).ncard :=
          Set.ncard_le_ncard hsub
      _ = d := by rw [Set.ncard_coe_finset]; simp
  · have hsub : (star d).neighborSet v ⊆ {0} := by
      intro j hj
      rw [SimpleGraph.mem_neighborSet, star_adj] at hj
      rw [Set.mem_singleton_iff]
      rcases hj.2 with h | h
      · exact absurd h hv
      · exact h
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at h1
    have : v.val ≠ 0 := by
      intro h; apply hv; ext; simpa using h
    have := v.isLt
    omega

lemma star_edges (d : ℕ) : d ≤ (star d).edgeSet.ncard := by
  have hsub : (↑(((Finset.univ : Finset (Fin (d + 1))).erase 0).image (fun j => s(0, j))) :
      Set (Sym2 (Fin (d + 1)))) ⊆ (star d).edgeSet := by
    intro e he
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase] at he
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := he
    rw [SimpleGraph.mem_edgeSet, star_adj]
    exact ⟨Ne.symm hj, Or.inl rfl⟩
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun a b h => by
    have h' : a = b ∨ (0 = b ∧ a = 0) := by simpa using h
    rcases h' with h' | ⟨h1, h2⟩
    · exact h'
    · rw [h2, h1])]
    at this
  simpa using this

lemma lower {d m : ℕ} (hm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G 1) :
    d + 1 ≤ m := by
  by_contra hlt
  have hf := hm (d + 1) (star d) (star_deg d) (by have := star_edges d; omega)
  rw [far_iff] at hf
  obtain ⟨u, v, w, x, h1, h2, a, b, c, e⟩ := hf
  rw [star_adj] at h1 h2
  rcases h1.2 with rfl | rfl <;> rcases h2.2 with rfl | rfl <;> simp_all

end H1

theorem erdos_934.variants.h_one : ∀ d : ℕ, d ≠ 2 → h 1 d = d + 1 := by
  intro d hd
  have mem : d + 1 ∈ {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G 1} :=
    fun n G hdeg hE => H1.upper hd G hdeg hE
  unfold h
  exact le_antisymm (Nat.sInf_le mem) (le_csInf ⟨_, mem⟩ (fun m hm => H1.lower hm))

end Erdos934

#print axioms Erdos934.erdos_934.variants.h_one
