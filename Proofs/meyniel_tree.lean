import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.Lattice.Nat

namespace MeynielConjecture

variable {V : Type*}

def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

lemma not_copsCatchWithin_zero (G : SimpleGraph V) (m : ℕ) (c : Fin 0 → V) (r : V) :
    ¬CopsCatchWithin G 0 m c r := by
  induction m generalizing c r with
  | zero =>
    rintro ⟨i, -⟩
    exact i.elim0
  | succ m ih =>
    rintro (⟨i, -⟩ | ⟨c', -, ⟨i, -⟩ | h⟩)
    · exact i.elim0
    · exact i.elim0
    · exact ih c' r (h r (Or.inl rfl))

lemma not_copsWin_zero [Nonempty V] (G : SimpleGraph V) : ¬CopsWin G 0 := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hc (Classical.arbitrary V)
  exact not_copsCatchWithin_zero G m c _ hm

lemma copsWin_card [Fintype V] (G : SimpleGraph V) : CopsWin G (Fintype.card V) :=
  ⟨(Fintype.equivFin V).symm, fun r => ⟨0, ⟨Fintype.equivFin V r, by simp⟩⟩⟩

lemma one_le_copNumber [Fintype V] [Nonempty V] (G : SimpleGraph V) : 1 ≤ copNumber G := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · exact not_copsWin_zero G h
  · exact Set.eq_empty_iff_forall_notMem.mp h _ (copsWin_card G)

/-- Distances are smaller than the number of vertices. -/
lemma dist_lt_card [Fintype V] {G : SimpleGraph V} (hc : G.Connected) (u v : V) :
    G.dist u v < Fintype.card V := by
  obtain ⟨p, hp, hl⟩ := hc.exists_path_of_dist u v
  exact hl ▸ hp.length_lt

/-- The cop can step one vertex closer to the robber. -/
lemma step_closer {G : SimpleGraph V} (hc : G.Connected) {c r : V} (hcr : c ≠ r) :
    ∃ c', G.Adj c c' ∧ G.dist c' r + 1 = G.dist c r := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist c r
  cases p with
  | nil => exact absurd rfl hcr
  | @cons _ y _ h p' =>
    refine ⟨_, h, ?_⟩
    have h1 := G.dist_le p'
    have h2 := hc.dist_triangle (u := c) (v := y) (w := r)
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h2
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Tree lemma: if `x` lies on the geodesic from `u` to `r`, `x ≠ r`, and the robber moves to
the neighbour `r'` of `r` closer to `u`, then `x` lies on the geodesic from `u` to `r'`. -/
lemma geodesic_parent {G : SimpleGraph V} (hc : G.Connected) (ha : G.IsAcyclic) {u x r r' : V}
    (hx : G.dist u r = G.dist u x + G.dist x r) (hxr : x ≠ r) (hadj : G.Adj r' r)
    (hd : G.dist u r = G.dist u r' + 1) :
    G.dist u r' = G.dist u x + G.dist x r' := by
  obtain ⟨p1, hp1⟩ := hc.exists_walk_length_eq_dist u x
  obtain ⟨p2, hp2⟩ := hc.exists_walk_length_eq_dist x r
  obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist u r'
  have e1 : (p1.append p2).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_append]; omega)
  have e2 : (q.concat hadj).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_concat]; omega)
  have heq : p1.append p2 = q.concat hadj :=
    congrArg Subtype.val ((ha.subsingleton_path u r).elim ⟨_, e1⟩ ⟨_, e2⟩)
  have hmem : x ∈ q.support := by
    have : x ∈ (p1.append p2).support :=
      (SimpleGraph.Walk.mem_support_append_iff p1 p2).2 (Or.inl p1.end_mem_support)
    rw [heq, SimpleGraph.Walk.support_concat] at this
    simp only [List.mem_append, List.mem_singleton] at this
    rcases this with h | h
    · exact h
    · exact absurd h hxr
  obtain ⟨q1, q2, hq12⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.1 hmem
  have l : q.length = q1.length + q2.length := by rw [hq12, SimpleGraph.Walk.length_append]
  have h1 := G.dist_le q1
  have h2 := G.dist_le q2
  have h3 := hc.dist_triangle (u := u) (v := x) (w := r')
  omega

/-- Main lemma: a cop on the geodesic from the root `u` to the robber catches the robber within
`m` rounds as soon as `card V ≤ dist u cop + m`. -/
lemma main [Fintype V] {G : SimpleGraph V} (hc : G.Connected) (ha : G.IsAcyclic) (u : V) :
    ∀ (m : ℕ) (c : Fin 1 → V) (r : V), G.dist u r = G.dist u (c 0) + G.dist (c 0) r →
      Fintype.card V ≤ G.dist u (c 0) + m → CopsCatchWithin G 1 m c r := by
  intro m
  induction m with
  | zero =>
    intro c r _ hn
    have := dist_lt_card hc u (c 0)
    omega
  | succ m ih =>
    intro c r hinv hn
    by_cases hcr : c 0 = r
    · exact Or.inl ⟨0, hcr⟩
    obtain ⟨x, hadj, hx⟩ := step_closer hc hcr
    have t1 := hc.dist_triangle (u := u) (v := c 0) (w := x)
    rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at t1
    have t2 := hc.dist_triangle (u := u) (v := x) (w := r)
    have hux : G.dist u x = G.dist u (c 0) + 1 := by omega
    have hinv' : G.dist u r = G.dist u x + G.dist x r := by omega
    refine Or.inr ⟨fun _ => x, fun i => ?_, ?_⟩
    · rw [Subsingleton.elim i 0]
      exact Or.inr hadj
    by_cases hxr : x = r
    · exact Or.inl ⟨0, hxr⟩
    refine Or.inr fun r' hr' => ih (fun _ => x) r' ?_
      (by show Fintype.card V ≤ G.dist u x + m; omega)
    show G.dist u r' = G.dist u x + G.dist x r'
    rcases hr' with rfl | hrr'
    · exact hinv'
    · rcases ha.dist_eq_dist_add_one_of_adj_of_reachable u hrr' (hc u r) with h | h
      · exact geodesic_parent hc ha hinv' hxr hrr'.symm h
      · have t3 := hc.dist_triangle (u := u) (v := x) (w := r')
        have t4 := hc.dist_triangle (u := x) (v := r) (w := r')
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hrr'] at t4
        omega

theorem meyniel_conjecture.variants.tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 := by
  refine le_antisymm (Nat.sInf_le ?_) (one_le_copNumber G)
  refine ⟨fun _ => Classical.arbitrary V, fun r => ⟨Fintype.card V, ?_⟩⟩
  exact main hc ha (Classical.arbitrary V) _ _ r (by simp) (by omega)

end MeynielConjecture

#print axioms MeynielConjecture.meyniel_conjecture.variants.tree
