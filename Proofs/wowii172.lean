import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean, Eccentricity.lean, VertexDistance.lean, Connectivity.lean). -/
namespace SimpleGraph

section BFS
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} {s t : Finset V} {u v w : V}

variable (G s) in
def bfsStep : Finset V := {w | w ∈ s ∨ ∃ v ∈ s, G.Adj v w}

lemma mem_bfsStep : w ∈ G.bfsStep s ↔ w ∈ s ∨ ∃ v ∈ s, G.Adj v w := by simp [bfsStep]

lemma reachable_of_mem_iterate_bfsStep (hv : v ∈ G.bfsStep^[n] {u}) : G.Reachable u v := by
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hv
    exact hv ▸ Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_bfsStep] at hv
    obtain hv | ⟨w, hw, hwv⟩ := hv
    · exact ih hv
    · exact (ih hw).trans hwv.reachable

end BFS

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

noncomputable def distMin (G : SimpleGraph α) (S : Set α) : ℕ :=
  open scoped Classical in
  let pairs := (S.toFinset ×ˢ S.toFinset).filter (fun p => p.1 ≠ p.2)
  if h : pairs.Nonempty then
    (pairs.image (fun p => G.dist p.1 p.2)).min' (Finset.Nonempty.image h _)
  else 0

def bfs_dist_aux (G : SimpleGraph α) [DecidableRel G.Adj] (target : α) : ℕ → ℕ → Finset α → ℕ
  | 0, _, _ => 0
  | fuel + 1, depth, reached =>
    if target ∈ reached then depth
    else bfs_dist_aux G target fuel (depth + 1) (G.bfsStep reached)

def computable_dist (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℕ :=
  if u = v then 0
  else bfs_dist_aux G v (Fintype.card α) 1 (G.bfsStep {u})

private lemma mem_iterate_bfsStep_dist_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ G.bfsStep^[n] {u}) : G.dist u w ≤ n := by
  induction n generalizing w with
  | zero => simp at hw; subst hw; simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [mem_bfsStep] at hw
    rcases hw with hw | ⟨a, ha_mem, hadj⟩
    · exact Nat.le_succ_of_le (ih w hw)
    · by_cases ha : a = u
      · subst ha
        exact le_trans (dist_le (.cons hadj .nil))
          (by simp [Walk.length_cons])
      · by_cases hd : G.dist u a = 0
        · rw [dist_eq_zero_iff_eq_or_not_reachable] at hd
          rcases hd with rfl | hd
          · exact absurd rfl ha
          · have : ¬G.Reachable u w := fun hr =>
              hd (hr.elim (fun p => (p.append (.cons hadj.symm .nil)).reachable))
            rw [dist_eq_zero_of_not_reachable this]; omega
        · obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero hd
          have ha_dist := ih a ha_mem
          exact le_trans (dist_le (p.append (.cons hadj .nil)))
            (by simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hp]; omega)

private lemma dist_le_mem_iterate_bfsStep (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hdist : G.dist u w ≤ n) (hreach : w = u ∨ G.Reachable u w) :
    w ∈ G.bfsStep^[n] {u} := by
  induction n generalizing w with
  | zero =>
    rcases hreach with rfl | hr
    · exact Finset.mem_singleton_self _
    · have h0 := Nat.le_zero.mp hdist
      rw [dist_eq_zero_iff_eq_or_not_reachable] at h0
      rcases h0 with h0 | h0
      · subst h0; exact Finset.mem_singleton_self _
      · exact absurd hr h0
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    simp only [mem_bfsStep]
    by_cases hle : G.dist u w ≤ n
    · left; exact ih w hle hreach
    · right
      have hdist_eq : G.dist u w = n + 1 := by omega
      obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist u w ≠ 0)
      have hlen : p.length = n + 1 := by omega
      refine ⟨p.getVert n, ?_, ?_⟩
      · exact ih _ (le_trans (dist_le (p.take n))
          (by rw [Walk.take_length]; omega)) (Or.inr (p.take n).reachable)
      · have := p.adj_getVert_succ (show n < p.length from by omega)
        rwa [show n + 1 = p.length from by omega, p.getVert_length] at this

theorem dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) :
    G.dist u v = computable_dist G u v := by
  unfold computable_dist
  split_ifs with h
  · subst h; simp [dist_self]
  · symm
    suffices hsuff : ∀ (fuel depth : ℕ) (reached : Finset α),
        (∀ w, w ∈ reached ↔ w ∈ G.bfsStep^[depth] {u}) →
        (∀ d, d < depth → v ∉ G.bfsStep^[d] {u}) →
        fuel + depth ≥ Fintype.card α + 1 →
        G.bfs_dist_aux v fuel depth reached = G.dist u v by
      exact hsuff (Fintype.card α) 1 (G.bfsStep {u})
        (fun w => by simp)
        (fun d hd => by
          have := Nat.lt_of_lt_of_le hd (Nat.le_refl 1)
          interval_cases d; simp [Finset.mem_singleton]; exact Ne.symm h)
        (by omega)
    intro fuel
    induction fuel with
    | zero =>
      intro depth reached h_inv h_not_found h_fuel
      simp [bfs_dist_aux]
      symm; rw [dist_eq_zero_iff_eq_or_not_reachable]
      right; intro hr
      have hpos := hr.pos_dist_of_ne h
      obtain ⟨p, hp_path, hp_len⟩ := hr.exists_path_of_dist
      have : G.dist u v < depth := by
        calc G.dist u v = p.length := hp_len.symm
          _ < Fintype.card α := hp_path.length_lt
          _ < depth := by omega
      exact h_not_found (G.dist u v) this
        (dist_le_mem_iterate_bfsStep G u v _ (le_refl _) (Or.inr hr))
    | succ fuel ih =>
      intro depth reached h_inv h_not_found h_fuel
      simp only [bfs_dist_aux]
      split_ifs with hv
      · have hle := mem_iterate_bfsStep_dist_le G u v depth ((h_inv v).mp hv)
        by_contra hne
        have hlt : G.dist u v < depth := by omega
        have hreach : G.Reachable u v := G.reachable_of_mem_iterate_bfsStep ((h_inv v).mp hv)
        exact h_not_found (G.dist u v) hlt
          (dist_le_mem_iterate_bfsStep G u v _ le_rfl (Or.inr hreach))
      · have h_inv' : ∀ w, w ∈ G.bfsStep reached ↔
            w ∈ G.bfsStep^[depth + 1] {u} := by
          intro w
          have heq : G.bfsStep reached = G.bfsStep (G.bfsStep^[depth] {u}) := by
            ext x; simp only [mem_bfsStep, h_inv]
          rw [heq, Function.iterate_succ', Function.comp]
        exact ih (depth + 1) (G.bfsStep reached) h_inv'
          (fun d hd => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
            · exact h_not_found d (by omega)
            · subst hd; rwa [h_inv] at hv)
          (by omega)

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture172

open SimpleGraph Finset

/-- The maximum original-graph degree among the peripheral vertices. -/
noncomputable def peripheryMaxDegree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (Finset.univ.filter fun v => v ∈ maxEccentricityVertices G).sup
    fun v => (G.neighborFinset v).card

/-- The maximum-degree vertices of `G²`, presented using finite graph distance. -/
def squareMaximumDegreeVertices {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  let squareDegree (v : V) :=
    (Finset.univ.filter fun w => v ≠ w ∧ computable_dist G v w ≤ 2).card
  {v | squareDegree v = Finset.univ.sup squareDegree}

/-! ### General lemmas -/

lemma dist_le_two_iff {V : Type*} {G : SimpleGraph V} (hc : G.Connected) {v w : V}
    (hne : v ≠ w) : G.dist v w ≤ 2 ↔ G.Adj v w ∨ ∃ x, G.Adj v x ∧ G.Adj x w := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (hc.preconnected v w).exists_walk_length_eq_dist
    cases p with
    | nil => exact absurd rfl hne
    | cons h1 q =>
      cases q with
      | nil => exact Or.inl h1
      | cons h2 q2 =>
        cases q2 with
        | nil => exact Or.inr ⟨_, h1, h2⟩
        | cons h3 q3 =>
          simp only [Walk.length_cons] at hp
          omega
  · rintro (h | ⟨x, h1, h2⟩)
    · exact (dist_le (Walk.cons h Walk.nil)).trans (by simp)
    · exact (dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

lemma le_distMin {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Set V)
    (k : ℕ) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → k ≤ G.dist x y) : k ≤ distMin G S := by
  classical
  unfold distMin
  dsimp only
  split_ifs with hne
  · apply Finset.le_min'
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hz
    rw [Finset.mem_filter, Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset] at hxy
    exact h x hxy.1.1 y hxy.1.2 hxy.2
  · exfalso
    apply hne
    refine ⟨(a, b), ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset]
    exact ⟨⟨ha, hb⟩, hab⟩

/-- A connected spanning subgraph has an edge across every nontrivial cut. -/
lemma cut_edge {V : Type*} [Fintype V] {G : SimpleGraph V} (T : G.Subgraph)
    (hspan : T.IsSpanning) (hconn : T.coe.Connected) (S : Set V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : ∃ x y, T.Adj x y ∧ x ∈ S ∧ y ∉ S := by
  let f : T.coe →g T.spanningCoe := ⟨fun x => x.1, fun {x y} h => h⟩
  have hr : T.coe.Reachable ⟨a, hspan a⟩ ⟨b, hspan b⟩ := hconn.preconnected _ _
  have p := (hr.map f).some
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  exact ⟨d.fst, d.snd, d.adj, hd1, hd2⟩

/-! ### The graph `D₉`: path 0–1–…–9, triangles {0,10,11} and {9,12,13} -/

def adjF (i j : Fin 14) : Prop :=
  (i.val + 1 = j.val ∧ j.val ≤ 9) ∨ (j.val + 1 = i.val ∧ i.val ≤ 9) ∨
  (i.val = 0 ∧ (j.val = 10 ∨ j.val = 11)) ∨ (j.val = 0 ∧ (i.val = 10 ∨ i.val = 11)) ∨
  (i.val = 9 ∧ (j.val = 12 ∨ j.val = 13)) ∨ (j.val = 9 ∧ (i.val = 12 ∨ i.val = 13)) ∨
  ((i.val = 10 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 10) ∨
    (i.val = 12 ∧ j.val = 13) ∨ (i.val = 13 ∧ j.val = 12))

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_symm (i j : Fin 14) (h : adjF i j) : adjF j i := by
  unfold adjF at *
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))); omega

lemma adjF_irrefl (i : Fin 14) : ¬ adjF i i := by
  unfold adjF; omega

def G : SimpleGraph (Fin 14) where
  Adj := adjF
  symm := ⟨fun x y h => adjF_symm x y h⟩
  loopless := ⟨fun x h => adjF_irrefl x h⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma connected : G.Connected := by
  have A : ∀ i j : Fin 14, adjF i j → G.Reachable i j := fun i j h => Adj.reachable h
  have hp : ∀ n : ℕ, (hn : n ≤ 9) → G.Reachable 0 ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Reachable.refl _
    | succ n ih =>
      intro hn
      exact (ih (by omega)).trans (A _ _ (Or.inl ⟨rfl, hn⟩))
  have hR : ∀ i : Fin 14, G.Reachable 0 i := by
    intro i
    by_cases h9 : i.val ≤ 9
    · exact hp i.val h9
    · have r9 := hp 9 le_rfl
      have h4 : i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 := by omega
      rcases h4 with e | e | e | e
      · exact A 0 i (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl e⟩)))
      · exact A 0 i (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr e⟩)))
      · exact r9.trans (A _ i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl e⟩))))))
      · exact r9.trans (A _ i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr e⟩))))))
  rw [connected_iff]
  exact ⟨fun u v => (hR u).symm.trans (hR v), ⟨0⟩⟩

/-! ### `Ls ≤ 4` -/

lemma two_nb (T : G.Subgraph) (hspan : T.IsSpanning) (hconn : T.coe.Connected)
    (v : Fin 14) (hv : v.val ≤ 9) : ∃ x y, x ≠ y ∧ T.Adj v x ∧ T.Adj v y := by
  -- every path edge is in `T`
  have pe : ∀ i : ℕ, (hi : i < 9) → T.Adj ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
    intro i hi
    obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
      {z | z.val ≤ i ∨ z.val = 10 ∨ z.val = 11} ⟨0, by omega⟩ ⟨i + 1, by omega⟩
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega)
    have hg : adjF x y := T.adj_sub hxy
    simp only [Set.mem_setOf_eq] at hx hy
    have e1 : x.val = i := by unfold adjF at hg; omega
    have e2 : y.val = i + 1 := by unfold adjF at hg; omega
    have ex : x = ⟨i, by omega⟩ := Fin.ext e1
    have ey : y = ⟨i + 1, by omega⟩ := Fin.ext e2
    rw [ex, ey] at hxy
    exact hxy
  by_cases h0 : v.val = 0
  · obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
      {z | z.val = 10 ∨ z.val = 11} ⟨10, by omega⟩ ⟨0, by omega⟩
      (Or.inl rfl) (by rintro (h | h) <;> simp at h)
    have hg : adjF x y := T.adj_sub hxy
    simp only [Set.mem_setOf_eq] at hx hy
    have ey : y.val = 0 := by unfold adjF at hg; omega
    have ev : v = y := Fin.ext (h0.trans ey.symm)
    refine ⟨x, ⟨1, by omega⟩, ?_, ?_, ?_⟩
    · intro e; rw [e] at hx; simp at hx
    · rw [ev]; exact hxy.symm
    · have := pe 0 (by omega)
      have ev0 : v = ⟨0, by omega⟩ := Fin.ext h0
      rw [ev0]; exact this
  by_cases h9 : v.val = 9
  · obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
      {z | z.val = 12 ∨ z.val = 13} ⟨12, by omega⟩ ⟨9, by omega⟩
      (Or.inl rfl) (by rintro (h | h) <;> simp at h)
    have hg : adjF x y := T.adj_sub hxy
    simp only [Set.mem_setOf_eq] at hx hy
    have ey : y.val = 9 := by unfold adjF at hg; omega
    have ev : v = y := Fin.ext (h9.trans ey.symm)
    refine ⟨x, ⟨8, by omega⟩, ?_, ?_, ?_⟩
    · intro e; rw [e] at hx; simp at hx
    · rw [ev]; exact hxy.symm
    · have := pe 8 (by omega)
      have ev0 : v = ⟨9, by omega⟩ := Fin.ext h9
      rw [ev0]; exact this.symm
  · refine ⟨⟨v.val - 1, by omega⟩, ⟨v.val + 1, by omega⟩, ?_, ?_, ?_⟩
    · intro e; have h' := Fin.mk.inj_iff.1 e; omega
    · have := pe (v.val - 1) (by omega)
      have ev : (⟨v.val - 1 + 1, by omega⟩ : Fin 14) = v := Fin.ext (by simp; omega)
      rw [ev] at this
      exact this.symm
    · exact pe v.val (by omega)

lemma Ls_le : Ls G ≤ 4 := by
  unfold Ls
  apply Real.sSup_le _ (by norm_num)
  rintro _ ⟨T, ⟨hspan, htree⟩, rfl⟩
  beta_reduce
  have hsub : ∀ (i1 : Fintype ↑T.verts) (i2 : ∀ v, Fintype ↑(T.neighborSet v)),
      (@Set.toFinset _ T.verts i1).filter (fun v => @Subgraph.degree _ _ T v (i2 v) = 1) ⊆
        ({10, 11, 12, 13} : Finset (Fin 14)) := by
    intro i1 i2 v hv
    rw [Finset.mem_filter] at hv
    have hu : ∃! u, T.Adj v u := Subgraph.degree_eq_one_iff_existsUnique_adj.mp hv.2
    by_contra hn
    have h9 : v.val ≤ 9 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      by_contra h
      apply hn
      have : v.val = 10 ∨ v.val = 11 ∨ v.val = 12 ∨ v.val = 13 := by omega
      rcases this with e | e | e | e
      · left; exact Fin.ext e
      · right; left; exact Fin.ext e
      · right; right; left; exact Fin.ext e
      · right; right; right; exact Fin.ext e
    obtain ⟨x, y, hxy, hx, hy⟩ := two_nb T hspan htree.connected v h9
    obtain ⟨u, -, hu2⟩ := hu
    exact hxy ((hu2 x hx).trans (hu2 y hy).symm)
  have h4 : ({10, 11, 12, 13} : Finset (Fin 14)).card = 4 := by decide
  have key : ∀ (i1 : Fintype ↑T.verts) (i2 : ∀ v, Fintype ↑(T.neighborSet v)),
      ((@Set.toFinset _ T.verts i1).filter
        (fun v => @Subgraph.degree _ _ T v (i2 v) = 1)).card ≤ 4 :=
    fun i1 i2 => (Finset.card_le_card (hsub i1 i2)).trans h4.le
  refine le_trans (Nat.cast_le.mpr (key _ _)) ?_
  norm_num

/-! ### `peripheryMaxDegree ≥ 2` -/

lemma deg2 : ∀ v : Fin 14, ∃ x y, x ≠ y ∧ adjF v x ∧ adjF v y := by decide

lemma pmd_ge : 2 ≤ peripheryMaxDegree G := by
  classical
  obtain ⟨v, hv⟩ := G.exists_eccent_eq_ediam_of_finite
  obtain ⟨x, y, hxy, hx, hy⟩ := deg2 v
  unfold peripheryMaxDegree
  have hmem : v ∈ (Finset.univ.filter fun v => v ∈ maxEccentricityVertices G) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩
  refine le_trans ?_ (Finset.le_sup hmem)
  exact Finset.one_lt_card.2 ⟨x, (mem_neighborFinset _ _ _).2 hx, y,
    (mem_neighborFinset _ _ _).2 hy, hxy⟩

/-! ### The square-degree maximisers are `1` and `8` -/

def sq2 (v w : Fin 14) : Prop := v ≠ w ∧ (adjF v w ∨ ∃ x, adjF v x ∧ adjF x w)

instance : DecidableRel sq2 := fun v w => by unfold sq2; infer_instance

lemma sqd_eq (v : Fin 14) :
    (Finset.univ.filter fun w => v ≠ w ∧ computable_dist G v w ≤ 2) =
      Finset.univ.filter (sq2 v) := by
  apply Finset.filter_congr
  intro w _
  unfold sq2
  rw [← dist_eq_computable]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (dist_le_two_iff connected h1).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (dist_le_two_iff connected h1).2 h2⟩

set_option maxRecDepth 100000 in
lemma sq_le : ∀ v : Fin 14, (Finset.univ.filter (sq2 v)).card ≤ 5 := by decide

set_option maxRecDepth 100000 in
lemma sq_eq5 : ∀ v : Fin 14, (Finset.univ.filter (sq2 v)).card = 5 ↔ (v = 1 ∨ v = 8) := by
  decide

lemma M_eq : squareMaximumDegreeVertices G = {1, 8} := by
  unfold squareMaximumDegreeVertices
  simp only [sqd_eq]
  have hsup : (Finset.univ.sup fun v => (Finset.univ.filter (sq2 v)).card) = 5 := by
    apply le_antisymm
    · exact Finset.sup_le fun v _ => sq_le v
    · exact le_trans ((sq_eq5 1).2 (Or.inl rfl)).ge (Finset.le_sup (f := fun v =>
        (Finset.univ.filter (sq2 v)).card) (Finset.mem_univ 1))
  rw [hsup]
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact sq_eq5 v

/-! ### `distMin ≥ 7` -/

def pot (x : Fin 14) : ℕ := if x.val ≤ 9 then x.val else if x.val ≤ 11 then 0 else 9

lemma pot_adj (x y : Fin 14) (h : adjF x y) : pot y ≤ pot x + 1 := by
  unfold pot; unfold adjF at h; split_ifs <;> omega

lemma pot_walk {u w : Fin 14} (p : G.Walk u w) : pot w ≤ pot u + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [Walk.length_cons]
    have := pot_adj _ _ h
    omega

lemma dist_ge (u w : Fin 14) : pot w - pot u ≤ G.dist u w := by
  obtain ⟨p, hp⟩ := (connected.preconnected u w).exists_walk_length_eq_dist
  have := pot_walk p
  omega

lemma distMin_ge : 7 ≤ distMin G (squareMaximumDegreeVertices G) := by
  rw [M_eq]
  apply le_distMin G _ 7 1 8 (by simp) (by simp) (by decide)
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact (dist_ge 1 8).trans' (by decide)
  · rw [dist_comm]; exact (dist_ge 1 8).trans' (by decide)
  · exact absurd rfl hxy

theorem conjecture172 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G ≥ (-1 : ℝ) + peripheryMaxDegree G +
          distMin G (squareMaximumDegreeVertices G) := by
  intro h
  have h1 := h (Fin 14) G connected
  have h2 := Ls_le
  have h3 : (2 : ℝ) ≤ peripheryMaxDegree G := by exact_mod_cast pmd_ge
  have h4 : (7 : ℝ) ≤ distMin G (squareMaximumDegreeVertices G) := by exact_mod_cast distMin_ge
  linarith

end WrittenOnTheWallII.GraphConjecture172

#print axioms WrittenOnTheWallII.GraphConjecture172.conjecture172
