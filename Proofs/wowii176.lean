import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
SpanningTree.lean, Eccentricity.lean, VertexDistance.lean, Connectivity.lean, Induced.lean). -/
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

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

omit [Fintype α] in
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

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

namespace WrittenOnTheWallII.GraphConjecture176

open SimpleGraph

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

/-! ### The graph `D₇`: path 0–1–…–7, triangles {0,8,9} and {7,10,11} -/

def adjF (i j : Fin 12) : Prop :=
  (i.val + 1 = j.val ∧ j.val ≤ 7) ∨ (j.val + 1 = i.val ∧ i.val ≤ 7) ∨
  (i.val = 0 ∧ (j.val = 8 ∨ j.val = 9)) ∨ (j.val = 0 ∧ (i.val = 8 ∨ i.val = 9)) ∨
  (i.val = 7 ∧ (j.val = 10 ∨ j.val = 11)) ∨ (j.val = 7 ∧ (i.val = 10 ∨ i.val = 11)) ∨
  ((i.val = 8 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨
    (i.val = 10 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 10))

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_symm (i j : Fin 12) (h : adjF i j) : adjF j i := by
  unfold adjF at *
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))); omega

lemma adjF_irrefl (i : Fin 12) : ¬ adjF i i := by
  unfold adjF; omega

def G : SimpleGraph (Fin 12) where
  Adj := adjF
  symm := ⟨fun x y h => adjF_symm x y h⟩
  loopless := ⟨fun x h => adjF_irrefl x h⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma connected : G.Connected := by
  have A : ∀ i j : Fin 12, adjF i j → G.Reachable i j := fun i j h => Adj.reachable h
  have hp : ∀ n : ℕ, (hn : n ≤ 7) → G.Reachable 0 ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Reachable.refl _
    | succ n ih =>
      intro hn
      exact (ih (by omega)).trans (A _ _ (Or.inl ⟨rfl, hn⟩))
  have hR : ∀ i : Fin 12, G.Reachable 0 i := by
    intro i
    by_cases h7 : i.val ≤ 7
    · exact hp i.val h7
    · have r7 := hp 7 le_rfl
      have h4 : i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
      rcases h4 with e | e | e | e
      · exact A 0 i (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl e⟩)))
      · exact A 0 i (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr e⟩)))
      · exact r7.trans (A _ i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl e⟩))))))
      · exact r7.trans (A _ i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr e⟩))))))
  rw [connected_iff]
  exact ⟨fun u v => (hR u).symm.trans (hR v), ⟨0⟩⟩

/-! ### `Ls ≤ 4` -/

lemma two_nb (T : G.Subgraph) (hspan : T.IsSpanning) (hconn : T.coe.Connected)
    (v : Fin 12) (hv : v.val ≤ 7) : ∃ x y, x ≠ y ∧ T.Adj v x ∧ T.Adj v y := by
  -- every path edge is in `T`
  have pe : ∀ i : ℕ, (hi : i < 7) → T.Adj ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
    intro i hi
    obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
      {z | z.val ≤ i ∨ z.val = 8 ∨ z.val = 9} ⟨0, by omega⟩ ⟨i + 1, by omega⟩
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
      {z | z.val = 8 ∨ z.val = 9} ⟨8, by omega⟩ ⟨0, by omega⟩
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
  by_cases h7 : v.val = 7
  · obtain ⟨x, y, hxy, hx, hy⟩ := cut_edge T hspan hconn
      {z | z.val = 10 ∨ z.val = 11} ⟨10, by omega⟩ ⟨7, by omega⟩
      (Or.inl rfl) (by rintro (h | h) <;> simp at h)
    have hg : adjF x y := T.adj_sub hxy
    simp only [Set.mem_setOf_eq] at hx hy
    have ey : y.val = 7 := by unfold adjF at hg; omega
    have ev : v = y := Fin.ext (h7.trans ey.symm)
    refine ⟨x, ⟨6, by omega⟩, ?_, ?_, ?_⟩
    · intro e; rw [e] at hx; simp at hx
    · rw [ev]; exact hxy.symm
    · have := pe 6 (by omega)
      have ev0 : v = ⟨7, by omega⟩ := Fin.ext h7
      rw [ev0]; exact this.symm
  · refine ⟨⟨v.val - 1, by omega⟩, ⟨v.val + 1, by omega⟩, ?_, ?_, ?_⟩
    · intro e; have h' := Fin.mk.inj_iff.1 e; omega
    · have := pe (v.val - 1) (by omega)
      have ev : (⟨v.val - 1 + 1, by omega⟩ : Fin 12) = v := Fin.ext (by simp; omega)
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
        ({8, 9, 10, 11} : Finset (Fin 12)) := by
    intro i1 i2 v hv
    rw [Finset.mem_filter] at hv
    have hu : ∃! u, T.Adj v u := Subgraph.degree_eq_one_iff_existsUnique_adj.mp hv.2
    by_contra hn
    have h7 : v.val ≤ 7 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      by_contra h
      apply hn
      have : v.val = 8 ∨ v.val = 9 ∨ v.val = 10 ∨ v.val = 11 := by omega
      rcases this with e | e | e | e
      · left; exact Fin.ext e
      · right; left; exact Fin.ext e
      · right; right; left; exact Fin.ext e
      · right; right; right; exact Fin.ext e
    obtain ⟨x, y, hxy, hx, hy⟩ := two_nb T hspan htree.connected v h7
    obtain ⟨u, -, hu2⟩ := hu
    exact hxy ((hu2 x hx).trans (hu2 y hy).symm)
  have h4 : ({8, 9, 10, 11} : Finset (Fin 12)).card = 4 := by decide
  have key : ∀ (i1 : Fintype ↑T.verts) (i2 : ∀ v, Fintype ↑(T.neighborSet v)),
      ((@Set.toFinset _ T.verts i1).filter
        (fun v => @Subgraph.degree _ _ T v (i2 v) = 1)).card ≤ 4 :=
    fun i1 i2 => (Finset.card_le_card (hsub i1 i2)).trans h4.le
  refine le_trans (Nat.cast_le.mpr (key _ _)) ?_
  norm_num

/-! ### `b ≤ 10` (each triangle loses a vertex) -/

lemma b_le : b G ≤ 10 := by
  unfold b largestInducedBipartiteSubgraphSize
  have hS : sSup {n | ∃ s : Finset (Fin 12), (G.induce (s : Set (Fin 12))).IsBipartite ∧
      s.card = n} ≤ 10 := by
    apply csSup_le'
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring G s).1 hs
    have key : ∀ a b d : Fin 2, a ≠ b → b ≠ d → a ≠ d → False := by decide
    have tri : ∀ x y z : Fin 12, adjF x y → adjF y z → adjF x z → x ∈ s → y ∈ s → z ∈ s →
        False := by
      intro x y z h1 h2 h3 hx hy hz
      exact key _ _ _ (hc x hx y hy h1) (hc y hy z hz h2) (hc x hx z hz h3)
    have ha : (0 : Fin 12) ∉ s ∨ (8 : Fin 12) ∉ s ∨ (9 : Fin 12) ∉ s := by
      by_contra hn
      simp only [not_or, not_not] at hn
      exact tri 0 8 9 (by decide) (by decide) (by decide) hn.1 hn.2.1 hn.2.2
    have hb : (7 : Fin 12) ∉ s ∨ (10 : Fin 12) ∉ s ∨ (11 : Fin 12) ∉ s := by
      by_contra hn
      simp only [not_or, not_not] at hn
      exact tri 7 10 11 (by decide) (by decide) (by decide) hn.1 hn.2.1 hn.2.2
    have gen : ∀ a b' : Fin 12, a ≠ b' → a ∉ s → b' ∉ s → s.card ≤ 10 := by
      intro a b' hab ha hb
      have hsub : s ⊆ (Finset.univ.erase a).erase b' := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, Finset.mem_univ _⟩
        · rintro rfl; exact hb hx
        · rintro rfl; exact ha hx
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
      omega
    rcases ha with h | h | h <;> rcases hb with h' | h' | h' <;> exact gen _ _ (by decide) h h'
  exact_mod_cast hS

/-! ### The square-degree maximisers are `1` and `6` -/

def sq2 (v w : Fin 12) : Prop := v ≠ w ∧ (adjF v w ∨ ∃ x, adjF v x ∧ adjF x w)

instance : DecidableRel sq2 := fun v w => by unfold sq2; infer_instance

lemma sqd_eq (v : Fin 12) :
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
lemma sq_le : ∀ v : Fin 12, (Finset.univ.filter (sq2 v)).card ≤ 5 := by decide

set_option maxRecDepth 100000 in
lemma sq_eq5 : ∀ v : Fin 12, (Finset.univ.filter (sq2 v)).card = 5 ↔ (v = 1 ∨ v = 6) := by
  decide

lemma M_eq : squareMaximumDegreeVertices G = {1, 6} := by
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

/-! ### `distMin ≥ 5` -/

def pot (x : Fin 12) : ℕ := if x.val ≤ 7 then x.val else if x.val ≤ 9 then 0 else 7

lemma pot_adj (x y : Fin 12) (h : adjF x y) : pot y ≤ pot x + 1 := by
  unfold pot; unfold adjF at h; split_ifs <;> omega

lemma pot_walk {u w : Fin 12} (p : G.Walk u w) : pot w ≤ pot u + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [Walk.length_cons]
    have := pot_adj _ _ h
    omega

lemma dist_ge (u w : Fin 12) : pot w - pot u ≤ G.dist u w := by
  obtain ⟨p, hp⟩ := (connected.preconnected u w).exists_walk_length_eq_dist
  have := pot_walk p
  omega

lemma distMin_ge : 5 ≤ distMin G (squareMaximumDegreeVertices G) := by
  rw [M_eq]
  apply le_distMin G _ 5 1 6 (by simp) (by simp) (by decide)
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact (dist_ge 1 6).trans' (by decide)
  · rw [dist_comm]; exact (dist_ge 1 6).trans' (by decide)
  · exact absurd rfl hxy

theorem conjecture176 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G + b G ≥ (Fintype.card V : ℝ) +
          distMin G (squareMaximumDegreeVertices G) := by
  intro h
  have h1 := h (Fin 12) G connected
  have h2 := Ls_le
  have h3 := b_le
  have h4 : (5 : ℝ) ≤ distMin G (squareMaximumDegreeVertices G) := by
    exact_mod_cast distMin_ge
  simp only [Fintype.card_fin] at h1
  push_cast at h1
  linarith

end WrittenOnTheWallII.GraphConjecture176

#print axioms WrittenOnTheWallII.GraphConjecture176.conjecture176
