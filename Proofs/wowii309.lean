import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/
VertexDistance.lean, Domination.lean). -/
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

def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

structure IsTotalNDominatingSet (G : SimpleGraph α) (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

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

namespace WrittenOnTheWallII.GraphConjecture309

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number of edges whose endpoints are at the same even distance from $v$. -/
def evenHorizontal (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.edgeFinset.filter fun e =>
    let distances := e.toFinset.image (G.computable_dist v)
    distances.card = 1 ∧ ∃ d ∈ distances, Even d).card

/-- The maximum of $\operatorname{distEven}(v)-\operatorname{evenHorizontal}(v)$. -/
noncomputable def maxEvenCorrection (G : SimpleGraph V) [Nonempty V]
    [DecidableRel G.Adj] : ℤ :=
  (Finset.univ.image
    (fun v => (G.distEven v : ℤ) - (evenHorizontal G v : ℤ))).max' (by simp)

/-- The minimum complement-edge neighborhood-union order, when a complement edge exists. -/
def minComplementEdgeNeighborhood (G : SimpleGraph V)
    [DecidableRel G.Adj] : Option ℕ :=
  Gᶜ.edgeFinset.image
    (fun e => Sym2.lift ⟨fun u w =>
      (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card,
      fun u w => by
        change (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card =
          (Gᶜ.neighborFinset w ∪ Gᶜ.neighborFinset u).card
        rw [Finset.union_comm]⟩ e) |>.min

def conjecture309Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    ∀ mt ∈ minComplementEdgeNeighborhood G,
      (G.totalDominationNumber : ℝ) ≤
        ((maxEvenCorrection G : ℝ) + (mt : ℝ)) / 2

/-! ### The graph `C₅[K₃]` on `Fin 15` (clique `i / 3`) -/

def adjF (i j : Fin 15) : Prop :=
  i ≠ j ∧ (i.val / 3 = j.val / 3 ∨ (i.val / 3 + 1) % 5 = j.val / 3 ∨
    (j.val / 3 + 1) % 5 = i.val / 3)

instance : DecidableRel adjF := fun i j => by unfold adjF; infer_instance

lemma adjF_symm (i j : Fin 15) (h : adjF i j) : adjF j i :=
  ⟨Ne.symm h.1, by rcases h.2 with h | h | h <;> omega⟩

def H : SimpleGraph (Fin 15) where
  Adj := adjF
  symm := ⟨fun x y h => adjF_symm x y h⟩
  loopless := ⟨fun x h => h.1 rfl⟩

instance : DecidableRel H.Adj := fun x y => inferInstanceAs (Decidable (adjF x y))

lemma mid : ∀ v w : Fin 15, v ≠ w → ¬ adjF v w → ∃ m, adjF v m ∧ adjF m w := by decide

lemma connected : H.Connected := by
  rw [connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  by_cases h1 : u = v
  · subst h1; exact Reachable.refl _
  by_cases h2 : adjF u v
  · exact Adj.reachable (G := H) h2
  obtain ⟨m, hm1, hm2⟩ := mid u v h1 h2
  exact (Adj.reachable (G := H) hm1).trans (Adj.reachable (G := H) hm2)

lemma dist_eq (v w : Fin 15) :
    H.dist v w = if v = w then 0 else if adjF v w then 1 else 2 := by
  split_ifs with h1 h2
  · subst h1; exact dist_self
  · exact dist_eq_one_iff_adj.2 h2
  · obtain ⟨m, hm1, hm2⟩ := mid v w h1 h2
    have hle : H.dist v w ≤ 2 :=
      (dist_le (Walk.cons (show H.Adj v m from hm1)
        (Walk.cons (show H.Adj m w from hm2) Walk.nil))).trans (by simp)
    have hpos : 0 < H.dist v w := (connected.preconnected v w).pos_dist_of_ne h1
    have hne : H.dist v w ≠ 1 := fun e => h2 (dist_eq_one_iff_adj.1 e)
    omega

/-! ### `maxEvenCorrection ≤ -8` -/

set_option maxRecDepth 100000 in
lemma de_card : ∀ v : Fin 15,
    (Finset.univ.filter fun w => v = w ∨ ¬ adjF v w).card ≤ 7 := by decide

lemma distEven_le (v : Fin 15) : H.distEven v ≤ 7 := by
  unfold distEven
  have : (Finset.univ.filter fun w => Even (H.dist v w)) =
      Finset.univ.filter (fun w => v = w ∨ ¬ adjF v w) := by
    apply Finset.filter_congr
    intro w _
    rw [dist_eq]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h2]
  rw [this]
  exact de_card v

def pairs (v : Fin 15) : Finset (Fin 15 × Fin 15) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ adjF p.1 p.2 ∧ p.1 ≠ v ∧ p.2 ≠ v ∧
    ¬ adjF v p.1 ∧ ¬ adjF v p.2

set_option maxRecDepth 100000 in
lemma pairs_card : ∀ v : Fin 15, 15 ≤ (pairs v).card := by decide

lemma cd2 (v w : Fin 15) (h1 : w ≠ v) (h2 : ¬ adjF v w) : computable_dist H v w = 2 := by
  rw [← dist_eq_computable, dist_eq, if_neg (Ne.symm h1), if_neg h2]

lemma evenH_ge (v : Fin 15) : 15 ≤ evenHorizontal H v := by
  unfold evenHorizontal
  refine (pairs_card v).trans (Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_)
  · intro p hp
    simp only [pairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨-, hadj, h1, h2, h3, h4⟩ := hp
    have e1 := cd2 v p.1 h1 h3
    have e2 := cd2 v p.2 h2 h4
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(mem_edgeFinset).2 hadj, ?_⟩
    show (s(p.1, p.2).toFinset.image (computable_dist H v)).card = 1 ∧
      ∃ d ∈ s(p.1, p.2).toFinset.image (computable_dist H v), Even d
    rw [Sym2.toFinset_mk_eq, Finset.image_insert, Finset.image_singleton, e1, e2,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
    exact ⟨Finset.card_singleton _, 2, Finset.mem_singleton_self _, even_two⟩
  · intro p hp q hq hpq
    simp only [pairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1 e2
    · exfalso
      have a := hp.1
      have b := hq.1
      rw [Fin.lt_def] at a b
      rw [e1, e2] at a
      omega

lemma corr_le : maxEvenCorrection H ≤ -8 := by
  unfold maxEvenCorrection
  apply Finset.max'_le
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨v, -, rfl⟩ := hy
  have h1 := distEven_le v
  have h2 := evenH_ge v
  omega

/-! ### `totalDominationNumber ≥ 3` -/

lemma key : ∀ x y : Fin 15, adjF x y → ∃ v, ¬ adjF v x ∧ ¬ adjF v y := by decide

lemma lower (D : Finset (Fin 15)) (hD : H.IsTotalDominating (D : Set (Fin 15))) :
    3 ≤ D.card := by
  by_contra hlt
  obtain ⟨x, hx, -⟩ := hD 0
  obtain ⟨y, hy, hxy⟩ := hD x
  have hx' : x ∈ D := Finset.mem_coe.1 hx
  have hy' : y ∈ D := Finset.mem_coe.1 hy
  have hne : x ≠ y := (hxy : adjF x y).1
  have hsub : ({x, y} : Finset (Fin 15)) ⊆ D := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx'
    · exact hy'
  have hDeq : ({x, y} : Finset (Fin 15)) = D :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
  obtain ⟨v, hv1, hv2⟩ := key x y hxy
  obtain ⟨w, hw, hvw⟩ := hD v
  have hw' : w ∈ D := Finset.mem_coe.1 hw
  rw [← hDeq, Finset.mem_insert, Finset.mem_singleton] at hw'
  rcases hw' with rfl | rfl
  · exact hv1 hvw
  · exact hv2 hvw

lemma dom3 : ∀ v : Fin 15, adjF v 0 ∨ adjF v 3 ∨ adjF v 6 := by decide

lemma tdn_ge : 3 ≤ totalDominationNumber H := by
  unfold totalDominationNumber
  have hdom : H.IsTotalDominating ((({0, 3, 6} : Finset (Fin 15))) : Set (Fin 15)) := by
    intro v
    rcases dom3 v with h | h | h
    · exact ⟨0, by simp, h⟩
    · exact ⟨3, by simp, h⟩
    · exact ⟨6, by simp, h⟩
  have hne : {n | ∃ D : Finset (Fin 15), H.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨3, {0, 3, 6}, ⟨hdom, by decide⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  rw [← hD.card_eq]
  exact lower D hD.isTotalDominating

/-! ### The complement-edge minimum is at most `12` -/

lemma hE : s((0 : Fin 15), 6) ∈ Hᶜ.edgeFinset := by
  rw [mem_edgeFinset, mem_edgeSet, compl_adj]
  decide

lemma key2 : ∀ f : Sym2 (Fin 15) → ℕ, f s(0, 6) = 12 →
    ∃ m, m ∈ (show Option ℕ from (Hᶜ.edgeFinset.image f).min) ∧ m ≤ 12 := by
  intro f hf
  obtain ⟨m, hm⟩ := Finset.min_of_mem (Finset.mem_image_of_mem f hE)
  refine ⟨m, Option.mem_def.2 hm, ?_⟩
  have h := Finset.min_le (Finset.mem_image_of_mem f hE)
  rw [hm, hf] at h
  exact WithTop.coe_le_coe.1 h

theorem conjecture309 : ¬ conjecture309Statement := by
  intro h
  obtain ⟨mt, hmt, hle⟩ : ∃ mt, mt ∈ minComplementEdgeNeighborhood H ∧ mt ≤ 12 := by
    unfold minComplementEdgeNeighborhood
    apply key2
    simp only [Sym2.lift_mk]
    rw [neighborFinset_eq_filter, neighborFinset_eq_filter]
    decide
  have h1 := h (Fin 15) H connected (by simp) mt hmt
  have h2 : (maxEvenCorrection H : ℝ) ≤ -8 := by exact_mod_cast corr_le
  have h3 : (3 : ℝ) ≤ H.totalDominationNumber := by exact_mod_cast tdn_ge
  have h4 : (mt : ℝ) ≤ 12 := by exact_mod_cast hle
  linarith

end WrittenOnTheWallII.GraphConjecture309

#print axioms WrittenOnTheWallII.GraphConjecture309.conjecture309
