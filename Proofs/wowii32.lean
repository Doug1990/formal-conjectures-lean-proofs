import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Restated from the checkout
(FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Check if a list of vertices forms an induced path in `G`. -/
def isInducedPath (G : SimpleGraph α) (l : List α) : Prop :=
  l.Nodup ∧ ∀ i j : Fin l.length, G.Adj (l.get i) (l.get j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- The path number of a graph: The number of vertices of a largest induced path of the graph. -/
noncomputable def path (G : SimpleGraph α) : ℕ :=
  open scoped Classical in
  let induced_paths := Finset.univ.filter (fun s : Finset α =>
    ∃ l : List α, l.toFinset = s ∧ isInducedPath G l)
  (induced_paths.image Finset.card).max.getD 0

/-- A uniform upper bound on the lengths of induced paths bounds `path`
(proof copied from the checkout). -/
theorem path_le_of_isInducedPath_length_le (G : SimpleGraph α) (k : ℕ)
    (h : ∀ l : List α, G.isInducedPath l → l.length ≤ k) : path G ≤ k := by
  classical
  unfold path
  let inducedPaths := Finset.univ.filter (fun s : Finset α ↦
    ∃ vertices : List α, vertices.toFinset = s ∧ G.isInducedPath vertices)
  change (inducedPaths.image Finset.card).max.getD 0 ≤ k
  have hmax : (inducedPaths.image Finset.card).max ≤ (k : WithBot ℕ) := by
    apply Finset.max_le
    intro cardinality hcardinality
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hcardinality
    obtain ⟨_, vertices, rfl, hvertices⟩ := Finset.mem_filter.mp hs
    rw [List.toFinset_card_of_nodup hvertices.1]
    exact WithBot.coe_le_coe.mpr (h vertices hvertices)
  cases hmaximum : (inducedPaths.image Finset.card).max with
  | bot => exact Nat.zero_le k
  | coe maximum =>
      have : maximum ≤ k := by
        rw [hmaximum] at hmax
        exact WithBot.coe_le_coe.mp hmax
      simpa [hmaximum, Option.getD] using this

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture32

open SimpleGraph

/-- The path on 5 vertices. -/
def P5 : SimpleGraph (Fin 5) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by rcases h with h | h <;> omega⟩

instance : DecidableRel P5.Adj := fun i j =>
  inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

lemma walk_len {u v : Fin 5} (p : P5.Walk u v) :
    (u.val : ℤ) - v.val ≤ p.length ∧ (v.val : ℤ) - u.val ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h' : a.val + 1 = b.val ∨ b.val + 1 = a.val := h
    simp only [Walk.length_cons]
    push_cast
    omega

lemma adj01 : P5.Adj 0 1 := Or.inl rfl
lemma adj12 : P5.Adj 1 2 := Or.inl rfl
lemma adj23 : P5.Adj 2 3 := Or.inl rfl
lemma adj34 : P5.Adj 3 4 := Or.inl rfl

lemma reach0 (i : Fin 5) : P5.Reachable 0 i := by
  have r1 : P5.Reachable 0 1 := adj01.reachable
  have r2 : P5.Reachable 0 2 := r1.trans adj12.reachable
  have r3 : P5.Reachable 0 3 := r2.trans adj23.reachable
  have r4 : P5.Reachable 0 4 := r3.trans adj34.reachable
  fin_cases i
  · exact Reachable.refl _
  · exact r1
  · exact r2
  · exact r3
  · exact r4

lemma conn : P5.Connected :=
  Connected.mk (fun u v => (reach0 u).symm.trans (reach0 v))

lemma dist_ge (u v : Fin 5) (k : ℕ) (hk : k + v.val ≤ u.val ∨ k + u.val ≤ v.val) :
    k ≤ P5.dist u v := by
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist u v
  rw [← hp]
  have := walk_len p
  omega

lemma ecc_ge (u v : Fin 5) (k : ℕ) (hk : k + v.val ≤ u.val ∨ k + u.val ≤ v.val) :
    k ≤ (P5.eccent v).toNat := by
  have h1 : (P5.dist v u : ℕ∞) ≤ P5.eccent v := by
    rw [(conn v u).coe_dist_eq_edist]
    exact edist_le_eccent
  have hne : P5.eccent v ≠ ⊤ :=
    ne_top_of_le_ne_top ((connected_iff_ediam_ne_top).1 conn) eccent_le_ediam
  have h2 : P5.dist v u ≤ (P5.eccent v).toNat := by
    have := ENat.toNat_le_toNat h1 hne
    simpa using this
  have h3 := dist_ge v u k (by omega)
  omega

lemma deg (i : Fin 5) : P5.degree i = if i = 0 ∨ i = 4 then 1 else 2 := by
  fin_cases i <;> decide

lemma minDeg : P5.minDegree = 1 := by
  apply le_antisymm
  · have := P5.minDegree_le_degree 0
    rw [deg] at this
    simpa using this
  · apply P5.le_minDegree_of_forall_le_degree
    intro v
    rw [deg]
    split_ifs <;> omega

lemma maxDeg : P5.maxDegree = 2 := by
  apply le_antisymm
  · apply P5.maxDegree_le_of_forall_degree_le
    intro v
    rw [deg]
    split_ifs <;> omega
  · have := P5.degree_le_maxDegree 1
    rw [deg] at this
    simpa using this

lemma hA : (Finset.univ.filter (fun v => P5.degree v = P5.minDegree)) = {0, 4} := by
  rw [minDeg]
  ext v
  fin_cases v <;> simp [deg]

lemma hM : (Finset.univ.filter (fun v => P5.degree v = P5.maxDegree)) = {1, 2, 3} := by
  rw [maxDeg]
  ext v
  fin_cases v <;> simp [deg]

lemma path_le : path P5 ≤ 5 := by
  apply path_le_of_isInducedPath_length_le
  intro l hl
  have := hl.1.length_le_card
  simpa using this

/--
WOWII [Conjecture 32](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \operatorname{dist}\_{\operatorname{avg}}(A) + 0.5 \cdot \operatorname{ecc}\_{\operatorname{avg}}(M)$,
...

The conjecture is false: the path on 5 vertices is a counterexample.
-/
theorem conjecture32 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let A : Finset α := Finset.univ.filter (fun v => G.degree v = G.minDegree)
      let M : Finset α := Finset.univ.filter (fun v => G.degree v = G.maxDegree)
      let distavgA : ℝ := (∑ p ∈ A.offDiag, (G.dist p.1 p.2 : ℝ)) / (A.offDiag.card : ℝ)
      let eccavg (S : Finset α) : ℝ := (∑ v ∈ S, (G.eccent v).toNat) / (S.card : ℝ)
      distavgA + (1 / 2 : ℝ) * eccavg M ≤ (path G : ℝ) := by
  intro hall
  have key := hall (Fin 5) P5 conn
  dsimp only at key
  rw [hA, hM] at key
  have hoff : ({0, 4} : Finset (Fin 5)).offDiag = {(0, 4), (4, 0)} := by decide
  rw [hoff] at key
  have hd1 := dist_ge 0 4 4 (by decide)
  have hd2 := dist_ge 4 0 4 (by decide)
  have he1 := ecc_ge 4 1 3 (by decide)
  have he2 := ecc_ge 4 2 2 (by decide)
  have he3 := ecc_ge 0 3 3 (by decide)
  have hp := path_le
  have hc : ({1, 2, 3} : Finset (Fin 5)).card = 3 := by decide
  rw [Finset.sum_pair (by decide), Finset.card_pair (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), hc] at key
  have r1 : (4 : ℝ) ≤ (P5.dist 0 4 : ℝ) := by exact_mod_cast hd1
  have r2 : (4 : ℝ) ≤ (P5.dist 4 0 : ℝ) := by exact_mod_cast hd2
  have a1 : (3 : ℝ) ≤ ((P5.eccent 1).toNat : ℝ) := by exact_mod_cast he1
  have a2 : (2 : ℝ) ≤ ((P5.eccent 2).toNat : ℝ) := by exact_mod_cast he2
  have a3 : (3 : ℝ) ≤ ((P5.eccent 3).toNat : ℝ) := by exact_mod_cast he3
  have hp' : (path P5 : ℝ) ≤ 5 := by exact_mod_cast hp
  push_cast at key
  linarith

#print axioms conjecture32

end WrittenOnTheWallII.GraphConjecture32
