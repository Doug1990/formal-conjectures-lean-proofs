import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

namespace Erdos816

open scoped Classical in
/--
`G` contains two vertices of the same degree which are joined by a path of length `3`.
-/
def HasEqualDegreePathThree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3

namespace KB

open scoped Classical in
lemma deg_inl (n : ℕ) (a : Fin n) :
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).degree (Sum.inl a) = n + 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp

open scoped Classical in
lemma deg_inr (n : ℕ) (b : Fin (n + 1)) :
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).degree (Sum.inr b) = n := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp

/-- A walk of length 3 in a complete bipartite graph changes sides. -/
lemma side {V W : Type*} {u v : V ⊕ W} (p : (completeBipartiteGraph V W).Walk u v)
    (hp : p.length = 3) : u.isLeft ≠ v.isLeft := by
  have key : ∀ {x y : V ⊕ W}, (completeBipartiteGraph V W).Adj x y → y.isLeft = !x.isLeft := by
    rintro (x | x) (y | y) h <;> simp_all
  match p, hp with
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    have e1 := key h1
    have e2 := key h2
    have e3 := key h3
    rw [e3, e2, e1]
    cases u.isLeft <;> simp

end KB

open scoped Classical in
theorem erdos_816.variants.complete_bipartite : ∀ n : ℕ,
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).edgeFinset.card = n ^ 2 + n ∧
      ¬ HasEqualDegreePathThree (completeBipartiteGraph (Fin n) (Fin (n + 1))) := by
  intro n
  constructor
  · have h := sum_degrees_eq_twice_card_edges (completeBipartiteGraph (Fin n) (Fin (n + 1)))
    rw [Fintype.sum_sum_type] at h
    simp only [KB.deg_inl, KB.deg_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    have e1 : (n + 1) * n = n * (n + 1) := Nat.mul_comm _ _
    have e2 : n ^ 2 + n = n * (n + 1) := by rw [sq, Nat.mul_succ]
    rw [e1] at h
    rw [e2]
    generalize n * (n + 1) = X at h ⊢
    omega
  · rintro ⟨u, v, -, hdeg, p, -, hp⟩
    have hs := KB.side p hp
    rcases u with a | b <;> rcases v with a' | b'
    · simp at hs
    · rw [KB.deg_inl, KB.deg_inr] at hdeg; omega
    · rw [KB.deg_inl, KB.deg_inr] at hdeg; omega
    · simp at hs

end Erdos816

#print axioms Erdos816.erdos_816.variants.complete_bipartite
