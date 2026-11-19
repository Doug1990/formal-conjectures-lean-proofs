# fernandes33

- Statement: `Arxiv.«2605.12342».conjecture_1.variants.rank_3_3` (Γ_{3⊕3} is not 2-generated)
- Source: `FormalConjectures/Arxiv/2605.12342/Conjecture1.lean:128` (category research solved)
- Verified file: `work/fernandes33.lean` (copied here as `fernandes33.lean`)

Proof idea: Let N ≤ Γ = Γ_{3⊕3} be the pairs with even first (hence also even second) component, i.e. N ≅ A₃ × A₃. Every element of N has order dividing 3, and every element outside N is a pair of transpositions: an involution that inverts every element of N by conjugation. The product of two elements outside N lies in N. A generic lemma (`not_two_gen`) then shows that any two elements lie either in N (a proper subgroup) or in a "dihedral" subgroup ⟨a⟩ ∪ t⟨a⟩ with a ∈ N and t ∉ N. That subgroup has at most 6 elements, while |Γ| ≥ 12 (injection Perm(Fin 3) × Bool → Γ). So no two elements generate Γ. The facts about permutations of Fin 3 are checked by `decide` after enumerating the 6 permutations.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-01
