# wowii64

- Statement: `WrittenOnTheWallII.GraphConjecture64.conjecture64` (disproof of f ≥ ⌈√(α·(1 + n mod Δ))⌉)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture64.lean:55` (research solved; an external formal proof is linked upstream)

Proof idea: the same C₅[K₄] counterexample on `Fin 20` as wowii63 (arithmetic adjacency, omega-driven). Every vertex has degree 11 (counted by `decide`), so Δ = 11 and n mod Δ = 9. {0, 8} is independent, so α ≥ 2 and the radicand is ≥ 20 > 16, which gives ⌈√·⌉ ≥ 5. The induced-forest bound f ≤ 4 is the wowii63 fibre argument (≤ 2 per clique by a triangle, a clique with 2 vertices forces both neighbouring cliques to be empty, and a 5-cycle rules out hitting all 5 cliques). largestInducedForestSize is restated verbatim from the checkout; indepNum and maxDegree are Mathlib's.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-18
