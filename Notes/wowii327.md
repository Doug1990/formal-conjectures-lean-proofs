# wowii327

- Statement: `WrittenOnTheWallII.GraphConjecture327.conjecture327` (DISPROOF of "connected G with 3·γ(G) = i(G) is well totally dominated"), research solved.
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture327.lean:69` in the checkout.
- Definitions restated from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean` and `WellTotallyDominated.lean` (only Mathlib imports needed).

## Proof idea

This uses the docstring's 12-vertex counterexample on `Fin 12` (u = 0, v = 1, a_i = 2+i, b_i = 7+i), with adjacency given by an explicit edge list and decided by `decide`. Connectivity holds because every vertex is 0 or adjacent to 0 or 1. γ = 2: {0,1} dominates, and no single vertex is universal (`decide`). i = 6: {u, b_0..b_4} is independent and dominating. For the lower bound, each vertex is encoded by a 0/1 indicator `ind D k`, and the 12 domination constraints and 17 independence constraints become linear ℕ facts. A 16-way case split on u, v, b_0, b_3 is then closed by `omega`. Finally, {u, v} and {v, b_0, b_3} are both minimal total dominating sets (minimality via private neighbours: `min_of_priv`), with sizes 2 ≠ 3.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-19 (3 compiles)
