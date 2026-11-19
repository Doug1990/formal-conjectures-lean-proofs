# wowii1

- Statement: `WrittenOnTheWallII.GraphConjecture1.conjecture1` (Ls(G) ≥ n + 1 − 2μ(G))
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture1.lean:50` (research solved; an external Lean proof is linked upstream)
- Date: 2026-11-18

Proof idea: this is the bound `boundA` from results/wowii6.lean, re-used verbatim. Take r farthest from
some vertex u and a neighbour s of r. Shortest walks from u avoid r, so G − r is connected. Run the
pair greedy in G − r from s. It produces a connected S, |S| = 2k + 1, dominating V − r, together with
a matching of k edges on S − s. Add the edge rs to get a matching of size k + 1 ≤ μ. S also dominates
r, so `tree_bound` (connected dominating S ⇒ Ls ≥ n − |S|) gives Ls ≥ n − 2k − 1 ≥ n + 1 − 2μ.

Axioms: `propext, Classical.choice, Quot.sound`

The file restates `Ls` and `matchingNumber` from FormalConjecturesForMathlib with targeted Mathlib imports.
