# wowii7

- Statement: `WrittenOnTheWallII.GraphConjecture7.conjecture7` (Ls(G) ≥ max_v l(v) − 1 + n − 2α(G))
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture7.lean:53` (research solved, DeLaVina–Fajtlowicz–Waller; an external Lean proof is linked upstream)
- Date: 2026-11-18

Proof idea: let v attain the maximum l(v), and let I ⊆ N(v) be independent with |I| = l(v). Run the
connected-dominating-set pair greedy (as in wowii6), but start it from the star S = {v} ∪ I with
Y = I. Invariant: S is connected around v, Y ⊆ S is independent, and |S| + l(v) ≤ 2|Y| + 1. While
some vertex is undominated, a boundary dart of a walk from v gives x adjacent to S and y adjacent to x
but not to S. Adding x and y to S and y to Y keeps the invariant, since y has no neighbour in S ⊇ Y.
At the end S is a connected dominating set, so Ls ≥ n − |S| ≥ n − (2α + 1 − l(v)) (`tree_bound`:
extend the S-internal edges plus one attachment edge per outside vertex to a spanning tree, in which
all outside vertices are leaves).

Axioms: `propext, Classical.choice, Quot.sound`

The file restates `Ls` and `indepNeighborsCard` from FormalConjecturesForMathlib with targeted Mathlib
imports.
