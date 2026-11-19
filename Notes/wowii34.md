# wowii34

- Statement: `WrittenOnTheWallII.GraphConjecture34.conjecture34` (DISPROOF of path ≥ ⌈dist_avg(C,V) + dist_avg(M,V)⌉)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture34.lean:57` (research solved)
- Date: 2026-11-19

Proof idea: the docstring's 39-vertex tree is built on `Fin 39`, using an arithmetic parent function `par`. Vertex 0 is the centre p4; vertices 1..31 are the perfect binary tree of depth 4 in heap order; 32..35 are p3, p2, p1 and the hub; 36..38 are the hub's leaves. Connectivity and the upper bound ecc(0) ≤ 5 come from parent walks (`walk0`). Distance lower bounds come from 1-Lipschitz potentials checked by `decide` (`pot` / `dist_ge`). These give ecc(v) ≥ 6 for v ≠ 0 (witnesses: leaf 36 and deep leaf 31), so center = {0}. They also give Σ dist(0,·) ≥ 154 and Σ dist(35,·) ≥ 266. Degree counts by `decide` give M = {35}. `avg_core` turns each average into ≥ S/38 (at most 38 pairs; zero distances do not change the sum). The pair `Finset` keeps the statement's classical instances via implicit instance arguments in `avg_ge`. path ≤ 11 is a depth argument: an induced path never steps down to a child and then back up (by injectivity), and all depths are ≤ 5, so 12 vertices are impossible. 154/38 + 266/38 = 210/19 > 11.

Axioms: propext, Classical.choice, Quot.sound
