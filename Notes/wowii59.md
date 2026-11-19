# wowii59

- Statement: `WrittenOnTheWallII.GraphConjecture59.conjecture59` (a disproof of f ≥ ⌈√(residue·b)⌉)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture59.lean:59` (research solved)
- Date: 2026-11-19

The counterexample is an 18-vertex graph in the docstring's family, with the chain core chosen by a `#eval` search (work/wowii59_search.lean). The core is the bipartite chain graph x_i ~ y_j iff j < k_i with k = [5,5,5,4,2] on vertices 0..9. Hub 10 is adjacent to all other vertices, so 11..17 are leaves. Residue = 10: the degrees come from `decide`, and the explicit Havel–Hakimi chain uses the wowii109 helpers (`ms_eq`/`step`). b ≥ 17: everything except the hub is 2-colourable. f ≤ 13: take an induced forest s with 0/1 indicators. For two core x's in s, their common neighbours (a y-range) contain at most one vertex of s (else there is a C4). If the hub and x_i are in s, then N(x_i) ∩ s = ∅ (else there is a triangle). The y-range cards are bridged to indicator sums (`filt_card`). A 32-way case split plus `omega` (`arith59`) gives |s ∩ (core ∪ hub)| ≤ 6, and with ≤ 7 leaves |s| ≤ 13. Then 10·17 = 170 > 169, so ⌈√170⌉ ≥ 14 > 13.

Axioms: propext, Classical.choice, Quot.sound
