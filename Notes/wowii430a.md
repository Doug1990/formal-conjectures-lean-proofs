# wowii430a

- Statement: `WrittenOnTheWallII.GraphConjecture430a.conjecture430a` (DISPROOF of i(G) ≤ α(G[N(C)]) + 2⌊CW(G) − 1⌋)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture430a.lean:64` (research solved)
- Date: 2026-11-19

Proof idea: the docstring's clique blow-up of P₇ with blob orders (1,4,12,19,12,4,1) is built on `Fin 53`, with blob index `bl` and adjacency "distinct, and blobs differ by ≤ 1". Parent walks toward vertex 17 give connectivity and ecc(17) ≤ 3. The 1-Lipschitz potentials bl and 6 − bl give ecc(v) ≥ 4 outside the middle blob, so the centre lies in blob 3 and N(C) ⊆ blobs 2..4. An independent set there has pairwise blob gaps ≥ 2, so it has at most 2 vertices (α ≤ 2). {0, 17, 52} is an independent dominating set, so the sInf is attained. Every dominating set must hit three pairwise disjoint blob windows (around blobs 0, 3 and 6), so i ≥ 3. Caro–Wei: deg+1 per blob is 5, 17, 35, 43, 35, 17, 5. Writing each 1/(deg+1) as nn/25585 gives a sum of 51123/25585 < 2, so ⌊CW − 1⌋ ≤ 0. Hence 3 ≤ 2 + 0 is false.

Axioms: propext, Classical.choice, Quot.sound
