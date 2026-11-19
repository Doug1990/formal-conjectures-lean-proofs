# LinearArboricityConjecture.linear_arboricity_conjecture.variants.cubic

- Source: `FormalConjectures/Wikipedia/LinearArboricityConjecture.lean:104` (category research solved, Akiyama–Exoo–Harary 1981)
- Statement: every nonempty 3-regular finite graph has linear arboricity exactly 2.
- Proof file: `results/lac_cubic.lean`. The definitions `IsLinearForest`, `HasLinearForestDecomposition` and `linearArboricity` are restated verbatim, with targeted Mathlib imports. The theorem statement is unchanged.

## Proof idea
Lower bound: a vertex of degree 3 has an edge, so 0 forests is impossible, and one linear forest would have to contain all 3 edges at that vertex (degree ≤ 2 fails). Upper bound: Hall's theorem gives an injective map g with v ~ g(v) for all v; the double count is 3|S| ≤ 3|N(S)|. Since g is a permutation, B = {v g(v)} has every degree in {1, 2}, so R = G \ B and B both have maximum degree ≤ 2 ("valid" colourings). Among valid colourings, take one that maximises P = #(R-reachable pairs) + #(B-reachable pairs). Suppose R has a cycle. Then some non-bridge edge vw exists, and v has a second R-neighbour x with vx also a non-bridge. So v, w, x all have R-degree 2 and B-degree ≤ 1. Moving vw (or vx) from R to B keeps the colouring valid and leaves R-reachability unchanged (no bridge was removed). It strictly increases B-reachability unless v and w (respectively v and x) are already B-connected. If both are, then v, w, x are three vertices of B-degree ≤ 1 in one component of a graph with maximum degree 2. That contradicts Σdeg = 2|E| ≥ 2(|C|−1) on the component (Mathlib's `Connected.card_vert_le_card_edgeSet_add_one`). By symmetry (G \ (G \ R) = R) B is acyclic too.

## Axioms
`'LinearArboricityConjecture.linear_arboricity_conjecture.variants.cubic' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-03. 4 compiles (1: three small errors; 2: unused-section-variable lints only; 3: axioms OK plus one remaining lint; 4: clean, with the axioms check). The results copy was written by hand from the verified work file and was not compiled separately.
