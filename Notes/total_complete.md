# total_complete

- Statement: `TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph` (category research solved)
- Source: `FormalConjectures/Wikipedia/TotalColoringConjecture.lean:78`
- Date: 2026-11-02

## Proof idea
Let m = 2⌊n/2⌋+1. This is odd and n ≤ m ≤ n+1. Colour vertex i with 2i mod m and edge {i,j} with i+j mod m (in `Fin m`).
Since all values are < 2m, each `% m` is either x or x − m. Linear arithmetic (omega) then gives:
adjacent vertices get different colours because m is odd; two edges sharing v have different colours because v+a ≡ v+b forces a = b; vertex v and edge {v,a} have different colours because 2v ≡ v+a forces v = a.
This makes K_n totally m-colourable, so χ'' ≤ m. For n ≥ 1, Δ(K_n) = n − 1 (`complete_graph_degree` + `degree_le_maxDegree`), so m ≤ Δ + 2. For n = 0, m = 1 ≤ 2.
The definitions from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/TotalColouring.lean are restated verbatim, because FormalConjecturesUtil is not built here.

## Axioms
`propext, Classical.choice, Quot.sound`
