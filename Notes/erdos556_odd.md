# erdos556_odd

- Statement: `Erdos556.erdos_556.variants.odd_lower_bound` (for odd n ≥ 3, 4n − 3 ≤ R(C_n; 3))
- Source: `FormalConjectures/ErdosProblems/556.lean:90` (category research solved, AMS 5)
- Date: 2026-11-17

## Proof idea

Since `multicolourRamsey` is an `sInf`, the proof first shows that the set is nonempty. A self-contained three-colour Ramsey lemma (`RC.ramsey`, induction on a₀+a₁+a₂ with the bound 3^r: pick a vertex, apply pigeonhole to its three colour neighbourhoods, then recurse) gives a monochromatic n-clique in any 3-colouring of K_{3^{3n}}, and hence a monochromatic C_n. For the lower bound, take N ≤ 4(n−1) and m = n−1, and split Fin N into 4 blocks x/m. Colour 0 joins vertices in the same block, colour 2 joins blocks {0,1} and {2,3} to each other, and colour 1 covers all other pairs. A copy of C_n in colour 0 stays inside one block, because the cycle graph is preconnected and the block index is constant along edges (`walk_const`), and that block has at most n−1 < n vertices (injection via x % m). Colours 1 and 2 are 2-colourable (block/2, resp. block % 2), so a copy of C_n would 2-colour the odd cycle, which contradicts Mathlib's `chromaticNumber_cycleGraph_of_odd`. `IsEdgeColouring` and `multicolourRamsey` are restated locally, verbatim from FormalConjecturesForMathlib.

## Axioms

'Erdos556.erdos_556.variants.odd_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
