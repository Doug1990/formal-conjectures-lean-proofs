# wowii109

- Statement: `WrittenOnTheWallII.GraphConjecture109.conjecture109` (a disproof of α ≤ ⌊(residue + 2b)/3⌋)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture109.lean:55` (research solved)
- Date: 2026-11-19

The counterexample is the docstring's 13-vertex graph K̄₇ ∨ (K₃ ⊔ K₃) on `Fin 13`, with arithmetic adjacency. Vertices 0..6 are independent, and {7,8,9} and {10,11,12} are cliques joined to all of 0..6. Kernel `decide` cannot unfold the well-founded `residueAux` / `List.mergeSort`, so the residue is computed step by step. Each Havel–Hakimi step is fixed by uniqueness of sorted permutations (`List.Perm.eq_of_pairwise'` + `pairwise_mergeSort'`), and every perm/sortedness side condition is checked by `decide`. The chain is 9⁶6⁷ → … → [0,0], so residue = 2. The degrees (6 and 9) come from `decide` on neighbour filters. α ≥ 7 comes from {0..6}. For b ≤ 9: if a 2-colourable induced set meets {0..6}, it has at most one vertex in each K₃ (otherwise there is a triangle), so its size is at most 7+1+1. Otherwise its size is at most 6. Then ⌊(2 + 2·9)/3⌋ = 6 < 7. The Residue/Induced definitions are restated (identical, except that the termination proof needed no final `omega` with this toolchain).

Axioms: propext, Classical.choice, Quot.sound
