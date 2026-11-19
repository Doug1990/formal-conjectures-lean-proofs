# wowii309

- Statement: `WrittenOnTheWallII.GraphConjecture309.conjecture309` (DISPROOF of γ_t ≤ ½(max_v(distEven − evenHorizontal) + min_{e ∈ E(Ḡ)} |N_Ḡ(e)|))
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture309.lean:86` (research solved, Gebendorfer)

Proof idea: the counterexample is C₅[K₃] on Fin 15 (vertex i lies in clique i/3, and cliques are adjacent cyclically mod 5). Two non-adjacent vertices always have a common neighbour, so dist ∈ {0, 1, 2} (`dist_eq`). For every v, distEven(v) = 7 (v plus the two far cliques), and evenHorizontal(v) ≥ 15 (the far cliques span a K₆; injection from ordered pairs i < j into Sym2 edges, with `computable_dist` rewritten through `dist_eq_computable`). So maxEvenCorrection ≤ −8. The complement edge s(0, 6) has a neighbourhood union of size 12, so the Option-minimum is ≤ 12. A total dominating set needs an adjacent pair x, y, and every adjacent pair leaves some vertex undominated (`decide`), so γ_t ≥ 3 ({0, 3, 6} witnesses nonemptiness). Then 3 ≤ (−8 + 12)/2 = 2 is a contradiction. The library definitions (computable_dist, distEven, totalDominationNumber) are restated from FormalConjecturesForMathlib.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-19
