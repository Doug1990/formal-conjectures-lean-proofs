# wowii91

- Statement: `WrittenOnTheWallII.GraphConjecture91.conjecture91` (research solved, a DISPROOF),
  source `FormalConjectures/WrittenOnTheWallII/GraphConjecture91.lean:64` in the checkout.
  It says that `b(G) ≤ 1 + f(G)·⌈l(G)⌉/2` fails for some connected graph.
- Proof idea: this is Talwar's 11-vertex counterexample (graph6 `JBza_CB?wF_`, decoded by
  hand): K_{3,3} minus an edge on {0,1,2}|{3,4,5} (edge 0–3 missing), a K₅ on {6,…,10},
  and edges 1–6 and 3–6. It lives on `ULift (Fin 11)` because the statement is
  universe-polymorphic (`Type*`).
  - b ≥ 8: {0,…,5,7,8} with an explicit 2-colouring.
  - f ≤ 6: an induced forest has ≤ 2 vertices of the K₅ (a triangle is not acyclic), and
    ≤ 4 vertices of {0,…,5} (any 5 of them contain one of five explicit 4-cycles). Both use
    "an edge of a cycle is not a bridge" via `isAcyclic_iff_forall_adj_isBridge`.
  - l ≤ 2: every N(v) is covered by `kv v` cliques (an explicit index function g), with
    Σ kv = 22, so `indepNum` of the induced neighbourhood is ≤ kv v.

  So the bound is ≤ 1 + 6·2/2 = 7 < 8. All finite facts are checked by elaborator `decide`
  over `Fin 11` (no powersets) and moved to ULift with `Finset.map Equiv.ulift`.
  Definitions (indepNeighborsCard, l, largestInducedForestSize, b, …) are restated locally,
  and the `@[category]` attribute is dropped.
- Axioms: `[propext, Classical.choice, Quot.sound]`
- Date: 2026-11-18
