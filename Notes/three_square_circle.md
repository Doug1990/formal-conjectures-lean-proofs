# SquarePacking.three_square_packing_in_circle_bound

- Source: `FormalConjectures/Wikipedia/SquarePacking.lean:155` (category textbook)
- Statement: `Nonempty (Packing 3 UnitSquare (Circle ((5 * NNReal.sqrt 17) / 16)))`
- Note: the work file restates the definitions locally (`Square`, `UnitSquare`, `Circle`, `Packing`) with targeted imports. It also adds `local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)`, because the checkout's notation comes from FormalConjecturesUtil, which cannot be imported.

**Proof idea.** The three embeddings are translations (`IsometryEquiv.addRight`). Two open unit squares sit side by side at x ∈ (-1,0) and (0,1), y ∈ (-13/16, 3/16), and a third is centred above them at x ∈ (-1/2,1/2), y ∈ (3/16, 19/16). The circle is centred at the origin. The centre height 13/16 makes the bottom outer corners and the top corners equidistant from the origin, with squared distance 1 + 169/256 = 1/4 + 361/256 = 425/256 = (5√17/16)². Because the squares are open, every point lies strictly inside the circle (`nlinarith` on the coordinate bounds). Disjointness follows from the disjoint coordinate ranges (`linarith` after `fin_cases`).

**Axioms:** `propext, Classical.choice, Quot.sound`

**Date:** 2026-10-29 (2 compiles)
