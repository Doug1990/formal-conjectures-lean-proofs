# WrittenOnTheWallII.Test.petersen_girth

- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line ~315), `@[category test, AMS 5]`
- Statement: `PetersenGraph.girth = 5`, where `PetersenGraph := petersenGraph` (Kneser graph K(5,2)). `PetersenVertex`, `petersenGraph` and its `DecidableRel` instance are copied verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean`. The file uses targeted Mathlib imports because the full `import Mathlib` / FormalConjecturesUtil does not load in time.

Proof idea: Upper bound: the explicit closed walk {0,1}-{2,3}-{0,4}-{1,2}-{3,4}-{0,1} is checked to be a cycle by `decide`, so `egirth ≤ 5`. Lower bound: a cycle of length 3 or 4 gives, through `cycleGraph_isContained_iff`, an injective homomorphism from `cycleGraph n`. The proof uses cardinality arguments in `Fin 5`, not brute force. A triangle would be three pairwise disjoint 2-sets, whose union has 6 elements. A 4-cycle a-b-c-d has a ≠ c and b ≠ d, so `a ∪ c` and `b ∪ d` each have at least 3 elements, and these two unions are disjoint. That again gives at least 6 elements. So `egirth = 5`, which gives `girth = 5`.

Axioms: `'WrittenOnTheWallII.Test.petersen_girth' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compile output: no errors, no sorry warnings (first compile).

Date: 2026-10-28
