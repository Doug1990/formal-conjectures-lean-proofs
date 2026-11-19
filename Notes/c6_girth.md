# WrittenOnTheWallII.Test.C6_girth

- Source: `FormalConjectures/WrittenOnTheWallII/Test.lean` (line ~422), `@[category test, AMS 5]`
- Statement: `C6.girth = 6`, where `C6 := cycleGraph 6` (restated locally; file uses `import Mathlib` because FormalConjecturesUtil is not built).

Proof idea: Upper bound: Mathlib's Eulerian cycle `cycleGraph.cycle 3` is a cycle of length 6, so `egirth ≤ 6`. Lower bound: a cycle of length n ∈ {3,4,5} would give, through `cycleGraph_isContained_iff`, an injective homomorphism `cycleGraph n → cycleGraph 6`. Adjacency in `cycleGraph 6` becomes `(u+1)%6 = v ∨ (v+1)%6 = u` (a 36-case `decide`). Then `omega` rules out each n: odd n fails on parity, and n = 4 fails because the image vertices 0/2 and 1/3 are distinct by injectivity. So `egirth = 6`, which gives `girth = 6`.

Axioms: `'WrittenOnTheWallII.Test.C6_girth' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compile output: only a deprecation warning for `push_neg`, no sorry.

Date: 2026-10-28
