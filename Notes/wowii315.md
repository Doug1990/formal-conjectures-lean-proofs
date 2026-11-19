# wowii315

- Statement: `WrittenOnTheWallII.GraphConjecture315.conjecture315` (research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture315.lean:53` (definitions restated from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean`)

## Proof idea
Let P be the set of pendant vertices. Two adjacent leaves would close off a component {p, q}, so G = K₂, and α = 1 ≠ 2 = |P|. So P is independent, and since |P| = α it is a maximum independent set. Hence every non-leaf v has a leaf neighbour (otherwise P ∪ {v} would be a larger independent set). A leaf's only neighbour must lie in any total dominating set, so every total dominating set contains all non-leaves. If every non-leaf has a non-leaf neighbour, then the non-leaves already form a total dominating set, and every minimal one equals it. Otherwise some non-leaf s has only leaf neighbours, so by connectivity G is a star at s, and every minimal total dominating set is {s, l} for a leaf l, of size 2.

## Axioms
`'WrittenOnTheWallII.GraphConjecture315.conjecture315' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-19
