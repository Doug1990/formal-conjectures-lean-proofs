# wowii3

- Statement: `WrittenOnTheWallII.GraphConjecture3.conjecture3` (research solved), source
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture3.lean:46` in the checkout.
  For connected `G` with ≥ 2 vertices: `i(G) · MaxTemp(G) ≤ Ls(G)`.
- Proof idea: let `v` attain `MaxTemp`, `d = deg v < n`, so `MaxTemp = d/(n−d)`. A
  maximum-cardinality independent set containing `v` is dominating (otherwise it could be
  enlarged) and avoids `N(v)`, so `i(G) ≤ n − d` and `i(G)·d/(n−d) ≤ d`. For `d ≤ Ls`, the
  star at `v` is acyclic (every edge is a bridge by the cut lemma), so Mathlib's
  `Connected.exists_isTree_le_of_le_of_isAcyclic` extends it to a spanning tree `T` with
  `deg_T v ≥ d`. The tree handshake (Σ deg = 2(n−1), every non-leaf has degree ≥ 2) shows
  that every vertex degree in a tree is ≤ #leaves. `Ls_ge` (from wowii4) turns that into a
  lower bound for `Ls`. Definitions (Ls, temp_v, MaxTemp, IsDominating,
  IsNIndepDominatingSet, indepDominationNumber) are restated locally from
  FormalConjecturesForMathlib, and the `@[category]` attribute is dropped.
- Axioms: `[propext, Classical.choice, Quot.sound]`
- Date: 2026-11-18
