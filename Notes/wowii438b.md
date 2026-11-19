# wowii438b

- Statement: `WrittenOnTheWallII.GraphConjecture438b.conjecture438b` (α₂(G) ≤ α(G) + α(G[V∖H₂]) + |E(G[H₂])|), research solved.
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture438b.lean:49` in the checkout.
- Definitions restated from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`.

## Proof idea

The proof shows the stronger statement for an ARBITRARY vertex set H (lemma `W438.bound`). Connectivity and n > 3 are not used. Let S be 2-independent, so G[S] has maximum degree ≤ 1. Give each vertex the injective key [x ∉ H]·n + index(x), and let R ⊆ S be the endpoints with the larger key on each edge of G[S]. Then S∖R is independent (≤ α). R is independent because each vertex has a unique partner in S, so R∖H ≤ α(V∖H). Every x ∈ R ∩ H has a partner of smaller key, which therefore also lies in H. So x ↦ s(x, partner) injects R ∩ H into E(G[H]). Summing the three parts gives the bound.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-19 (3 compiles)
