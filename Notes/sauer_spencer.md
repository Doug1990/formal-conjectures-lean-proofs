# sauer_spencer

- Statement: `BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.sauer_spencer` (category research solved, Sauer–Spencer 1978)
- Source: `FormalConjectures/Paper/BollobasEldridgeCatlinConjecture.lean:70` (`Packs` restated locally; the statement is unchanged)

Proof idea: take a permutation σ that minimises the number of ordered conflict pairs (u,v), i.e. pairs with G₁.Adj u v and G₂.Adj (σu) (σv). Suppose a conflict (u,v) exists. A vertex w is bad if σw is a G₂-neighbour of σ(N₁(u)) (at most Δ₁Δ₂ such w) or w is a G₁-neighbour of σ⁻¹(N₂(σu)) (at most Δ₂Δ₁ such w). u is bad in both ways, so together with v at most 2Δ₁Δ₂ < n vertices are excluded, and a good w ≠ v exists. Swapping u and w creates no new conflict: the conflict set of σ∘(u w) is contained in the old one, which a 3×3 case analysis on whether each endpoint is u, w or neither confirms. The swap also removes (u,v), which contradicts minimality.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-01. 2 compiles.
