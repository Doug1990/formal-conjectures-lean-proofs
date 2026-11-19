# wowii316

- Statement: `WrittenOnTheWallII.GraphConjecture316.conjecture316` (research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture316.lean:48`
- Date: 2026-11-19

**Proof idea.** Let P be the set of pendant vertices, C the rest, p = |P|, c = |C|, n = p + c.
First we show that any two distinct non-pendant vertices a, b are adjacent. Suppose not. If c ≥ 3,
count: Σ deg_{Gᶜ} = n² − n − Σ deg, and Σ deg = p + Σ_{v∈C}(|N(v)∩C| + |N(v)∩P|) ≤ 2p + c² − c − 2.
(Double counting gives Σ_v |N(v)∩P| = Σ_{l∈P} deg l = p, and a, b each miss one C-vertex.) With
Σ deg_{Gᶜ} ≤ p·n this gives p(c−3) ≤ −2, a contradiction. If c = 2, then C = {a, b}, and
{a} ∪ (pendants at a) is closed under adjacency, so by connectivity it contains b, a contradiction.
Then let Q be the set of neighbours of pendants. Every TDS contains Q. If |Q| ≥ 2, Q is itself a
TDS (C is a clique, and two adjacent pendants would force G = K₂), so every minimal TDS equals Q.
If |Q| ≤ 1, every minimal TDS T contains a vertex x adjacent to all other vertices (the unique
support vertex, or any vertex of T if there are no pendants), so T = {x, w} and |T| = 2.
The definitions (averageDegree, total domination, pendantVertices) are restated with targeted
Mathlib imports.

Axioms: `propext, Classical.choice, Quot.sound`
