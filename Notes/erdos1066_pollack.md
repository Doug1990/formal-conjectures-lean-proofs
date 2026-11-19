# erdos1066_pollack

- Statement: `Erdos1066.erdos_1066.variants.pollack` (n/4 ≤ g n), checkout file `FormalConjectures/ErdosProblems/1066.lean:93`, category research solved.
- Date: 2026-11-13

## Proof idea
The literature (Pollack) uses the Four Colour Theorem. This proof avoids it. In a finite planar point set with all pairwise distances ≥ 1, the lexicographically smallest point v (minimal x, then minimal y) has at most 3 points at distance exactly 1. Each such neighbour is v + (cos θ, sin θ) with θ = arcsin(Δy) ∈ (−π/2, π/2]. Here x ≥ 0 by minimality, and θ = −π/2 is excluded by the y-tie-break. Two neighbours are ≥ 1 apart, so cos(θ−θ') ≤ 1/2, hence |θ−θ'| ≥ π/3. Pigeonhole on ⌈(θ+π/2)/(π/3)⌉ ∈ {1,2,3} then rules out 4 neighbours. Greedy induction follows: put v in the independent set and delete v and its ≤ 3 neighbours, so |X| ≤ 4|I|. This gives indepNum ≥ ⌈n/4⌉ for every admissible X. The sSup defining g is bounded because the collinear configuration {(i,0) : i < n} is admissible and indepNum ≤ |X|. `UnitDistancePlaneGraph` and `g` are restated verbatim, with targeted Mathlib imports.

## Axioms
'Erdos1066.erdos_1066.variants.pollack' depends on axioms: [propext, Classical.choice, Quot.sound]
