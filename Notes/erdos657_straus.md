# erdos657_straus

- Statement: `Erdos657.erdos_657.variants.straus` (research solved, Straus)
- Source: `FormalConjectures/ErdosProblems/657.lean:118`
- Date: 2026-11-14

Proof idea: take the 2^k vertices φ(s) of the box in ℝ^k with side lengths √(2^i), indexed by subsets s ⊆ Fin k (φ(s)_i = √(2^i) if i ∈ s, else 0). Then dist(φ s, φ t)² = Σ_{i ∈ s∆t} 2^i. Binary expansions are unique (`Finset.geomSum_injective`), so the distance determines s∆t. Hence φ is injective (|A| = 2^k). An isosceles triple would give a∆b = c∆b, i.e. a = c, so there is none. Every distance is √(Σ_{i∈u} 2^i) for a nonempty u, so there are ≤ 2^k − 1 distances. The imports are Mathlib-only. The checkout definitions (`distanceSet`, `distinctDistances`, `Set.Triplewise`, `IsIsosceles`, `Set.IsIsoscelesFree`, the `ℝ^` notation) are restated verbatim; the statement is unchanged.

Axioms: `[propext, Classical.choice, Quot.sound]`
