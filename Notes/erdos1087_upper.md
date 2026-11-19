# erdos1087_upper

- Statement: `Erdos1087.erdos_1087.variants.upper`, f(n) = O(n^{7/2}) (Erdős–Purdy upper bound, research solved)
- Source: `FormalConjectures/ErdosProblems/1087.lean:98`
- Date: 2026-11-14

## Proof idea
The proof is elementary and needs only one geometric fact: two circles with distinct centres meet in at most two points (`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`). From it comes a generic Cauchy–Schwarz codegree lemma (`UP.cs`).
1. For every r, the number M(r) of ordered pairs at distance r satisfies M(r)² ≤ 3n³ (a K_{2,3}-type argument).
2. The number I of isosceles triples (apex, b, c) satisfies I² ≤ 3n⁵. Two distinct apexes and b leave at most 2 choices for c.

A degenerate 4-set has two different unordered pairs at the same distance. This follows from fibres of size ≤ 2: 12 ordered pairs map onto fewer than 6 distances. If the two pairs are disjoint, the set is the image of a 4-tuple in QA, and |QA| ≤ Σ_v M(d_v), so |QA|² ≤ 3n⁷. Otherwise it is an isosceles triple plus a fourth point, at most n·I sets with (nI)² ≤ 3n⁷. So f(n) ≤ 2√3·n^{7/2} ≤ 4·n^{7/2}. The definitions `distanceSet`, `distinctDistances`, `HasRepeatedDistance`, `degenerateCount` and `f` are restated verbatim with targeted imports.

## Axioms
`'Erdos1087.erdos_1087.variants.upper' depends on axioms: [propext, Classical.choice, Quot.sound]`
