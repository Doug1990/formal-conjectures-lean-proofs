# Erdos1010.erdos_1010.variants.rademacher

- Source: `FormalConjectures/ErdosProblems/1010.lean:64` (category research solved, Rademacher's theorem)
- Statement: every graph on `Fin n` with ⌊n²/4⌋+1 edges has at least ⌊n/2⌋ triangles.
- Verified file: `work/erdos1010_rad.lean`. `results/erdos1010_rademacher.lean` is a byte-for-byte copy written with the Write tool and was not compiled separately.

## Proof idea
The proof works on vertex Finsets S with in-S degrees, so it never changes the vertex type. P(S) = Σ_{v∈S} deg_S(v) is twice the edge count, and T(S) is the set of triangles inside S. The claim "2(⌊s²/4⌋+1) ≤ P(S) ⇒ ⌊s/2⌋ ≤ |T(S)|" is proved by strong induction on s = |S|. Mantel's theorem is proved by the same induction, and it gives a triangle xyz in S. Deleting an adjacent pair x, y changes P by exactly 2(d(x)+d(y)) − 2. So if some pair of the triangle has d(x)+d(y) ≤ s, then S∖{x,y} still satisfies the hypothesis for s−2, and the triangle containing x and y is one extra. Otherwise all three pair sums are ≥ s+1. In that case each outside vertex w adjacent to j of x, y, z gives C(j,2) ≥ j−1 triangles (an injective map from W × Fin 3), so t ≥ d(x)+d(y)+d(z) − s − 2 ≥ ⌊s/2⌋.

## Axioms
`'Erdos1010.erdos_1010.variants.rademacher' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-05. 3 compiles. The final compile showed only one unusedSectionVars lint on the helper `mantel`.
