# erdos588_trivial

- Statement: `Erdos588.erdos_588.variants.trivial_upper` (category textbook)
- Source: `FormalConjectures/ErdosProblems/588.lean:77`
- Date: 2026-10-30

Proof idea: pair counting. For a finite point set T, every line in `linesWithPointsFor k T`
is spanned by two distinct points of T, so it is a genuine line and the family is finite
(image of `T.offDiag`). For each such line L, the ordered pairs of distinct points of
T ∩ L form `(T.filter (· ∈ L)).offDiag`, of size k(k−1). Two distinct points of a line span
that line (`line_pair_eq`), so these offDiag sets are pairwise disjoint for distinct lines,
and their union sits inside `T.offDiag`, of size n(n−1). Hence #lines · k(k−1) ≤ n(n−1) for
every admissible set, and the bound passes to the `sSup` over ℕ via `csSup_le'` and
`Nat.le_div_iff_mul_le`. The no-(k+1)-collinear hypothesis is not needed. Definitions
(`NonCollinearFor`, `linesWithPointsFor`, `numLinesWithPointsMax`) are restated verbatim
with targeted imports.

Axioms: `propext, Classical.choice, Quot.sound`
