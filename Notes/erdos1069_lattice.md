# erdos1069_lattice

- Statement: `Erdos1069.erdos_1069.variants.lattice` (category textbook)
- Source: `FormalConjectures/ErdosProblems/1069.lean`, line 75
- Date: 2026-10-29

Proof idea: take the m×m grid P(i,j) = i·e₀ + j·e₁ (0 ≤ i,j < m); P is injective, so the grid has m² points.
The m rows (affine subspaces through P(0,j) with direction span{e₀}) and the m columns (through P(i,0) with
direction span{e₁}) are lines (direction of finrank 1) with m grid points each, so they are m-rich. Rows are pairwise
distinct (compare the y-coordinate of P(0,j)), columns likewise, and no row is a column (a row contains P(0,j) and
P(1,j), which have different x-coordinates). This gives 2m m-rich lines. `ncard` needs finiteness of the set of
m-rich lines: for m ≥ 2 each such line equals line[a,b] for two distinct points of s (`line_pair_eq`, copied from
Erdos211), so it lies in the image of `s.offDiag`. The statement's `IsLine`, `richLines` and the `ℝ²` notation
are restated locally (same definitions as in FormalConjecturesForMathlib/Geometry/2d.lean and the source file).

Axioms: `'Erdos1069.erdos_1069.variants.lattice' depends on axioms: [propext, Classical.choice, Quot.sound]`
