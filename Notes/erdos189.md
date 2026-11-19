# erdos189

- Statements: `Erdos189.erdos_189` (rectangles, research solved, Kovač 2023) and
  `Erdos189.erdos_189.variants.square` (research solved, "easy to see" per Graham).
- Source: `FormalConjectures/ErdosProblems/189.lean` lines 56 and 67 in the checkout.
- Checkout definitions restated locally: `ℝ²` notation, the `Module.Oriented` / finrank instances,
  and `IsCcwConvexPolygon` (from FormalConjecturesForMathlib/Geometry/2d.lean), plus `Erdos189For`.

## Proof idea
View points as complex numbers and colour x by (⌊Re x²⌋ mod 8, ⌊Im x²⌋ mod 8), which gives 64 colours.
The three perpendicularity conditions force d = a + c − b. The degenerate case d = c is excluded
because the ccw-convexity condition needs sign ∡ b c d = 1. For any parallelogram, a² + c² − b² − d² = −2(a−b)(c−b),
so its squared modulus is 4·|a−b|²·|c−b|² = 4·area². If all four vertices share a colour, then the real
and imaginary parts of a²+c²−b²−d² each lie within 2 of a multiple of 8, so their squares are < 4 or > 36.
This rules out squared modulus 16, so no colour class contains a rectangle of area 2. The square
variant follows by weakening, since a square is a rectangle.

## Axioms
`'Erdos189.erdos_189' depends on axioms: [propext, Classical.choice, Quot.sound]`
`'Erdos189.erdos_189.variants.square' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-18. 2 compiles.
