# PierceBirkhoff.pierce_birkhoff_conjecture_dim_one

- Source: `FormalConjectures/Wikipedia/PierceBirkhoff.lean:101` (category research solved, Mahé)
- Verified work file: `work/pierce_birkhoff1.lean`. The copy here was written by hand from it and not compiled separately.
- Date: 2026-11-04

## Proof idea
Let Z be the finite set of points where two *different* piece polynomials g_i ≠ g_j agree. Near each point x,
the interval (x, x+ε) avoids Z. A connectedness argument (`isPreconnected_closed_iff` with the closed
sets "pieces carrying polynomial g_{i0}" and "the other pieces") shows that f equals a single piece polynomial R_x
on [x, x+ε], and likewise a polynomial L_x on [x−ε, x]. If x ∉ Z then L_x = R_x. So
h = f − Σ_{z∈Z} 1_{[z,∞)}·(R_z − L_z) is locally polynomial everywhere. A clopen argument on ℝ (two polynomials
that agree on an open set are equal) makes h one global polynomial. Each jump term has the form
1_{x≥z}·(x−z)·r(x). With a = (r+1)²/4 ≥ 0 and b = (r−1)²/4 ≥ 0 (so r = a − b), this term equals
max((x−z)a, 0) + min(−(x−z)b, 0). Finite sup-inf forms of polynomials are closed under addition (index
over products), so f is a finite sup of finite infs of polynomials. In dimension 1 the semi-algebraicity
hypothesis is not needed: closedness and finiteness of the cover suffice.

## Axioms
`'PierceBirkhoff.pierce_birkhoff_conjecture_dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]`
