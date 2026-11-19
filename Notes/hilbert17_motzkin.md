# Hilbert17.f_not_sum_of_squares

- Source: `FormalConjectures/HilbertProblems/17.lean:73` (category textbook, Motzkin)
- Statement: the Motzkin polynomial f = x⁴y² + x²y⁴ − 3x²y² + 1 is not a finite sum of squares of real polynomials.

Proof idea: this is a Newton polytope argument done with coefficients. Lemma `core`: let κ be an additive weight on monomials and m the κ-maximal monomial over the supports of all Sᵢ, with κ injective at the top. Then coeff_{2m}(Σ Sᵢ²) = Σ cᵢ(m)² > 0. Lemma `newton`: if Σ Sᵢ² has no monomials with w·m > 2K, then every monomial of every Sᵢ has w·m ≤ K. Ties are broken with κ = B·(w·m) + m₀, where B bounds all the exponents. This is applied with w = (−2,1), (1,−2), (1,1) and K = 0, 0, 3. So each Sᵢ is supported on {1, xy, x²y, xy²}. Then coeff_{x²y²}(Σ Sᵢ²) = Σ cᵢ(xy)² ≥ 0, which contradicts the coefficient −3 of f. Reusable: `core`, `newton`, `coord`, `coeff_f`.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-10-31 (2 compiles)
