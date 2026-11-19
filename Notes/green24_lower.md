# green24_lower

- Statement: `Green24.variants.lower_HL` (`gamma ≥ 1/12`), category research solved
- Source: `FormalConjectures/GreensOpenProblems/24.lean:87`
- Date: 2026-10-31

Proof idea: take A = {0, …, n−1} with n = 12m. Every pair (x, d) with 0 ≤ x < 6m and 1 ≤ d ≤ 2m gives a
counted pair (x, x+d), because x + 3d < 12m. The map is injective, so max013AffineTranslates(12m) ≥ 12m²
= n²/12. The ratio is ≥ 1/12 along n = 12m (frequently), and it is bounded by 1 (trivial n² bound), so
`le_limsup_of_frequently_le` applies. Note: the formalisation counts translates with negative d too, so
intervals actually give ≈ n²/3. The bound 1/12 is far from tight but it is exactly what is stated.

Axioms: `'Green24.variants.lower_HL' depends on axioms: [propext, Classical.choice, Quot.sound]`
