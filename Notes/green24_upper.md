# green24_upper

- Statement: `Green24.variants.upper_HL` (`gamma ≤ 3/4`), category research solved
- Source: `FormalConjectures/GreensOpenProblems/24.lean:82`
- Date: 2026-10-31

Proof idea: a counted pair (x, y) gives the triple x, y, w = 3y − 2x, with y strictly between x and w.
Pick a median threshold t, so that ⌊n/2⌋ elements of A are ≤ t (via a discrete intermediate value lemma).
If y ≤ t, the endpoint below y is also ≤ t. Map (x, y) ↦ (x, y) when x < y and to (y, w) otherwise. This
is an injection into L × L (the order of each image pair records which case it came from). The case y > t
works the same way with U × U. Hence 2·#T ≤ 2(⌊n/2⌋² + ⌈n/2⌉²) ≤ n² + 1, so the ratio is ≤ (n²+1)/(2n²)
≤ 3/4 for n ≥ 2. This in fact gives γ ≤ 1/2. Coboundedness of the limsup comes from nonnegativity.

Axioms: `'Green24.variants.upper_HL' depends on axioms: [propext, Classical.choice, Quot.sound]`
