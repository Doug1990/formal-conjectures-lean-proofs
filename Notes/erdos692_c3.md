# erdos692_c3

- Statement: `Erdos692.erdos_692.variants.cambie_three` (δ₁(3,7) < δ₁(3,6) and δ₁(3,7) < δ₁(3,8))
- Source: `FormalConjectures/ErdosProblems/692.lean:104` (category research solved, Cambie)
- Date: 2026-11-17

## Proof idea
The set of x with exactly one divisor in (n, m) is L-periodic whenever every d in (n, m) divides L, because d ∣ x + L ↔ d ∣ x. A generic lemma (per_dens, adapted from erdos690_dens) shows that an L-periodic set has density #(S ∩ [0, L))/L. Uniqueness of limits then pins down any δ satisfying `IsDelta₁`. The three counts over one period are computed by kernel `decide` (no native_decide): 7 of 20 for (3,6), 20 of 60 for (3,7), and 152 of 420 for (3,8). This gives δ₁ = 7/20, 1/3 and 38/105, and `norm_num` finishes. `HasDensity`/`partialDensity` are restated locally from FormalConjecturesForMathlib/Data/Set/Density.lean, with the same definitions.

## Axioms
`'Erdos692.erdos_692.variants.cambie_three' depends on axioms: [propext, Classical.choice, Quot.sound]`
