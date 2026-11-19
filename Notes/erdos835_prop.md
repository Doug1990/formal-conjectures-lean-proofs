# erdos835_prop (lives in results/erdos835_comp.lean)

- Statements: `Erdos835.property_iff_chromaticNumber` (835.lean:56, category test) and `Erdos835.johnsonGraph_18_9_chromaticNumber` (835.lean:88, research solved).
- Source: `FormalConjectures/ErdosProblems/835.lean` in the checkout.
- Date: 2026-11-14.

## Proof idea
For a (k+1)-set A, the k-sets strictly inside A are exactly `powersetCard k A`. There are k+1 of them and they pairwise meet in k−1 elements (CP.inter_card), so they form a clique of J(2k,k). Forward direction: a proper (k+1)-colouring is injective on this clique, so its image is all of Fin (k+1). Backward direction: if s, t are adjacent, then s ∪ t is a (k+1)-set. Property says the image of its k+1 k-subsets is all k+1 colours, so the colouring is injective there and c s ≠ c t, which gives (k+1)-colourability. A k-colouring is impossible because it would be injective on the clique, giving k+1 ≤ k. The equivalence goes through `chromaticNumber_eq_iff_colorable_not_colorable`. J(18,9) is the composite theorem at k = 9, since 10 is composite (`decide`).

## Axioms
`'Erdos835.property_iff_chromaticNumber' depends on axioms: [propext, Classical.choice, Quot.sound]`
`'Erdos835.johnsonGraph_18_9_chromaticNumber' depends on axioms: [propext, Classical.choice, Quot.sound]`
