# erdos835_comp

- Statement: `Erdos835.johnson_chromaticNumber_composite` (k > 2, k+1 composite ⇒ k+1 < χ(J(2k,k))), category research solved (Ma–Tang).
- Source: `FormalConjectures/ErdosProblems/835.lean:142` in the checkout.
- Date: 2026-11-14.

## Proof idea
Assume there is a proper (k+1)-colouring. The k+1 k-subsets of any (k+1)-set A pairwise meet in k−1 elements, so they form a clique and get all k+1 colours, each exactly once. In particular colour class 0 contains exactly one k-subset of every (k+1)-set. Let p = minFac(k+1) < k+1, so k+1 = pq, and let V be any (k+p)-subset of the 2k points. Double count the pairs (B ⊂ A ⊆ V) with |A| = k+1 and B of colour 0. Each A has one B, and each B ⊆ V lies in exactly p such A. So p ∣ C(k+p, k+1) = C(pq+p−1, p−1). But Lucas's theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) gives C(pq+p−1, p−1) ≡ C(p−1,p−1)·C(q,0) = 1 (mod p), a contradiction. The `Nat.Composite` abbrev and the Johnson graph are restated locally from FormalConjecturesForMathlib, with targeted Mathlib imports.

## Axioms
`'Erdos835.johnson_chromaticNumber_composite' depends on axioms: [propext, Classical.choice, Quot.sound]`
