# Erdős 1136: complete chain (4 statements)

- Source: `FormalConjectures/ErdosProblems/1136.lean` in the checkout
  - `Erdos1136.erdos_1136` (:52, research solved)
  - `Erdos1136.erdos_1136.variants.multiples_of_three` (:60, research solved)
  - `Erdos1136.erdos_1136.variants.mueller` (:70, research solved)
  - `Erdos1136.erdos_1136.variants.upper_bound` (:79, research solved)
- Verified file: `work/erdos1136.lean`. `results/erdos1136.lean` is a hand copy of it.
- The statements are unchanged. `partialDensity`, `lowerDensity` and `HasDensity` are restated from
  FormalConjecturesForMathlib/Data/Set/Density.lean, because the file uses targeted Mathlib imports
  (FormalConjecturesUtil is not built here).

## Proof idea
Generic lemma `dens_of_sq`: if (#(S ∩ [0,N)) − αN)² ≤ K·N for all N ≥ 1, then S has density α.
- Multiples of 3: there are exactly ⌈N/3⌉ multiples of 3 below N. A sum of two multiples of 3 is not 2^k.
- Müller's set M = {n : odd part of n ≡ 3 mod 4}. Its members are characterised by: n ≡ 3 mod 4 ⇒ in M,
  n ≡ 1 mod 4 ⇒ not in M, and 2n ∈ M ↔ n ∈ M. These give the count recursion C(N) = ⌊N/4⌋ + C(⌈N/2⌉),
  so |C(N) − N/2| ≤ k+1 for N ≤ 2^k, which yields an error² ≤ 8N.
- Avoidance for M uses induction on k: two odd members are ≡ 3 mod 4, so their sum is ≡ 2 mod 4 and ≥ 6.
  Mixed parity gives an odd sum. Two even members halve to members.
- `erdos_1136` follows from the density 1/2 via `Tendsto.liminf_eq`.
- The upper bound uses x ↦ x for x < 2^k and x ↦ 2^(k+1) − x otherwise. This is injective on A ∩ [0, 2^(k+1)),
  because x + y = 2^(k+1) and 2x = 2^(k+1) are excluded. So the partial density at 2^(k+1) is ≤ 1/2, and
  `liminf_le_of_frequently_le` finishes.

## Axioms
All four theorems: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
