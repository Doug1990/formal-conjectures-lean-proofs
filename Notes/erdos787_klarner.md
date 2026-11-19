# erdos787_klarner

- Statement: `Erdos787.erdos_787.variants.klarner` (g(n) ≫ log n), checkout file `FormalConjectures/ErdosProblems/787.lean:112`, category research solved (Klarner).
- Date: 2026-11-12

## Proof idea
Take the positive part P of A (or the positive part of −A, whichever has at least (n−1)/2 elements). Choose elements greedily from the top down: the next element s is the largest element of P that lies below all chosen ones and has s + c ∉ A for every chosen c. Admissibility of all pairs is then automatic. To show a choice always exists, use the potential S = Σ_{c chosen} #{a ∈ A : a ≥ c}. Every element that is not admissible lies in ⋃_c ({a ≥ c} ∪ ({a ≥ c} − c)), so there are at most 2S of them, and #{a ≥ s} ≤ 2S + 1. Hence 2S + 1 ≤ 3^k after k steps (`KL.grow`), and |P| ≥ 3^k gives k admissible elements. Taking k = log₉ n − 1 gives g(n) ≥ log n / (4 log 3) for n ≥ 729. The definitions `g`, `le_g` and `disjoint_restrictedSumset_iff` are copied verbatim from the checkout, and `Finset.restrictedSumset` is a local copy because the file uses targeted Mathlib imports.

## Axioms
'Erdos787.erdos_787.variants.klarner' depends on axioms: [propext, Classical.choice, Quot.sound]
