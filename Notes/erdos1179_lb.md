# Erdos1179.erdos_1179.variants.lower_bound

- Source: `FormalConjectures/ErdosProblems/1179.lean:97` (category research solved; the docstring calls it trivial)
- Statement: if 0 < ε < 1 and A ⊆ G is ε-balanced, then |G| ≤ 2^|A|.
- Date: 2026-11-09

Proof idea: if some g had repCount A g = 0, balance would give 2^|A|/|G| ≤ ε·2^|A|/|G| with
2^|A|/|G| > 0, which contradicts ε < 1. So every g ∈ G is a subset sum of A. Then univ ⊆ the image of
A.powerset under S ↦ Σ S, and |G| ≤ |A.powerset| = 2^|A|. The definitions are restated locally,
and the imports are targeted.

Axioms: `'Erdos1179.erdos_1179.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
