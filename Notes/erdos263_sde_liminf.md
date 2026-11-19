# erdos263_sde_liminf

- Statement: `Erdos263.erdos_263.variants.super_doubly_exponential` (research solved)
- Source: `FormalConjectures/ErdosProblems/263.lean:121` in the checkout
- Proof file: `results/erdos263_folk.lean` (this file also holds `folklore` and `super_doubly_exponential_eventual`, which this proof uses)

Proof idea: let l be the liminf, with l > 0. The ratios a(n+1)/a(n)^(2+ε) are nonnegative, so the sequence is bounded below and `Filter.eventually_lt_of_lt_liminf` applies. It gives l/2 < a(n+1)/a(n)^(2+ε) eventually. Multiplying out gives the eventual bound (l/2)·a(n)^(2+ε) ≤ a(n+1). The previously proved `super_doubly_exponential_eventual` (with c = l/2) then gives the result. It in turn reduces to the folklore criterion a(n)^(1/2^n) → ∞.

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-12
