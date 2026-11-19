# erdos263_sde

- Statement: `Erdos263.erdos_263.variants.super_doubly_exponential_eventual` (category research solved), source `FormalConjectures/ErdosProblems/263.lean:137`.
- Proof file: `results/erdos263_folk.lean`. It contains this theorem together with `erdos_263.variants.folklore`, which it uses, and it is identical to `work/erdos263_folk.lean`.

Proof idea: let y_n = log a_n. The hypothesis gives y_{n+1} ≥ log c + (2+ε) y_n. Since a is strictly increasing, a_n ≥ n, so y_n eventually exceeds Y0 = 2|log c|/ε + 1. From then on y_{n+1} ≥ (2 + ε/2) y_n, so y_n/2^n grows at least like (1 + ε/4)^n and tends to ∞. Any b with a_n/b_n → 1 eventually has b_n > a_n/2. Then log b_n / 2^n ≥ y_n/2^n − 1 → ∞, so b_n^{1/2^n} = exp(log b_n / 2^n) → ∞, and the folklore theorem (proved in the same file) gives that Σ 1/b_n is irrational.

Axioms: `'Erdos263.erdos_263.variants.super_doubly_exponential_eventual' depends on axioms: [propext, Classical.choice, Quot.sound]` (folklore: the same).

Date: 2026-11-12. 2 compile attempts for this theorem: (1) `field_simp` already closed a goal, and `tendsto_atTop_mono'` takes the filter explicitly; (2) clean.
