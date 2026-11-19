# erdos690_dens

- Statement: `Erdos690.erdos_690.variants.hasDensity` (category research solved)
- Source: FormalConjectures/ErdosProblems/690.lean:71
- Proof idea: whether n ≥ 1 lies in `kthPrimeFactorSet k p` depends only on which primes q ≤ p divide n. Every such q divides p!, so for n ≥ 1, membership is invariant under n ↦ n + p!. The point 0 is never in the set. If p! is not in the set, the set is fully periodic with period p!. Otherwise, insert 0 S is periodic. A periodic set has a density (the `P.per_dens` lemma, reused from results/erdos697.lean), and adding the point 0 changes the partial density only by 1/N → 0 (`P.dens_insert`). `kthPrimeFactorSet` and `Set.HasDensity`/`partialDensity` are restated locally. The only compiler message is an unused-variable lint for `hk`, which is part of the original statement.
- Axioms: `'Erdos690.erdos_690.variants.hasDensity' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-11 (1 compile)
