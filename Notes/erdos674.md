# erdos674

- Statements: `Erdos674.erdos_674` (solutionSet.Nonempty) and `Erdos674.erdos_674.variants.infinite` (solutionSet.Infinite)
- Source: formal-conjectures/FormalConjectures/ErdosProblems/674.lean, lines 44 and 51 (category research solved)
- Date: 2026-11-16

## Proof idea
This is Ko's family of solutions of x^x y^y = z^z, rederived by hand. Fix n ≥ 2, N = 2^n, a = N − 1, k = N − 1 − n and W = 2^(2Nk)·a^(2a). Set x = N²W, y = a²W, z = 2NaW. All three are of the form 2^p·a^q, so x^x y^y = z^z reduces to two exponent identities: (2Nk+2n)N² + 2Nk·a² = (2Nk+n+1)·2Na and 2a·N² + (2a+2)a² = (2a+1)·2Na. After substituting a = n+k and N = n+k+1, both are polynomial identities, closed by `ring`. n = 2 gives the example 2^12·3^6, 2^8·3^8, 2^11·3^7 from the statement's docstring. Infinitude: x ≥ 2^n, so the first projections of the set are unbounded. `solutionSet` is restated locally with targeted Mathlib imports. The statement is unchanged.

## Axioms
'Erdos674.erdos_674' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos674.erdos_674.variants.infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
