# erdos1193

- Statements: `Erdos1193.erdos_1193.parts.i`, `erdos_1193.parts.ii`, `erdos_1193.variants.sumRep_univ`, `erdos_1193.variants.upper_density_pos` (all research solved)
- Source: `FormalConjectures/ErdosProblems/1193.lean` (lines 47, 64, 73, 80) in the checkout

Proof idea: these are trivial, as the docstring itself says. For A = ℕ, every pair in the antidiagonal of n counts, so sumRep ℕ n = n + 1. Take g n = n + 1, which is monotone and positive. Then {n | sumRep A n = g n} = ℕ, whose partial density is eventually 1. So its lower and upper densities are both 1 (`Tendsto.liminf_eq` / `limsup_eq`), and this refutes parts i and ii and proves upper_density_pos. The file restates the needed FormalConjecturesForMathlib definitions (partialDensity, upper/lowerDensity, indicatorOne, sumConv, sumRep) verbatim, so it can use targeted Mathlib imports. Note that Erdős presumably meant extra restrictions, so the formal statements are much weaker than the intended problem.

Axioms (all four): [propext, Classical.choice, Quot.sound]

Date: 2026-11-12
