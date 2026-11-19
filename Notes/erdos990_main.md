# Erdos990.erdos_990 (main statement, disproof)

- Source: `FormalConjectures/ErdosProblems/990.lean:79` (category research solved, APSSV26b)
- Lean file: `results/erdos990_ce.lean` (the same file as the counterexample variant, which it uses)

Proof idea: assume there is a constant C. Take N = ⌈3C²⌉ and the counterexample polynomial f with
n = N+2 terms, M f < 3 and a positive real root x of multiplicity N+1 (variants.counterexample).
Choose α = β = 0. The density term vanishes, and arg x = 0, so `rootArgCount f {0}` is at least
the multiplicity N+1 (via `replicate (mult) x ≤ roots` and `Multiset.countP_le_of_le`). Since
0 ≤ M f < 3 we get log M f ≤ 3, so N+1 ≤ |C|·√(3(N+2)). Squaring gives (N+1)² ≤ 3C²(N+2) ≤ N(N+2),
a contradiction.

Axioms: `'Erdos990.erdos_990' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-13
