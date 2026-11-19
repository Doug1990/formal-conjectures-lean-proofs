# Erdos316.erdos_316.variants.generalized

- Source: `FormalConjectures/ErdosProblems/316.lean:84` (category research solved)
- Statement: for every n ≥ 2 there is a finite A ⊆ ℕ∖{0,1}, A nonempty, with Σ_{a∈A} 1/a < n,
  such that every partition of A into at most n parts has a part with reciprocal sum ≥ 1.

**Proof idea.** Choose A with all elements dividing L and Σ_{a∈A} L/a = nL − 1, so the sum of
reciprocals is n − 1/L < n. Every part has a reciprocal sum in (1/L)ℤ, so a part with sum < 1 has
sum ≤ (L−1)/L, and ≤ n such parts give a total ≤ n − n/L < n − 1/L, a contradiction (`no_split`).
Construction (`construct`): let K be the largest number with Σ_{k=2}^K 1/k < n (it exists since the
harmonic series diverges, via `log_le_harmonic_floor`), and L = (K+1)!. Take {2,…,K}. The remaining
amount r = nL − 1 − Σ_{k≤K} L/k is ≤ K!, so by `rep` (from results/erdos18_upper.lean) r is a sum of
distinct divisors e of K!. Add the elements L/e ≥ K+1 (disjoint from {2,…,K}, with L/(L/e) = e).

- Axioms: `[propext, Classical.choice, Quot.sound]`
- Compiles: 2 (1st: only unused-simp-arg lints; 2nd: clean + axioms). Targeted imports, fast.
- Date: 2026-11-08
