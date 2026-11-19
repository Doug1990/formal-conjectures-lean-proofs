# Erdos367.erdos_367.variants.k_le_two

- Source: `FormalConjectures/ErdosProblems/367.lean:69` (category research solved; the docstring calls it trivial, per van Doorn)
- Date: 2026-11-10
- Verified file: `work/erdos367_k2.lean` (results copy is identical). `B` is restated verbatim.

Proof idea: B r m is a sub-product of the prime-power factorisation of m, so B r m ∣ m (`B_dvd`). For k ≤ 2 and n ≥ 1, every factor in the window [n, n+k) is ≤ n+1, so the product is ≤ (n+1)^k ≤ (n+1)² ≤ 4n². `IsBigO.of_bound 4` then finishes, with `Real.rpow_two`.

Axioms: `'Erdos367.erdos_367.variants.k_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]`
