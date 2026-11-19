# erdos678_fin

- Statement: `Erdos678.erdos_678.variants.not_infinitely_many_pairs`
- Source: formal-conjectures/FormalConjectures/ErdosProblems/678.lean, line 104 (category research solved)
- Date: 2026-11-16

## Proof idea
We show that for EVERY k only finitely many pairs (m, n) satisfy n + k ≤ m and M(m, k+1) < M(n, k), where M(n, k) = lcm(n+1, …, n+k). That refutes "eventually infinite".

- Upper bound: M(n, k) divides the product of the k numbers, so M(n, k) ≤ (n+k)^k ≤ m^k.
- Lower bound: lcm(L, x)·gcd(L, x) = L·x, and gcd(M(m, j), m+j+1) divides ∏_i gcd(m+i, m+j+1). Each factor divides a difference ≤ j, so the gcd is ≤ j^j. Induction then gives (m+1)^j ≤ M(m, j)·c_j with c_j = ∏_{i<j} i^i.
- Combining: (m+1)·m^k ≤ (m+1)^(k+1) < c_{k+1}·m^k, so m + 1 < c_{k+1}, and n < m.

`lcmInterval` is restated locally from FormalConjecturesForMathlib (upstream it lives in namespace `Finset`, here at root level, same definition). Targeted Mathlib imports are used. The statement is unchanged.

## Axioms
'Erdos678.erdos_678.variants.not_infinitely_many_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
