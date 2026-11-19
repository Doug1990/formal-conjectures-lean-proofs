# Erdos682.erdos_682.variants.dickson_counterexample

- Source: FormalConjectures/ErdosProblems/682.lean:76 (category textbook)

Proof idea: each of 2184, …, 2200 has a prime factor r ≤ 13, and r ∣ 30030, so r also divides 2183 + 30030d + k for 1 ≤ k ≤ 17 (case split with `interval_cases`, divisibility by `omega`). So none of those numbers is prime, and the minFac of each is ≤ 13 < 18 = p(n+1) − p(n). With n = count Prime (2183 + 30030d), `Nat.nth_count` gives p n = 2183 + 30030d. `Nat.count_add` plus the fact that the only prime in [q, q+18) is q gives count(q+18) = n + 1, so p(n+1) = 2201 + 30030d.

Axioms: `'Erdos682.erdos_682.variants.dickson_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
