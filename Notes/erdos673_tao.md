# Erdos673.erdos_673.variants.tao

- Source: `FormalConjectures/ErdosProblems/673.lean`, line 77 (category textbook)
- Statement: for n > 0, m > 1, m ∣ n: τ(n/m)/m ≤ G(n) ≤ τ(n), where G(n) = Σ d_i/d_{i+1} over consecutive divisors.

Proof idea: rewrite the `Fin` sum as a sum over `range (τ(n) - 1)` (the index `(i + 1)` elaborates to `↑i + 1`, so there is no wrap-around). Upper bound: each ratio d_i/d_{i+1} is ≤ 1 by monotonicity of `Nat.nth` on the finite divisor set, and there are τ(n) - 1 terms. Lower bound: for every divisor e of n/m, both e and e·m divide n, so with i = `Nat.count (· ∣ n) e` we get d_i = e and d_{i+1} ≤ e·m (because `count` is monotone and e+1 ≤ e·m). That term is therefore ≥ 1/m, and i + 1 < τ(n). The map e ↦ count e is injective on divisors, so summing over its image gives τ(n/m)/m ≤ G(n), since all terms are nonnegative.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29
