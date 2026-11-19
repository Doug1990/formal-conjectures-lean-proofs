# Erdos459.erdos_459 and Erdos459.erdos_459.variants.upper_tight

Source: FormalConjectures/ErdosProblems/459.lean:50 and :57 (category research solved).

Proof idea: f u = sInf {v | u < v ∧ primeFactors v ⊆ primeFactors u}. Because primeFactors (u²) = primeFactors u and u < u² for u ≥ 2, u² is in the set. So the set is nonempty, f u lies in it, and f u ≤ u². f u ≠ u+1, because the prime minFac(u+1) would divide both u and u+1, and so it would divide 1. That gives u+2 ≤ f u. For a prime p, every v in the set has only the prime factor p, so v = p^k (`Nat.eq_prime_pow_of_unique_prime_dvd`). From p < p^k we get k ≥ 2, so v ≥ p². The def `f` is restated locally, and the imports are targeted (no FormalConjecturesUtil).

Axioms (both theorems): [propext, Classical.choice, Quot.sound]

Date: 2026-11-08
