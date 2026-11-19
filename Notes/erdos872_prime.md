# Erdos872.erdos_872.variants.prime_question

- Source: `FormalConjectures/ErdosProblems/872.lean:206` (category research solved)
- Statement: for n ≥ 2, every maximal primitive subset A of {2..n} has at least π(n) elements.

Proof idea: for each prime q ≤ n let P(q) = q^(log_q n) be the largest power of q that is ≤ n.
P(q) lies in {2..n}, so maximality of A gives some a ∈ A with a ∣ P(q) or P(q) ∣ a (otherwise
A ∪ {P(q)} would still be primitive). Choose such an a = f(q). f is injective. If one a were
comparable with P(q) and P(r) for distinct primes q < r, then: both dividing a is impossible,
because q^k·r^m ≥ q^(k+1) > n ≥ a; a dividing both forces a = 1; and the mixed cases force
r ∣ q or q ∣ r. So `Finset.card_le_card_of_injOn` gives π(n) ≤ |A|. This is the forum argument
quoted in the docstring. IsPrimitive is restated locally with the same definition, and targeted
imports are used.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-08 (2 compiles)
