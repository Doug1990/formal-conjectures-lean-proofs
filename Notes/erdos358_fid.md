# Erdos358.f_id

- Source: `FormalConjectures/ErdosProblems/358.lean:66` (category textbook)
- Statement: `f id = fun n ↦ #{d ∈ n.divisors | Odd d}` (number of ways to write n as a sum of consecutive positive integers = number of odd divisors).

Proof idea: for n = 0 the representation set is infinite (every (u, v) with u > v > 0 gives an empty sum), so `Nat.card` is 0, matching `divisors 0 = ∅`. For n > 0, Gauss's formula gives 2·Σ_{i=u}^{v} i = (v−u+1)(u+v). The two factors have opposite parity and the length is the smaller one. The map φ(d) = ((|d − 2n/d| + 1)/2, (d + 2n/d − 1)/2) sends an odd divisor d to a representation. It is injective because the sum and |difference| of {d, 2n/d} determine the pair, and d is its odd member. It is surjective because the odd factor of (v−u+1)(u+v) = 2n is an odd divisor of n. All arithmetic side goals are closed by `omega`.

Axioms: `'Erdos358.f_id' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29. Compiles: 3 (1: missing imports / `open Filter`; 2: `le_or_lt` unknown; 3: clean).
