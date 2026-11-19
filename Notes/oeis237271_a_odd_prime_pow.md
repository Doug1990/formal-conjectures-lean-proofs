# OeisA237271.a_odd_prime_pow

- Source: FormalConjectures/OEIS/237271.lean:141 (category research solved)
- Statement: for an odd prime p, a(p^k) = k + 1.
- Proof idea: `Nat.divisors_prime_pow` writes the divisors as the image of range (k+1) under i ↦ p^i, which is strictly monotone, so `StrictMonoOn.map_finsetSort` + `Finset.sort_range` give the sorted list [1, p, …, p^k]. The consecutive pairs are (p^i, p^(i+1)) for i < k. Every one is counted, since p^(i+1) is odd and p^(i+1) = p^i·p ≥ 2p^i because p ≥ 3. So `List.countP_eq_length` makes the count equal to the zip length k.
- Axioms: propext, Classical.choice, Quot.sound
- Date: 2026-11-06 (1 run, 2 compiles)
- The definition `a` is restated verbatim; targeted imports, no FormalConjecturesUtil.
