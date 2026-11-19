# PartitionParity.kolberg

- Source: `FormalConjectures/Paper/PartitionParity.lean:68` (category research solved, Kolberg 1959)
- Statement: `{n | Even (partitionNumber n)}.Infinite ∧ {n | Odd (partitionNumber n)}.Infinite`
- `Nat.partitionNumber` restated locally exactly as in `FormalConjecturesForMathlib/Combinatorics/Enumerative/Partition/Basic.lean`.

Proof idea: over ZMod 2, Mathlib's partition generating function (`Nat.Partition.hasProd_powerSeriesMk_card_restricted` with the trivial predicate) times Euler's pentagonal product (`hasProd_one_sub_X_pow`) gives `P · E = 1`, where `E` has coefficient 1 exactly at generalized pentagonal numbers. Generalized pentagonal numbers below `pent(K)` are at most `pent(K) − (2K−1)` (lemma `gap`), so for any polynomial `B` with constant term 1 and degree ≤ N, `B·E` has coefficient 1 at `pent(K)` for all large K (lemma `key`). If p(n) were eventually even, take `B = P`; if eventually odd, take `B = (1+X)·P` (then `B·E = 1+X`). Both contradict `key`.

Axioms: `'PartitionParity.kolberg' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-01. 2 compiles.
