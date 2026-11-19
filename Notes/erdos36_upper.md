# erdos36_upper

- Statement: `Erdos36.minimum_overlap.variants.upper.erdos_1955` (category research solved)
- Source: `FormalConjectures/ErdosProblems/36.lean:321` in the checkout
- Statement: `atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2`

Proof idea: Erdős' construction. Take A = the middle block {⌊n/2⌋+1, …, ⌊n/2⌋+n} and B = the two
outer blocks {1, …, ⌊n/2⌋} ∪ {⌊n/2⌋+n+1, …, 2n}. They partition [1, 2n] and both have n elements.
For a difference k > 0, every pair (a, b) with a − b = k has b in the left block, and for k ≤ 0 it
has b in the right block. Since b determines the pair, each overlap is at most ⌈n/2⌉, so
2·M(n) ≤ n + 1. For ε > 0 this gives M(n)/n ≤ 1/2 + ε once n·ε > 1. `limsup_le_of_le` (the quotient
is ≥ 0, so cobounded) and `le_of_forall_pos_le_add` finish the proof. Definitions are restated
locally; targeted Mathlib imports.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
