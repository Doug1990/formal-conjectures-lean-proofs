# Green31.green_31.variants.upper_li69

- Source: `FormalConjectures/GreensOpenProblems/31.lean:110` (category research solved, Lindström)
- Statement: ∃ C, eventually F N ≤ √N + N^{1/4} + C, where F N is the largest Sidon subset of [1, N].

Proof idea: this reuses the erdos30_lindstrom argument with C = 1. The sharp energy bound E(S, [0, m]) ≤ k(m+1) + (m+1)m together with the Cauchy–Schwarz bound gives k²(m+1) ≤ (N+m)(k+m). With m + 1 = ⌈N^{3/4}⌉ and q = N^{1/4}, a quadratic positivity argument at x₀ = q² + q + 1 gives k ≤ √N + N^{1/4} + 1 for every N.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-10-31 (1 compile; the .lean file was copied to results/ in the next run with the Write tool)
