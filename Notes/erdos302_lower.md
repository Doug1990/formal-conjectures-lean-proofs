# Erdős 302: Cambie's 5/8 lower bound and parts.ii

- Statements: `Erdos302.erdos_302.variants.lower_five_eighths` (research solved) and
  `Erdos302.erdos_302.parts.ii` (research solved), source
  `FormalConjectures/ErdosProblems/302.lean` (lines 126 and 75) in the checkout.
- Proof idea: Cambie's set A = {odd x with 4x ≤ N} ∪ (N/2, N] contains no distinct triple with
  1/a = 1/b + 1/c, i.e. bc = a(b+c). If a > N/2, then 2bc ≤ N(b+c) < 2a(b+c), which is impossible.
  If a is odd and small and b (or c) is odd, a parity check on bc = a(b+c) fails. If a is small and
  both b and c are large, then 4bc = 4a(b+c) ≤ N(b+c) < 4bc. The two pieces are disjoint, and their
  sizes give 5N ≤ 8|A| + 16, so f(N) ≥ (5/8 − ε)N once N > 2/ε. parts.ii follows: with ε = 1/16
  we get f(N)/N ≥ 9/16 eventually, so the limit cannot be 1/2 (`ge_of_tendsto`).
  Distinctness is not even needed.
- Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`
- Definitions restated locally (FormalConjecturesUtil is not built); `@[category]` attributes dropped.
- Date: 2026-11-01
