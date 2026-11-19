# OpenQuantumProblem35.ame_5_2_exists

- Source: `FormalConjectures/OpenQuantumProblems/35.lean:727` (category research solved; Scott 2004, the 5-qubit code state)
- Statement: `ExistsAME 5 2`
- Definitions restated verbatim from the source file; targeted Mathlib imports instead of FormalConjecturesUtil.

## Proof idea
Witness: the pentagon graph state, ψ(y) = (-1)^{Q(y)}/√32 with Q(y) = Σ y_i y_{i+1} (cyclic, mod 2).
For a permutation π the reduced density matrix on the first 2 parties only depends on the two
positions p = π⁻¹(0), q = π⁻¹(1): a `Finset.sum_bij'` (`bridge`) rewrites the sum over the
traced-out configuration z ∈ {0,1}³ as a sum over y ∈ {0,1}⁵ with y_p = a₀, y_q = a₁, pairing y
with y updated at p, q to (b₀, b₁). The resulting integer sign sums equal 8·[a = b] for all
20 ordered pairs (p, q) and all a, b (`core`, `decide +kernel`, fast). With amplitude² = 1/32
this gives (1/4)·I. Normalization: 32 amplitudes of squared norm 1/32.

## Axioms
`'OpenQuantumProblem35.ame_5_2_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

Verified file: work/ame52.lean (results copy written by hand from it, not compiled separately).
Date: 2026-11-05. Compiles: 3 (1 for the `core` test file work/ame52_core.lean, 2 for the full file).
