# mo17560_all_nats

- Statement: `Mathoverflow17560.mathoverflow_17560.variants.all_nats` (category textbook)
- Source: `FormalConjectures/Mathoverflow/17560.lean:43` in the checkout
- Statement: if `(n : ℝ) ^ x` is a natural number for every `n : ℕ`, then `x` is a natural number.

Proof idea: suppose `x ∉ ℕ` and let `k = ⌊x⌋₊ + 1 > x`. The `k`-th forward difference `D k f n`
(defined recursively as `D (k+1) f = D k (f(·+1) − f)`) of `f(s) = s ^ x` at a natural `n`
is an integer, because all `f(n+m)` are integers (`D_int`). An iterated mean value theorem
(`D_mvt`, proved by induction on `k` for a family `h_i` with `h_i' = h_{i+1}`, applied to
`h_i(s) = x(x−1)…(x−i+1) s^(x−i)`) gives `D k f n = c_k ξ^(x−k)` with `ξ ≥ n` and
`c_k = ∏_{j<k}(x−j) ≠ 0`. As `x − k < 0`, this is nonzero and tends to `0`, so for
large `n` it is an integer of absolute value in `(0, 1)`. Contradiction.

Axioms: `propext, Classical.choice, Quot.sound`

Compiled 2026-11-18 (3 compiles). Imports are targeted Mathlib modules (not `FormalConjecturesUtil`).
results/mo17560_all_nats.lean is identical to work/mo17560_all_nats.lean.
