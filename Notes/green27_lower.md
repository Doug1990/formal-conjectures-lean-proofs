# Green27.green_27.variants.previous_lower

- Source: `FormalConjectures/GreensOpenProblems/27.lean:114` (category research solved, Straus 1976)
- Statement: `(fun p ↦ Real.log (p : ℝ)) =O[primesAtTop] m`, where `m p` is the least size of a set
  `A ⊆ ZMod p` with `|A| ≥ 2` and no unique (unordered-pair) representation in `A + A`.
- Definitions `allUniqueSums`, `HasNoUniqueRepresentation`, `m`, `primesAtTop` restated verbatim
  (FormalConjecturesUtil is not built locally); targeted Mathlib imports.

**Proof idea.** Straus's dilation argument. If `A ⊆ ZMod p` is nonempty with no unique sums and
`4^|A| < p`, pigeonhole the `4^|A| + 1` dilations `t ∈ [0, 4^|A|]` by the vector of buckets
`⌊4·val(t a)/p⌋`; two of them, `t ≠ t'`, agree, so `u = t − t' ≠ 0` maps every `a ∈ A` to a
residue with an integer lift `d(a)` of absolute value `< p/4`. Sums of lifts then do not wrap
around mod `p`, so the element `M` maximizing `d` makes `M + M` a unique sum (via `u` being a
unit), a contradiction. Hence `p ≤ 4^|A|`, i.e. `|A| ≥ log p / log 4`. For `p ≥ 3` the whole
group `ZMod p` has no unique sums, so the defining set is nonempty and `le_csInf` gives
`m p ≥ log p / log 4`, which is the `IsBigO` bound with constant `log 4`.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-31
