# Green32.green_32.variants.dirichlet_regime

- Source: `FormalConjectures/GreensOpenProblems/32.lean:128` (category research solved;
  "basically Dirichlet's lower bound for Bohr sets" [Gr24])
- Statement: `∃ c > 0, ∀ ω, (∀ᶠ p, 101 ≤ ω p ∧ ω p ≤ c log p) → HasLargeGapDilate ω`.
- Definitions `HasGap`, `HasLargeGapDilate` restated verbatim; targeted Mathlib imports.

**Proof idea.** Take `c = 1/log 203`. Then `k = ⌊ω p⌋ ≥ 101` satisfies `203^k ≤ p`, hence
`202^k < p` and `ω p < k + 1 ≤ p`. Core lemma: if `202^|A| < p`, pigeonhole the dilations
`t ∈ [0, 202^|A|]` by the bucket vector `⌊202·val(t a)/p⌋`; two of them `t ≠ t'` coincide, and
`u = t − t'` is a unit with `u·a ≡ d(a)`, `|d(a)| < p/202` for all `a ∈ A`. So `u·A` avoids the
residues `s, s+1, …, s+L−1` with `s = ⌊p/202⌋ + 1` as soon as `101 L ≤ 100 p` (a hit would give
`p ∣ s + i − d(a)` with `0 < s + i − d(a) < p`). Finally `L = ⌊100p/ω p⌋ ≤ 100p/101`.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-31
