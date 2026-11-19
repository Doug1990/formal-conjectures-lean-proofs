# Erdos350.erdos_350.variants.strengthening and Erdos350.erdos_350

- Source: `FormalConjectures/ErdosProblems/350.lean:87` (strengthening, Hanson–Steele–Stenger, research solved)
  and `:76` (erdos_350, Ryavec, research solved). The def `DecidableDistinctSubsetSums` is restated
  verbatim, and only targeted Mathlib imports are used.

## Proof idea
Sort A as a_0 < … < a_{k−1} via `orderEmbOfFin`. Then 0 ∉ A, since {0} and ∅ have the same sum. The 2^j subsets of
the j smallest elements have distinct sums in [0, Σ_{i<j} a_i], so Σ_{i<j} a_i ≥ 2^j − 1 = Σ_{i<j} 2^i (the
partial sums dominate those of b_i = 2^i). A general weak-majorization lemma (HS.core) holds for φ convex and
antitone on (0,∞): write φ(a_i) − φ(b_i) = c_i (b_i − a_i), where c_i = −(chord slope of φ between a_i and q_i),
with q_i = b_i, or q_i = 2b_i = b_{i+1} when a_i = b_i. Then c_i ≥ 0 and c is antitone, by secant monotonicity
(`ConvexOn.secant_mono`, since a_i ≤ a_{i+1} and q_i ≤ b_{i+1} ≤ q_{i+1}). Abel summation against the
nonpositive partial sums of b − a gives Σφ(a_i) ≤ Σφ(2^i). With φ(x) = x^{−s}, which is convex because
exp(−s·log x) is exp convex over −s·log x, the geometric sum gives (1 − r^k)/(1 − r) < 1/(1 − r) with r = 2^{−s}.
erdos_350 is the case s = 1.

## Axioms
`'Erdos350.erdos_350.variants.strengthening' depends on axioms: [propext, Classical.choice, Quot.sound]`
`'Erdos350.erdos_350' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-14 (4 compiles)
