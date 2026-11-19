# erdos507_ut

- Statement: `Erdos507.erdos_507.variants.upper_trivial` (α(n) ≪ 1/n, Heilbronn triangle problem, trivial upper bound), source `FormalConjectures/ErdosProblems/507.lean:103` (category research solved).
- Proof idea: let m = ⌊(n−3)/2⌋ and put each point p of the unit disk into the bucket ⌊(p₀+1)m/2⌋ ∈ {0,…,m}. Since n > 2(m+1), pigeonhole puts three distinct points a, b, c into one bucket, so their x-coordinates differ by at most 2/m. All y-coordinates lie in [−1,1], and area = |(a₀−c₀)(b₁−c₁) − (b₀−c₀)(a₁−c₁)|/2 ≤ 4/m ≤ 56/n for n ≥ 7. So minTriangleArea S ≤ 56/n for every admissible S, which gives 0 ≤ α n ≤ 56/n (`Real.sSup_le`, `Real.sSup_nonneg`) and the IsBigO bound with constant 56. The statement uses `≪`, which unfolds to `IsBigO atTop`, and that is written out here. `ℝ²`, the orientation instance, `triangle_area` and `triangle_area_eq_det` are copied verbatim from FormalConjecturesForMathlib/Geometry/2d.lean (targeted imports).
- Axioms: `'Erdos507.erdos_507.variants.upper_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-12
