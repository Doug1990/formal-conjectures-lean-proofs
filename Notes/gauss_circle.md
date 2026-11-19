# GaussCircleProblem.error_le

- Source: `FormalConjectures/Wikipedia/GaussCircleProblem.lean:68` (category research solved; Gauss's bound |E(r)| ≤ 2√2·π·r for large r, Hardy [Ha59]).
- File: `results/gauss_circle.lean` (targeted imports, `N` and `E` restated verbatim, `ℝ²` as a local notation, statement unchanged).

**Proof idea.** Gauss's square-counting argument with slack 1 in place of √2/2. The half-open unit squares Q(p) centred at lattice points are pairwise disjoint and measurable. Each has volume 1, via `PiLp.volume_preserving_ofLp` and `Real.volume_pi_Ico`. Every point of Q(p) is within distance 1 of p. So the union of Q(p) over the (finite) lattice points in the closed disk of radius r lies in the disk of radius r+1. It also contains the disk of radius r−1: send x to p = (⌊x₀+½⌋, ⌊x₁+½⌋). With `EuclideanSpace.volume_closedBall_fin_two` and `measure_biUnion_finset` this gives π(r−1)² ≤ N(r) ≤ π(r+1)² for r ≥ 1. Hence |E(r)| ≤ π(2r+1), which is at most 2√2πr once r ≥ 2 (uses √2 > 7/5). Reusable: `bounds`, `Q`/`vol_Q`/`Q_inj`/`close`, `S_finite`, `d2` (dist in ℝ² as a square root).

**Axioms:** `'GaussCircleProblem.error_le' depends on axioms: [propext, Classical.choice, Quot.sound]`

**Date:** 2026-10-31. Compiles: 3 (1: two small errors, `simp` left `ofReal (2⁻¹+2⁻¹)^2` and a `sq` rewrite mismatch; 2: only lint about an unused `first` fallback; 3: clean + axioms).
