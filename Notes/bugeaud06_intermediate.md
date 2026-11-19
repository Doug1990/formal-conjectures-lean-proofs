# Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary

- Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean:199` (category API)
- Date: 2026-10-30
- Compiles: 2 (1st: wrong namespace, `Real.isLittleO_log_rpow_atTop` → `isLittleO_log_rpow_atTop`)

Proof idea: suppose m(k+1)/m(k) ≥ 1 + c/log k for k ≥ N (N ≥ 3). Then m(k) > 0 there, since
the ratio would otherwise be 0. Fix n ≥ 2N with log n ≥ c and put y = c/log n ≤ 1. For
N ≤ k < n we have c/log k ≥ y, so induction gives m(n) ≥ (1+y)^(n−N). The bound exp(y/2) ≤ 1+y
on [0,1] (from exp(−y/2) ≥ 1−y/2) turns this into m(n) ≥ exp((n−N)·y/2) ≥ exp(n·c/(4 log n)).
Finally log n = o(n^(1−α)) (`isLittleO_log_rpow_atTop`) gives 4·log n·n^α ≤ c·n eventually,
so n^α ≤ n·c/(4 log n). The hypothesis 0 < α is not needed (the linter flags it as unused; the
statement was kept unchanged).

Axioms: `'Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary' depends on axioms: [propext, Classical.choice, Quot.sound]`
