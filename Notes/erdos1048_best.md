# erdos_1048.variants.diam_ge_two_is_best

- Statement: `Erdos1048.erdos_1048.variants.diam_ge_two_is_best`, source `FormalConjectures/ErdosProblems/1048.lean:110` (category research solved; the "best possible" example f = zⁿ).
- Proof idea: for n ≥ 1, ‖zⁿ‖ ≤ 1 ⟺ ‖z‖ ≤ 1, so the level set of Xⁿ is the closed unit disk. The disk is convex, hence preconnected, so its connected component containing 0 is the whole disk. Its ediam is ofReal (diam) since it is bounded, and `Metric.diam_closedBall_eq` gives diam = 2. `levelSet` from Erdos1043 is restated verbatim locally (targeted imports).
- Axioms: `propext, Classical.choice, Quot.sound`
- Verified file: work/erdos1048_best.lean (2 compiles; this results copy is identical).
- Date: 2026-11-05
