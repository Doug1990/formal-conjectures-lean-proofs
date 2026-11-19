# Borsuk.borsuk_conjecture.zero

- Source: `FormalConjectures/Wikipedia/BorsukConjecture.lean`, line 173 (category test): `BorsukConjecture 0`.
- Draft: `work/borsuk_zero.lean`. Uses targeted Mathlib imports. `HasBorsukCover`, `BorsukConjecture` and the scoped `ℝ^n` notation (from `FormalConjecturesForMathlib/Geometry/Euclidean.lean`) are copied verbatim.

**Proof idea.** The statement is vacuous, as the source docstring says. `ℝ^0 = EuclideanSpace ℝ (Fin 0)` has only one point, because any two points are equal by `PiLp.ext` with `Fin.elim0`. So no subset is `Nontrivial`, and the hypothesis `s.Nontrivial` gives a contradiction.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
