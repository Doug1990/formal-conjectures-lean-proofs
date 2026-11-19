# qubitSICFamily_pairwise

- Statement: `OpenQuantumProblem23.qubitSICFamily_pairwise` (category test), source `FormalConjectures/OpenQuantumProblems/23.lean` in the checkout.
- Note: the checkout's `FormalConjecturesUtil` is not built, so the file uses `import Mathlib` and omits the `@[category test, AMS 15 47 81]` attribute. Needed definitions are copied verbatim; the statement is unchanged.
- Proof idea: record Re/Im of ω, ω² and conj(ω)² (with ω = -1/2 + i√3/2), and the values tetraA², tetraB², √3² and their fourth powers. Then case-split over all pairs i ≠ j in `Fin 4`, expand `overlapSq` into real and imaginary parts, normalise with `ring_nf`, and substitute the square values. Every pair gives 1/3 = sicOverlapSq 2.
- Axioms: `[propext, Classical.choice, Quot.sound]`
- Date: 2026-10-27
