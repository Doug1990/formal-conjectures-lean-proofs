# Erdos138.monoAP_guarantee_set_nonempty

- Source: `FormalConjectures/ErdosProblems/138.lean:62` (category research solved; this is van der Waerden's theorem in finite form)
- Verified file: `work/erdos138_vdw.lean`. `results/erdos138_vdw.lean` is an identical copy.

## Proof idea
Mathlib's Hales–Jewett theorem (`Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)`) gives a finite ι such that every r-colouring of `ι → Fin k` has a monochromatic combinatorial line. Colour `v` by the colour of `1 + Σᵢ vᵢ`. A line `l` has coordinates that are either the variable `x` (set `s`, nonempty by `proper`) or a constant, so `1 + Σᵢ l(x)ᵢ = a + x·|s|`. That is an AP with difference `d = |s| > 0`, and its values lie in `[1, 1 + |ι|·k]` (helper `V.vdw_fin`). With `N = |ι|·k + 2`, a colouring of `Icc 1 N` is extended to ℕ, and the AP `{a + n·d : n < k}` is monochromatic with exactly k elements (the map `n ↦ a + n·d` is injective). The case r = 0 is vacuous because `Icc 1 N` is nonempty. The defs `Set.IsAPOfLength(With)` and `ContainsMonoAPofLength` are restated locally, exactly as in FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean.

## Axioms
'Erdos138.monoAP_guarantee_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-10
