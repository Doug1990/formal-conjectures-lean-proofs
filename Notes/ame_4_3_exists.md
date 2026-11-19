# OpenQuantumProblem35.ame_4_3_exists

- Source: `FormalConjectures/OpenQuantumProblems/35.lean:760` (category research solved; Helwig et al. 2012, Goyeneche et al. 2015)
- Statement: `ExistsAME 4 3`
- Definitions (Config, StateVector, combineFirst, reducedDensityFirst, maximallyMixed, IsAME, ExistsAME, ...) restated verbatim from the source file; targeted Mathlib imports instead of FormalConjecturesUtil.

## Proof idea
Take the uniform superposition (amplitude 1/3) over the 9 code words of the ternary MDS code
enc(i,j) = (i, j, i+j, i+2j) mod 3. Every pair of distinct positions determines the code word
(`mds_inj`, checked by `decide +kernel` over 12·81 cases), so for each permutation π the two
coordinates at positions π⁻¹(0), π⁻¹(1) fix a unique message, and the other two coordinates
are an injective "completion" function of them. The source file's completion criterion
(`reducedDensityFirst_of_completion`, copied) then gives reduced density (1/9)·I = maximally
mixed. Normalization: 9 nonzero amplitudes of squared norm 1/9.

## Axioms
`'OpenQuantumProblem35.ame_4_3_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

Verified file: work/ame43.lean (results copy written by hand from it, not compiled separately).
Date: 2026-11-05. Compiles: 3.
