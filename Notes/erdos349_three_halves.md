# Erdos349.three_halves_two_not_isGoodPair

- Source: FormalConjectures/ErdosProblems/349.lean:176 (category research solved)
- Statement: `¬ IsGoodPair (3 / 2) 2`

Proof idea: ⌊(3/2)·2^0⌋ = 1 and ⌊(3/2)·2^(m+1)⌋ = 3·2^m, so every term of the sequence is 1 or a multiple of 3. A subset sum of distinct terms therefore contains 1 at most once (the filter `x = 1` is ∅ or {1}) and is ≡ 0 or 1 (mod 3). The integer 3·|N|+2 ≥ N is ≡ 2 (mod 3), so it is not a subset sum, which contradicts eventual completeness. `subsetSums` / `IsAddComplete` are restated locally with the same bodies as in FormalConjecturesForMathlib.

Axioms: `'Erdos349.three_halves_two_not_isGoodPair' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
