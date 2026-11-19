# Erdos138.monoAPNumber_two_one and Erdos138.monoAPNumber_two_two

- Source: `FormalConjectures/ErdosProblems/138.lean` (category test), statements `W 1 = 1` and `W 2 = 3`.
- Draft: `work/erdos138_v2.lean`. Uses targeted Mathlib imports. `Set.IsAPOfLengthWith`, `Set.IsAPOfLength`, `ContainsMonoAPofLength` (from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`) and `monoAP_guarantee_set`, `monoAPNumber`, `W` are copied verbatim, because `FormalConjecturesUtil` is not built.

**Proof idea.** For each value we show that the target N is in the guarantee set and that every smaller N is not; then `Nat.sInf_le` and `le_csInf` give the value. Two helper lemmas turn an AP of length 1 (or 2) in the image into one point (or two points with distinct values) of `ap`, using `Set.encard_eq_one` and `Set.encard_eq_two`. W 1: any coloring of {1} has the singleton {1} as a 1-term AP, and {1..0} is empty, so no AP exists there. W 2: among the colors of 1, 2, 3 in Fin 2, two must be equal, and any pair a<b is a 2-term AP. For N ≤ 2, coloring 1 ↦ 0 and everything else ↦ 1 gives two distinct points of {1,2} with different colors, so no monochromatic 2-AP exists.

Axioms (both): `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
