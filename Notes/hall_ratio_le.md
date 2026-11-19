# hall_ratio_le

- Statement: `HallRatioConjecture.hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber` (category research solved; textbook fact from Scheinerman–Ullman)
- Source: `FormalConjectures/Paper/HallRatioConjecture.lean:72` (definitions from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/FractionalChromaticNumber.lean`, restated locally because the project modules are not built; the statement is unchanged)

Proof idea: the Hall ratio is an `sSup` of nonnegative ratios, so `Real.sSup_le` reduces it to showing `|S| / α(G[S]) ≤ χ_f(G)` for each nonempty `S`, plus `χ_f ≥ 0`. `le_csInf` then reduces that to an arbitrary fractional colouring `w` with total weight `t`. Double counting: `|S| ≤ Σ_{v∈S} Σ_{T∋v} w T = Σ_T w T · |S ∩ T| ≤ t · α(G[S])`, because each `T` with `w T ≠ 0` is independent, so `S ∩ T` lifts to an independent set of `G.induce S` (`IsIndepSet.card_le_indepNum`). For `S` nonempty this forces `α(G[S]) > 0`, so we can divide.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-01. 2 compiles.
