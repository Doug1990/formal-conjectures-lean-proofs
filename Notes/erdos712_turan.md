# Erdos712.erdos_712.variants.graph_case and graph_case_div_sq

- Source: `FormalConjectures/ErdosProblems/712.lean:65` and `:73` (category research solved)
- Definitions restated verbatim from `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (targeted Mathlib imports).

**Proof idea.** First, `ex_eq` shows ex₂(n, K_{r+1}) = |E(turanGraph n r)|. The translation between 2-uniform families H and simple graphs uses Adj a b ↔ a ≠ b ∧ {a,b} ∈ H, and the edge counts agree by double counting degrees (Σ deg = 2|E| and Σ_v |{e ∈ H : v ∈ e}| = 2|H|). The upper bound is Mathlib's Turán theorem `CliqueFree.card_edgeFinset_le`, rewritten with `card_edgeFinset_turanGraph`. The lower bound takes the edge family of `turanGraph n r`, which is K_{r+1}-free by `turanGraph_cliqueFree`. From Mathlib's edge-count formula we get 2r·E ≤ (r−1)n² and (n²−r²)(r−1) ≤ 2r(E+1). For each normalization (C(n,2) or n²), these give lower and upper bounds that are explicit rational functions of 1/n. Both bounds tend to the stated limit, and the squeeze theorem finishes.

Axioms (both): `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
