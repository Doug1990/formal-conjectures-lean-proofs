# Erdos670.erdos_670.variants.choose_two

- Source: `FormalConjectures/ErdosProblems/670.lean:82` (category textbook)
- Statement: if A ⊆ ℝ^d has separated distances and |A| ≠ 2, then C(|A|, 2) ≤ diam A.

Proof idea: for |A| ≤ 1 the left side is 0 and diam ≥ 0. For |A| ≥ 3, every distance is ≥ 1: given a ≠ b, pick a third point c. Then s(a,c) ≠ s(b,c), so 1 ≤ |d(a,c) − d(b,c)| ≤ d(a,b). Let S be the set of distance values over A.offDiag. Each fibre has at most 2 ordered pairs, (a,b) and (b,a), because different unordered pairs have different distances. So |A|(|A|−1) ≤ 2|S|, which gives C(|A|,2) ≤ |S|. Induction on the max element (`Finset.induction_on_max`) shows that a finite set of reals, all ≥ 1 and pairwise ≥ 1 apart, with every element ≤ y (y ≥ 0), has cardinality ≤ y. Taking y = diam A finishes the proof.

Axioms: `'Erdos670.erdos_670.variants.choose_two' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29. Compiles: 2 (1: `@Metric.diam_nonneg _ _ s` argument order wrong; 2: clean).
