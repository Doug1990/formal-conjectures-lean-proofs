# Erdos1186.erdos_1186.variants.probabilistic

- Source: `FormalConjectures/ErdosProblems/1186.lean:109` (category research solved)
- Statement: for k ≥ 2, δ k ≤ 1 / ((k − 1) · 2^k), where δ k = liminf A(n;k)/n².
- Date: 2026-11-09

Proof idea: averaging (the probabilistic method, done as an exact count). Colour by subsets
S ⊆ {1..n}. A progression P with k distinct terms (d ≥ 1) is monochromatic iff P ⊆ S or P ∩ S = ∅,
which holds for at most 2·2^(n−k) subsets S. Summing over all 2^n subsets gives
minMonoCount·2^(k−1) ≤ #progressions. The number of pairs (a,d) with a, d ≥ 1 and a+(k−1)d ≤ n
satisfies 2(k−1)·# ≤ n², by induction on n: going from n to n+1 adds at most n/(k−1) pairs. So
minMonoCount/n² ≤ 1/((k−1)2^k) for every n ≥ 1, and `Filter.liminf_le_of_frequently_le`
(bounded below by 0) finishes. The definitions are restated locally, and the imports are targeted.

Axioms: `'Erdos1186.erdos_1186.variants.probabilistic' depends on axioms: [propext, Classical.choice, Quot.sound]`
