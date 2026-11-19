# Erdos742.variants.plesnik_bound

- Source: `FormalConjectures/ErdosProblems/742.lean`, line 103 (`research solved`, Plesník [Pl75]).
- Statement: every diameter-2-critical graph on n vertices has |E| < 3n(n−1)/8.
- `IsDiameter2Critical` is restated locally, verbatim from the checkout. The file uses Mathlib-only imports.

## Proof idea
Critical edge lemma (`crit`): deleting uv creates a pair at distance > 2. So either uv lies in no triangle (TF), or one endpoint a has a witness y ≁ a whose unique common neighbour with a is the other endpoint b. For a vertex u, let o_u be the number of witnessed edges at u that are not TF, and t_u the number of TF edges at u. Then every edge is counted, so 2E ≤ Σt + 2Σo. The witnesses are distinct non-neighbours of u. This gives o_u + d_u + 1 ≤ n. For a TF edge uv they also avoid N(v), which is disjoint from N(u), so o_u + d_u + d_v ≤ n. With c_u = n−1−d_u−o_u ≥ max(0, t_v − 1) over the TF-neighbours v, average over them. The symmetrisation Σ_{uv TF} t_v/t_u ≥ Σt uses a/b + b/a ≥ 2. Together these give Σc ≥ Σt − k, where k = #{u : t_u > 0} ≤ min(n, Σt). Hence 6E ≤ 2n² − n. With n ≥ 3 (since diam = 2), this gives E < 3n(n−1)/8. The cases n = 3, 4, 5 need integrality.

## Verification
`#print axioms Erdos742.plesnik_bound` prints: propext, Classical.choice, Quot.sound

Date: 2026-11-14. 3 compiles.
