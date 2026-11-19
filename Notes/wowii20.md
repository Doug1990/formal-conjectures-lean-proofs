# wowii20

- Statement: `WrittenOnTheWallII.GraphConjecture20.conjecture20` (research solved)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean:49`
- Claim: for a connected graph G, n / ⌊deg_avg⌋ ≤ b(G) (largest induced bipartite subgraph).

## Proof idea
Let k = ⌊D/n⌋, where D = Σ deg. If k ≤ 0, the left side is ≤ 0. If k = 1, then 2|E| = D < 2n, so a connected G is a tree, hence bipartite, and b = n. If k ≥ 2, the argument avoids the Alon–Kahn–Seymour forest bound cited in the docstring and uses two rounds of the Caro–Wei greedy instead. The greedy (proved by strong induction, picking a vertex of minimum degree in S) gives a maximal independent I ⊆ S with Σ_{v∈S} 1/(d_S(v)+1) ≤ |I|. Phase 1 (S = V) and Cauchy–Schwarz (a tangent-line proof) give a(D+n) ≥ n² for a = |I|. Phase 2 runs on S' = V∖I, with x = |S'|. By maximality, every v ∈ S' has a neighbour in I, so d_{S'}(v)+1 ≤ deg v and Σ_{u∈I} deg u ≥ x. This gives an independent J ⊆ S' with |J|(D−x) ≥ x². I ∪ J is 2-coloured, so b ≥ a + |J|. The final real inequality (`arith`) uses k·n ≤ D < (k+1)n and k ≥ 2, and has two cases: the tangent bound for x²/(D−x) at slope n/D when 2nD + n² − D² ≥ 0, and the extremal point x = nD/(D+n) otherwise.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-18
