# wowii200

- Statement: `WrittenOnTheWallII.GraphConjecture200.conjecture200` (a DISPROOF of "tree(G) = ⌈1 + l_avg(G)⌉ ⇒ G has a Hamiltonian path")
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture200.lean:70` (research solved)
- Date: 2026-11-18

Proof idea: this is the q = 5 member of the docstring family, on Fin 11. C = {0,…,4} induces K₅ minus the edge 01. x = 5 and y = 6 are complete to C, z = 7 is adjacent to 0 and 1, and the pendants 8, 9, 10 hang at 2, 3, 4. The claw {0,5,6,7} is an induced tree (star ⇒ acyclic via bridges), so tree ≥ 4. For tree ≤ 4, take an induced tree S with |S| ≥ 5. Its 0/1 membership indicators satisfy: at most 2 per triangle, at most 3 per 4-cycle, and each vertex of S has a neighbour in S (connectivity). A 32-way case split plus `omega` (lemma `arith200`) shows these force |S| ≤ 4. For the average: a clique cover of every neighbourhood by 3 cliques gives l(v) ≤ 3, and explicit independent sets in the neighbourhoods give Σ l ≥ 24. So 2 < l_avg ≤ 3 and ⌈1 + l_avg⌉ = 4. Finally, in a path every vertex other than the two endpoints has two distinct neighbours (`two_nbrs`, by walk induction). The three degree-1 pendants must therefore all be endpoints, which is impossible.

Axioms: `[propext, Classical.choice, Quot.sound]`
