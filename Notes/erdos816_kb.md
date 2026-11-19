# erdos816_kb

- Statement: `Erdos816.erdos_816.variants.complete_bipartite` (category research solved)
- Source: `FormalConjectures/ErdosProblems/816.lean:81` in the checkout
- Date: 2026-11-14

Proof idea: in K_{n,n+1} every left vertex has degree n+1 and every right vertex has degree n
(computed by splitting the neighbour count over `Fin n ⊕ Fin (n+1)`). So two vertices with equal
degree lie on the same side. Adjacency in a complete bipartite graph flips `Sum.isLeft`, so a walk
of length 3 (odd) always ends on the other side. That rules out the required path. The edge count
n² + n comes from the handshake lemma: Σ deg = n(n+1) + (n+1)n = 2|E|.
This is the construction that shows erdos_816's bound is sharp. It is not the main theorem.

Axioms: `[propext, Classical.choice, Quot.sound]`
