# wowii101

- Statement: `WrittenOnTheWallII.GraphConjecture101.conjecture101` (α(G) ≤ ⌊(n + |alphaCore G|)/2⌋, Hajnal's inequality)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean:71` (research solved)
- Date: 2026-11-19

**Proof idea.** This is the Levit–Mandrescu set-and-collection lemma. Fix a maximum independent set S0. By induction over any finite family Γ of maximum independent sets, 2α ≤ |S0 ∩ ⋂Γ| + |S0 ∪ ⋃Γ|. In the step for a new set S, let X = I \ S, where I is the current intersection and U the current union. No vertex of S ∩ U is adjacent to X, because both lie in a common independent set. So (S ∩ U) ∪ X is independent, and maximality of S gives |X| ≤ |S \ U|. Apply the lemma to the family of all maximum independent sets. A vertex lying in every maximum independent set is in the α-core: an α-sized independent set of G − v maps to one of G that avoids v. The union has at most n elements. The connectedness hypothesis is not needed.

Axioms: `propext, Classical.choice, Quot.sound`
