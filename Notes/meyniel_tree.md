# MeynielConjecture.meyniel_conjecture.variants.tree

- Source: FormalConjectures/Wikipedia/MeynielConjecture.lean:158 (category research solved, Nowakowski–Winkler 1983)
- Statement: a nonempty finite connected acyclic graph has cop number 1.

Proof idea: the definitions (Step, CopsCatchWithin, CopsWin, copNumber) and the API lemma
one_le_copNumber are restated verbatim. For ≤ 1, one cop starts at a fixed root u. Invariant:
the cop c lies on a geodesic from u to the robber r, i.e. dist u r = dist u c + dist c r. Each
round the cop steps to a neighbour one closer to r (step_closer), which raises dist u c by exactly
1 and keeps the invariant. A robber move away from u keeps it by the triangle inequality; a move
towards u (its parent, by `IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable`) keeps it by the
tree lemma geodesic_parent (two geodesic walks u→r are equal by path uniqueness, so the cop lies on
the geodesic u→r'). Since dist u c < card V, induction on m with "card V ≤ dist u c + m" ends
with a capture within card V rounds.

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-10-31
