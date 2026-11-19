# mukwembi_q3

- Statement: `SizeOrderConnectedDomination.mukwembi_theorem_2_1` (category research solved; the claimed theorem is false)
- Source: `FormalConjectures/Paper/SizeOrderConnectedDomination.lean:56` in the checkout
- Date: 2026-11-01
- Compiles: 3 (1: oversized Decidable instance in `triple`, misnamed walk variable; 2: clean; 3: + `#print axioms`)

## Proof idea
The counterexample is the 3-cube Q₃ on `Fin 8`, where i ~ j iff i xor j ∈ {1,2,4}. It is connected (every
v ≠ 0 has a smaller neighbour, then strong induction) and triangle-free (adjacency flips the bit-parity), and it has
12 edges (3-regular, handshake lemma). The core lemma `no_small` shows every connected dominating set has ≥ 4 vertices.
A singleton dominates only 4 vertices. Otherwise, connectivity of the induced subgraph gives every member a neighbour
inside D (first step of a walk). So a set of size ≤ 3 lies in {d, e, f} with d ~ e and f = d or f ~ d or f ~ e,
and a `decide` check finds an undominated vertex in every such case. Since `univ` is a connected dominating set,
`Nat.sInf_mem` gives 4 ≤ γ_c ≤ 8, and (8 − γ_c)²/4 + 7 ≤ 11 < 12. The definitions from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean are restated locally, verbatim; the statement is unchanged.

## Axioms
`'SizeOrderConnectedDomination.mukwembi_theorem_2_1' depends on axioms: [propext, Classical.choice, Quot.sound]`
