# ohba_ert

- Statement: `OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor` (category research solved, Erdős–Rubin–Taylor 1979)
- Source: `FormalConjectures/Wikipedia/OhbaConjecture.lean:74`
- Date: 2026-11-02

Proof idea: we prove a stronger statement by strong induction on a finite set s of parts.
If every vertex in a part of s has a list of at least |s| colours, there is a list colouring
that is proper between different parts of s. If some part {u, v} has a common colour x, colour
both u and v with x and remove x from all other lists (each loses at most one colour). Then
recurse on s minus that part. Otherwise the two lists in each part are disjoint, and we apply
Hall's theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) to get an injective
choice of colours. A set X of at most |s| vertices is covered by any single list. A larger X
contains both vertices of some part (pigeonhole), whose disjoint lists already give
≥ 2|s| ≥ |X| colours. The theorem is the case s = univ. `Choosable` is restated locally
because FormalConjecturesUtil is not built.

Axioms: `'OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles: 2 (1st: one no-op `simp only`; 2nd: clean + axioms).
