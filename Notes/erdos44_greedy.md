# Erdos44.greedy_sidon_construction

- Source: `FormalConjectures/ErdosProblems/44.lean:138` (category textbook)
- Statement: for `1 ≤ N` there is a Sidon set `A ⊆ {1,…,N}` with `N ≤ |A|³`.
- Date: 2026-10-29

Proof idea: take a Sidon subset `A` of `{1,…,N}` of maximal cardinality. If `x ∈ {1,…,N}`
cannot be added, then `x + a = b + c` or `2x = b + c` for some `a, b, c ∈ A` (or `x ∈ A`).
The map `g(b, c, a) = if c < b ∧ a = b then (b+c)/2 else b + c - a` on `A³` hits all these
values (the triples `(b, c, b)` with `c < b` would only give the redundant value `c`, so they
are reused for the midpoints). Hence `{1,…,N} ⊆ g(A³)` and `N ≤ |A|³`. Helper `insert_sidon`
shows that `insert x A` stays Sidon when `x ∉ g(A³)`. `IsSidon` is restated verbatim
from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`; targeted imports.

Axioms: `'Erdos44.greedy_sidon_construction' depends on axioms: [propext, Classical.choice, Quot.sound]`
