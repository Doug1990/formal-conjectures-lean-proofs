# erdos1111_wagon

- Statement: `Erdos1111.erdos_1111.variants.wagon` (line 75)
- Source: `FormalConjectures/ErdosProblems/1111.lean` (tagged `research solved`; Wagon [Wa80b], via El-Zahar–Erdős)
- File: `results/erdos1111_wagon.lean` (identical to `work/erdos1111_wagon.lean`)

Proof idea: assume there are no two anticomplete sets that each contain an edge, and take a
maximum clique K (|K| = k ≤ t − 1). For a vertex w, let M(w) be the set of v ∈ K with
v not adjacent to w. M(w) is nonempty by maximality. Colour w by an element of K.sym2: a pair
of two distinct elements of M(w) if such a pair exists, else the diagonal s(a, a) with
M(w) = {a}. This colouring is proper. If adjacent x, y get the same off-diagonal pair {a, b},
then {a, b} and {x, y} are anticomplete edges. If they get the same diagonal s(a, a), then
(K ∖ {a}) ∪ {x, y} is a larger clique. So χ ≤ |K.sym2| = C(k+1, 2) ≤ C(t, 2), which
contradicts C(t, 2) + 1 ≤ χ. `Anticomplete` is restated locally as in the checkout. The
statement is verbatim, without the `@[category …]` attribute.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-14
