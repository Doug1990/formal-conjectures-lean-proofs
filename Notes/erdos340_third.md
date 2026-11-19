# Erdos340.erdos_340.variants.third

- Source: `FormalConjectures/ErdosProblems/340.lean:104` (category textbook)
- Statement: `n^(1/3) =O[atTop] #(range greedySidon ∩ [1, n])` for the greedy Sidon sequence.
- Date: 2026-10-29

Proof idea: let `S_k` be the set after `k` greedy steps and `a_k` its newest (largest)
element. Using the covering map `g(b, c, a) = if c < b ∧ a = b then (b+c)/2 else b+c-a`
and `insert_sidon` (from `results/erdos44_greedy.lean`), every `m` with `1 ≤ m < a_{k+1}` lies
in `g(S_k³)`: either `m` is a term, or `a_j < m < a_{j+1}` for some `j ≤ k`, and by the
minimality of `Nat.find` in `greedySidon.go`, `S_j ∪ {m}` is not Sidon. For `n ≥ 1` take the
least `k` with `n < a_{k+1}`; then `S_k ⊆ range a ∩ [1, n]` and `n ≤ |S_k|³`, so
`n^(1/3) ≤ |S_k| ≤ count`, giving the bound with constant 1.
`IsSidon`, its `Decidable` instance, `greedySidon.go/aux`, `greedySidon` are restated from
`FormalConjecturesForMathlib/Combinatorics/Basic.lean` with identical data. Only the existence proof
inside `go` is our own; it is a Prop, so `Nat.find` gives the same values. The one compiler warning
is the unused `hε` in the given statement.

Axioms: `'Erdos340.erdos_340.variants.third' depends on axioms: [propext, Classical.choice, Quot.sound]`
