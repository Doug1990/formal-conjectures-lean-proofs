# erdos1126

- Statement: `Erdos1126.erdos_1126` (research solved, de Bruijn 1966 / Jurkat 1965)
- Source: `FormalConjectures/ErdosProblems/1126.lean:46`
- Date: 2026-11-17

Proof idea: Fubini (`Measure.ae_ae_of_ae_prod`) gives a full-measure set G of x such that f(x+y) = f(x) + f(y) for almost every y. For each x, pick u (by choice) with u ∈ G and x − u ∈ G. This is possible because both conditions hold for a.e. u, and a.e. statements are stable under y ↦ a ± y (quasi-measure-preserving maps). Set g(x) := f(u) + f(x−u). Chaining the two a.e. identities shows that f(x+y) − f(y) = g(x) for a.e. y. An a.e.-constant value is unique, since ae volume is NeBot. Together these give g(x+y) = g(x) + g(y) for all x, y, and f = g on G. The only warning is the unused binder `h`, which is part of the original statement.

Axioms: `'Erdos1126.erdos_1126' depends on axioms: [propext, Classical.choice, Quot.sound]`
