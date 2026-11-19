# Constant6a.c6a_upper_bound

- Statement: `C6a ≤ 1 / 2` (Tao's optimization constant 6a, union-closed sets), category research solved
- Source: `FormalConjectures/OptimizationConstants/6a.lean:62` in the checkout
- Proof idea: `csSup_le`. The set is nonempty because `c = 0` works for every family. For an admissible `c`, test it on the union-closed family `{∅, {0}}`, which is not `{∅}`. It has 2 members, and every element `i` lies in at most one of them (only `{0}` can contain `i`). So `2c ≤ 1`.
- Axioms: `propext, Classical.choice, Quot.sound`
- Compiles: 1 (clean on the first try, with `#print axioms`)
- Date: 2026-11-03
