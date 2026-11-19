# erdos652_first

- Statement: `Erdos652.erdos_652.variants.first` (category research solved, "trivial" per its docstring)
- Source: FormalConjectures/ErdosProblems/652.lean:75
- Proof idea: take the origin together with the n−1 points (k/m, √(1−(k/m)²)), k < m = n−1, on the unit circle. These points are distinct because their first coordinates differ, and none of them is the origin. Every point has distance 1 from the origin, so the origin sees exactly one distinct distance. `distinctDistancesFrom` is restated locally with the same `open Classical` definition, and `dDF_eq` bridges the decidability instance.
- Axioms: `'Erdos652.erdos_652.variants.first' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-11 (1 compile)
