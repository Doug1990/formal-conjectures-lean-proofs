# burning_path

- Statement: `BurningNumberConjecture.burning_number_conjecture.variants.path` (category research solved, Bonato–Janssen–Roshanbin 2016)
- Source: `FormalConjectures/Paper/BurningNumberConjecture.lean:85` in google-deepmind/formal-conjectures
- Statement: for n ≥ 1, `burningNumber (pathGraph n) = ⌈√n⌉₊`.

## Proof idea

Path distance: every walk in `pathGraph n` has length ≥ |u − v| (induction on the walk), and there is an explicit walk of length |u − v|, so `dist u v` is squeezed. Lower bound: a burning sequence with k rounds covers Fin n by balls of radius k−1−i, each with ≤ 2(k−1−i)+1 vertices (injection into an `Icc` of naturals), and Σ_{i<k}(2(k−1−i)+1) = k², so n ≤ k² and ⌈√n⌉ ≤ k. Upper bound for k = ⌈√n⌉ (so n ≤ k²): with j = k−1−i, the centre of round i is min(k² − (j+1)² + j, n−1). A vertex v is covered by the round with j = Nat.sqrt(k² − v − 1), because v lies in [k² − (j+1)², k² − j² − 1] and so within distance j of the unclipped centre (clipping to n−1 only brings the centre closer, since v ≤ n−1).

## Axioms

`'BurningNumberConjecture.burning_number_conjecture.variants.path' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date

2026-11-01 (2 compiles; definitions restated, targeted imports)
