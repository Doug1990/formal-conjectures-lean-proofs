# Erdos602.erdos_602.variants.countable_index

- Source: `FormalConjectures/ErdosProblems/602.lean:156` (category research solved)
- Statement: a family (A_i)_{i ∈ ℕ} of countably infinite sets with finite pairwise intersections
  of size ≠ 1 has Property B (a 2-colouring with no monochromatic A_i).

Proof idea: Bernstein's lemma. The intersection hypotheses and countability are not needed;
only the infiniteness of each A_i is used. By recursion, pick x_n ≠ y_n in A_n outside the
finite set S_n = {x_0, y_0, …, x_{n−1}, y_{n−1}} (possible because A_n \ S_n is infinite).
Then x_n ≠ y_m for all n, m: for m < n, y_m ∈ S_n ∌ x_n; for n < m, x_n ∈ S_m ∌ y_m; for
m = n by choice. Colour z with 1 iff z is some y_m. Then x_n gets 0 and y_n gets 1, so no A_n is
monochromatic. The definitions IsMonochromatic / HasPropertyB are restated locally from the
source file, and targeted imports are used.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-08 (2 compiles)
