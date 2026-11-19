# mqg4_nnreal

- Statement: `MonochromaticQuantumGraph.eqSystem4_no_solution_nnreal_ge4` (Bogdanov, research solved)
- Source: `FormalConjectures/Paper/MonochromaticQuantumGraph.lean:346`
- Date: 2026-11-18

Proof idea: the definitions are restated with targeted Mathlib imports. For N = 4 the perfect-matching sum unfolds (by `simp`) to the three terms W01·W23 + W02·W13 + W03·W12. At the constant colouring i the sum is 1, so one of the three matching products, k(i) ∈ Fin 3, is nonzero. With D ≥ 4 colours, pigeonhole gives colours i ≠ j with k(i) = k(j). Evaluate the system at the two-colour assignment (i,i,j,j), (i,j,i,j) or (i,j,j,i), matching the shared type. The sum must be 0, and in ℝ≥0 each summand is then 0 (`add_eq_zero`). But the summand of that type is W(e₁; i,i)·W(e₂; j,j), a product of two nonzero factors, which is a contradiction.

Axioms: `propext, Classical.choice, Quot.sound`
