# Erdos494.erdos_494.variants.k_eq_2_card_not_pow_two

- Source: `FormalConjectures/ErdosProblems/494.lean:58` (category research solved, Selfridge–Straus: k = 2 and |A| not a power of 2 ⇒ A is determined by its 2-sums)
- Definitions `sumMultiset` and `Erdos494Unique` are restated verbatim (targeted imports, no FormalConjecturesUtil).

Proof idea: with P_m = Σ_{a∈A} a^m and Q_m = Σ over the 2-sum multiset of z^m, Finset induction gives 2Q_m + 2^m P_m = Σ_{a,b∈A} (a+b)^m = Σ_j C(m,j) P_j P_{m−j}. If A and B have the same 2-sums and the same size n, strong induction on m gives (2n − 2^m)(P_m(A) − P_m(B)) = 0. The middle binomial terms only use lower power sums, and the two outer terms give 2n·P_m. Since n is not a power of 2, all power sums agree. Then A ⊆ B: for a₀ ∈ A∖B, the polynomial r = ∏_{a∈A∖{a₀}}(X−a)·∏_{b∈B}(X−b) has Σ_A r = Σ_B r (linearity in the power sums). The left side is r(a₀) ≠ 0 and the right side is 0. Equal cards then give A = B.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-12. Compiles: 2 (1: one unsolved `simp` goal in the empty case of the induction, the rest was correct; 2: clean + axioms).
