# OpenQuantumProblem35.ame_6_2_exists

- Source: FormalConjectures/OpenQuantumProblems/35.lean:733 (category research solved)
- Statement: `ExistsAME 6 2` (an absolutely maximally entangled 6-qubit state exists)
- Verified file: work/ame62.lean (this is a hand copy, not compiled separately). The definitions from 35.lean are restated locally with targeted imports.

Proof idea: the witness is the graph state of the wheel graph W₆ (a 5-cycle plus a hub joined to all 5 vertices), ψ(y) = (−1)^{Q(y)}/8, where Q is the quadratic form of the graph. For every permutation, the reduced density on the first 3 parties is (1/64)·Σ_z s(W a z)s(W b z). If a = b, every term is 1, so the sum is 8. If a ≠ b, a kernel `decide` rank check (`rank`: for every 3-set A and every nonzero c on A there is j ∉ A with Σ G_{j,i} c_i = 1) gives an outside vertex j = π⁻¹(R k). Flipping z_k is an involution that negates each term, because flipping bit j changes Q by the neighbour sum N_j (`Q_flip`, checked by `decide +kernel` over 6 × 64 cases) and N_j differs by 1 between the two configurations (`N_W` linearity). `Finset.sum_involution` then makes the sum 0. This avoids the 120 × 64 × 64 brute-force check.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-05
