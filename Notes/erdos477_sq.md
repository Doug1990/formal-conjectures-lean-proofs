# Erdos477.erdos_477.variants.S_sq

Source: FormalConjectures/ErdosProblems/477.lean:61 (category research solved, Sekanina 1959).

Proof idea: suppose every z is uniquely a + k² with a ∈ A. If a, a' ∈ A and a + k² = a' + k'², uniqueness forces a = a'. So two distinct elements of A cannot differ by a difference of two squares. Every odd number 2k+1 = (k+1)² − k² and every multiple of four 4k = (k+1)² − (k−1)² is such a difference. So distinct elements of A differ by 2 mod 4. Each z has a representative a ≤ z (since k² ≥ 0). Take a0 ≤ 0, then a1 ≤ a0 − 1, then a2 ≤ a1 − 1. These are three distinct elements of A with pairwise differences ≡ 2 mod 4, which is impossible (omega).

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-08
