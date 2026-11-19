# wowii100

- Statement: `WrittenOnTheWallII.GraphConjecture100.conjecture100` (α(G) ≤ ⌈(max_v l(v) + ½·‖deg(Gᶜ)‖₂)/2⌉ for connected G)
- Source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean:82` (research solved)
- Date: 2026-11-19

**Proof idea.** Let S be a maximum independent set with A = |S|, T = V∖S with t = |T|, and L = max l(v). By the ceiling, it suffices to show 4A−4−2L < ‖deg Gᶜ‖₂, i.e. (4A−4−2L)² < Q = Σ_v deg_{Gᶜ}(v)² whenever the left side is nonnegative. Let x_s be the number of non-neighbours of s ∈ S in T, and z_v the number of non-neighbours of v ∈ T in S. Then deg_{Gᶜ}(s) ≥ A−1+x_s and deg_{Gᶜ}(v) ≥ z_v. Since S ∩ N(v) is independent inside N(v), z_v ≥ A−L. Double counting gives Σx_s = Σz_v =: X. Connectedness gives x_s ≤ t−1, so t(A−L) ≤ X ≤ A(t−1), hence tL ≥ A. This yields Q ≥ A(A−1)² + (3A−2−L)X and L·X ≥ A(A−L). The case L < A then reduces to the polynomial inequality 4L(2A−2−L)² < L·A(A−1)² + A(A−L)(3A−2−L), proved by nlinarith after the substitution L = 1+p, A−L = 1+q. The case L ≥ A uses 4(A−2)² < A(A−1)².

Axioms: `propext, Classical.choice, Quot.sound`
