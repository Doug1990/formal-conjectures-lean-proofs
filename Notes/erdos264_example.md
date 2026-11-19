# Erdos264.erdos_264.variants.example

- Statement: `theorem erdos_264.variants.example : IsIrrationalitySequence (fun n ↦ 2 ^ (2 ^ n))`
- Source: FormalConjectures/ErdosProblems/264.lean:68 (category research solved)
- Date: 2026-11-05
- Axioms: `'Erdos264.erdos_264.variants.example' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Proof idea
Write x_n = 2^(2^n), a_n = x_n + b_n with |b_n| ≤ B. The series converges, and its tails satisfy
0 < T_N ≤ 4/x_N. Suppose the sum is p/q. Let Q_N = ∏_{n<N} a_n. Then k_N = q·Q_N·T_N is an integer:
it satisfies k_0 = p and k_{N+1} = a_N k_N − q Q_N. The bound ∏_{n<N}(x_n + B) ≤ 2^B·∏ x_n = 2^(B−1) x_N
comes from Bernoulli's inequality (x+B)x^(B−1) ≤ (x+1)^B and the Fermat-number identity
∏(x_n+1) = x_N − 1, so |k_N| ≤ q·2^(B+1). Since x_{N+1} = x_N², eliminating Q_N gives
k_{N+2} = y²(k_{N+1}−k_N) + y(k_{N+1} − 2b_N k_N) + (b_{N+1}+b_N)k_{N+1} − b_N² k_N with y = x_N.
For y large this forces k_{N+1} = k_N first, and then k_N·(1−2b_N) = 0 (1−2b_N is odd, so nonzero).
So k_N = 0, which contradicts T_N > 0. The hypothesis b_n ≠ 0 is not used.

Verified file: work/erdos264_example.lean (2 compiles, the 2nd one clean). The results copy is a hand copy of it
and was not compiled separately.
