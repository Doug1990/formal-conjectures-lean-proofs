# Erdos294.erdos_294.variants.erdos_graham_upper

Source: FormalConjectures/ErdosProblems/294.lean:82 (category research solved; Erdős–Graham, proof in Liu–Sawhney 2024 §4).

Statement: t(N) ≪ N / log N. The `≪` notation (FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean) is written out as `Asymptotics.IsBigO atTop`. HasUnitFractionSolution and t are restated verbatim.

Proof idea: suppose p is prime, N < p(k+1) and k·lcm(1..k) < p, and that 1 = Σ_{n∈s} 1/n with min s = p and s ⊆ [p, N]. Multiples of p in s are p·j with 1 ≤ j ≤ k. Multiply by p·Q·R, where Q = ∏ of the non-multiples and R = lcm(1..k). Reducing mod p gives p | Q·X with X = Σ_j R/j. Since p ∤ Q, p | X, but 0 < X ≤ k·R < p, a contradiction. So t(N) ≤ p. For log N ≥ 28 take k = ⌊log N/28⌋. Chebyshev (ψ(k) ≤ (log 4 + 4)k, from Mathlib) gives lcm(1..k) ≤ e^{7k} ≤ N^{1/4}, so k(k+1)·lcm(1..k) ≤ N. Bertrand gives a prime p ∈ (N/(k+1), 2N/(k+1)], and then t(N) ≤ p ≤ 56 N / log N.

Axioms: propext, Classical.choice, Quot.sound

Compile: clean (no warnings).

Date: 2026-11-10
