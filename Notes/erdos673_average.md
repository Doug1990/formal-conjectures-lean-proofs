# Erdos673.erdos_673.variants.average

- Source: `FormalConjectures/ErdosProblems/673.lean`, line 70 (category research solved; Erdős calls it "easy")
- Statement: (1/X) Σ_{n ≤ X} G(n) → ∞.
- File `erdos673_average.lean` also contains `erdos_673.variants.tao` (the same proof as `erdos673_tao.lean`), which this proof uses.

Proof idea: Tao's bound with m = 2 gives G(2k) ≥ τ(k)/2. Since G ≥ 0 and k ↦ 2k injects Ioc 0 (X/2) into Icc 1 X, we get Σ_{n≤X} G(n) ≥ ½ Σ_{k≤N} τ(k) with N = ⌊X/2⌋. Swapping the sum gives Σ_{k≤N} τ(k) = Σ_{a≤N} ⌊N/a⌋ ≥ N·H_N − N, and `log_add_one_le_harmonic` gives H_N ≥ log(N+1). For a target b, take X ≥ 2⌈e^{8b+2}⌉ + 2. Then H_N ≥ 8b + 2 and 4N ≥ X, so the sum is ≥ N(H_N − 1)/2 ≥ bX (nlinarith, with a case split on the sign of b).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29
