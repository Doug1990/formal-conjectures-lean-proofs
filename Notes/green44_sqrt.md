# Green44.green_44.variants.less_than_sqrt

- Source: `FormalConjectures/GreensOpenProblems/44.lean`, line 55 (category research solved)
- Statement: for 1000 primes p_0 < … < p_999 with p_999² < N, sieving [1,N] by ⌊p_i/2⌋ residue classes mod each p_i leaves at most N/10 integers.
- Lean file: `results/green44_sqrt.lean` (identical copy of `work/green44_ls1.lean`)

## Proof idea
This is a self-contained large sieve for prime moduli, done entirely with finite sums. The frequencies are F = {0} ∪ {a/p_i : 1 ≤ a < p_i}, and distinct frequencies are 1/Q²-spaced mod 1 (Q = p_999).

- **Duality.** The weight of [1,N] is majorised by the trapezoid kernel (1/L)·D_{N+L}(β)·conj D_L(β) with L = Q². Cauchy–Schwarz then gives L·Σ_F|S(α)|² ≤ |S|·max_r Σ_s |D_{N+L}||D_L|(α_r − α_s).
- **Kernel bound.** Jordan's inequality gives |D_K(β)| ≤ 1/(2‖β‖). A floor-injection spacing argument gives Σ_{s≠r} 1/‖α_r − α_s‖² ≤ 4Q⁴, so the kernel sum is at most (N+L)L + Q⁴.
- **Lower bound.** Montgomery's lemma for each prime (orthogonality plus Cauchy–Schwarz over the residue classes) gives Σ_{a≠0}|S(a/p)|² ≥ |S|²·ω/(p−ω) ≥ |S|²/2, so Σ_F|S|² ≥ 501|S|².

Combining the two bounds: 501|S| ≤ N + 2Q² < 3N, hence 10|S| ≤ N.

## Axioms
`'Green44.green_44.variants.less_than_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-18
