# erdos673_i

- Statement: `Erdos673.erdos_673.parts.i` (category research solved; Erdős calls it trivial)
- Source: `FormalConjectures/ErdosProblems/673.lean:53` in the checkout
- Statement: `∀ C : ℝ, {n : ℕ | C < G n}.HasDensity 1`

Proof idea: Since Σ 1/p diverges (`not_summable_one_div_on_primes`) and 1 − x ≤ e^{−x}, every
tail of the primes has a finite block [a, b) with ∏(1 − 1/p) ≤ δ. The number of n < N coprime to
Q = ∏_{p∈[a,b)} p is at most (N/Q + 1)·φ(Q) ≤ δN + Q (φ(Q) = Q·∏(1 − 1/p), via
`Nat.filter_coprime_Ico_eq_totient`). Given C and ε, take a first block [0, e₁) with δ = ε/2, then
K with 2^K > C·e₁, then K more consecutive blocks with δ = ε/(2(K+1)). If n ≠ 0 has a prime factor
in every block, take m = p ≤ e₁ from the first block. Then n/m has ≥ K distinct prime factors, so
τ(n/m) ≥ 2^K (`Nat.card_divisors`), and Tao's bound τ(n/m)/m ≤ G(n) (reproved from
results/erdos673_tao.lean) gives G(n) > C. By a union bound, at most εN + const integers below N
are bad, so the partial density is ≥ 1 − ε − const/N and ≤ 1. `tendsto_order` finishes.
`Set.partialDensity` / `Set.HasDensity` are restated locally, copied verbatim from
FormalConjecturesForMathlib/Data/Set/Density.lean. Targeted imports.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
