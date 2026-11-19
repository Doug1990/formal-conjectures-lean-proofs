# green43_lt_half

- Statement: `Green43.green_43.variants.general_exponent_lt_half` (∀ α ∈ (0, 1/2), SievedLowerBoundExp α)
- Source: `FormalConjectures/GreensOpenProblems/43.lean:183` (category research solved)
- Definitions `sievedSet`, `sievedCard`, `SievedLowerBound`, `SievedLowerBoundExp` copied verbatim; the statement is unchanged.

Proof idea: Set X = N^α and let P be the primes in (⌈X⌉, 2⌈X⌉−2], so every p ∈ P lies in [X, 2X).
Combinatorial core (Cauchy–Schwarz): with c(x) = #{p ∈ P : p | x − a(p)}, Σ_{x≤N} c ≥ k(N/(2X) − 1) and
Σ c² ≤ k²(N/X² + 1) + kN/X. Here k = #P ≤ 3X, and c vanishes off the sieved set. With 3X² ≤ N and X ≥ 12 this gives
|sieved| ≥ kN/(80X). Prime count: an Erdős/Bertrand-style central binomial bound (adapted from Mathlib's Bertrand
proof) gives (n/3)·log 4 ≤ (1 + √(2n) + K)·log(2n), where K = #primes in (n, 2n]. With log(2n) ≤ (2n)^η/η
(η = δ/α, δ = min(ε/2, α/4)) this yields k ≥ η X/(32 N^δ) − 2√X − 3 ≥ 80 X / N^{2δ} for large N. Hence
|sieved| ≥ N^{1−2δ} ≥ N^{1−ε}. All "large N" conditions have the form C ≤ N^γ, from tendsto_rpow_atTop.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-18 (built across several runs; 10 compiles in total for the final assembly, including earlier partial runs' 8)
