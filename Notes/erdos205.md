# erdos205

- Statement ids: `Erdos205.erdos_205.parts.i`, `Erdos205.erdos_205.parts.ii`, `Erdos205.erdos_205.parts.iii`
- Source: `FormalConjectures/ErdosProblems/205.lean` (lines 58, 71, 85), category research solved (Barreto–Leeham).
- Date: 2026-11-13

**Proof idea.** CRT construction. For r ≥ 48, take Bertrand primes p_k ∈ (2^{k+1}, 2^{k+2}] for k < r. These are distinct and odd. Choose n (CRT value + the product of the moduli) with n ≡ 2^r (mod 2^{r+1}) and n ≡ 2^k (mod p_k^r) for k < r. Then n = 2^r·odd > 2^r is not a power of 2. For every k with 2^k ≤ n, m = n − 2^k is nonzero and is divisible by p_k^r (k < r) or by 2^r (k ≥ r), so Ω(m) ≥ r and m ≥ 2^r. Also n < 2^{r(r+1)²+1}, so log m < r(r+1)²+1 ≤ r⁴/24 ≤ e^r, i.e. log log m < r ≤ Ω(m). One lemma `RP.gen` (any f with f(m) ≤ log log m for large m is not eventually representable) gives all three parts. Part i takes f = log log. Part ii specialises to ε = 1. Part iii uses the o-bound with constant 1 together with log log m ≥ 0 for m ≥ 3. Note that `IsRepresentable` allows m = 0. This is excluded because n is not a power of 2, which matters for part iii, where f(0) may be positive.

**Axioms:** `propext, Classical.choice, Quot.sound` (all three theorems).
