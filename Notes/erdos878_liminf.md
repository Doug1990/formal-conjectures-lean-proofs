# erdos878_liminf

- Statement: `Erdos878.erdos_878.variants.H_div_self_liminf_finite` (research solved, Erdős [Er84e])
- Source: `FormalConjectures/ErdosProblems/878.lean:156`
- Date: 2026-11-14

Proof idea. The proof is a logarithmic averaging argument with C = 200. Suppose H(x) > 200x for all x ≥ x0. With y = x0+2 and X = y⁴, the harmonic lower bound log(b+1) − log(a+1) ≤ Σ_{a≤x<b} 1/(x+1) gives Σ_{x<X} H(x)/(x(x+1)) ≥ 200(log(X+1) − log(y+1)). On the other side, swapping sums and telescoping Σ_{x>n} 1/(x(x+1)) ≤ 1/n gives Σ_{x<X} H(x)/(x(x+1)) ≤ Σ_{n<X} f(n)/n². Write that sum as a sum over primes p < X and group n = p·i by K = ⌊log_p i⌋. Each block is ≤ (p^K/p)·Σ_{i≥p^K} 1/i² ≤ 2/p, so prime p contributes ≤ (2/p)(log_p X + 1) ≤ 4 log X/(p log p). The Chebyshev-type bound Σ_{p} 1/(p log p) ≤ 16 comes from dyadic blocks: primes in [2^r, 2^{r+1}) number ≤ 2^{r+2}/r because their product is ≤ primorial(2^{r+1}) ≤ 4^{2^{r+1}}; then Σ 1/r² ≤ 2. So Σ f(n)/n² ≤ 64 log X = 256 log y. Then 600 log y − 200 ≤ 256 log y contradicts log y ≥ log 2 > 0.69.

Axioms: `propext, Classical.choice, Quot.sound`
