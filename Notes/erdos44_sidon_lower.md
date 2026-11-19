# Erdos44.sidon_set_lower_bound

- Statement: `Erdos44.sidon_set_lower_bound` (category textbook), checkout file `FormalConjectures/ErdosProblems/44.lean:129`.
  For every N ≥ 1 there is a Sidon set A ⊆ {1, …, N} with √N/2 ≤ |A|.
- Verified file: `work/erdos44_lower.lean`. This copy is identical to it.

## Proof idea
The proof uses Bose's construction with discrete logarithms in GF(p²) = `GaloisField p 2`. Let θ be a generator of the cyclic unit group. θ does not lie in the prime field: otherwise every element would, and p² ≤ p. Hence θ + x ≠ 0 for every x ∈ ZMod p. Write θ + x = θ^{e(x)} with e(x) < ord θ ≤ p². The set A = {e(x) + 1} has p elements, since e is injective, and lies in [1, p²]. It is Sidon over ℕ because e(x)+e(y) = e(u)+e(v) gives (θ+x)(θ+y) = (θ+u)(θ+v). Comparing coefficients then gives x+y = u+v (otherwise θ would lie in the prime field) and xy = uv, so {x,y} = {u,v}. No modular reasoning is needed. For N with s = ⌊√N⌋ ≥ 2, Bertrand gives a prime p with s/2 < p ≤ 2⌊s/2⌋ ≤ s. So p² ≤ N and 2p ≥ s+1 > √N. For s = 1 the set {1} works.

Reusable: `Erdos44.Bose.key` (generic over any field embedding), `Bose.exists_sidon` (Sidon set of size p in [1, p²] for every prime p).

## Axioms
'Erdos44.sidon_set_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-05. Compiles: 2 (1st clean except a `haveI` style lint; 2nd clean + axioms).
