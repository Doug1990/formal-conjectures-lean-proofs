# Erdos1209.erdos_1209.parts.iii.a

- Source: `FormalConjectures/ErdosProblems/1209.lean:196` (category research solved)
- Statement: there is no n ∈ ℕ such that n + 2^(2^k) is prime for every k.

**Proof idea.** If n is even, then n + 4 (k = 1) is even and ≥ 4. If n = 1, then n + 2^32 = 641 · 6700417 (Euler's factor of F₅). For odd n ≥ 3, let p = n + 2^(2^n) and write p − 1 = 2^s·t with t odd. Since 2^min(s, n) divides both p − 1 and 2^(2^n), it divides n − 1 < 2^n, so s < n. Let k' = n + φ(t). Then 2^(k') − 2^n = 2^n(2^φ(t) − 1) is divisible by 2^s·t = p − 1 (Euler mod t). By Fermat mod p this gives 2^(2^k') ≡ 2^(2^n), so p divides n + 2^(2^k'). That number is a prime strictly larger than p, which is a contradiction. The Fermat-number factorisation is the only computation; everything else is elementary.

- Axioms: `propext, Classical.choice, Quot.sound`
- Compiles: 2 (1: one rewrite-order error; 2: clean + `#print axioms`)
- Date: 2026-11-09
