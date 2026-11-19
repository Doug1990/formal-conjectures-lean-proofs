# erdos441_ub

- Statement: `Erdos441.erdos_441.variants.erdos_upper_bound` (g(N) ≤ √(4N) + C)
- Source: `FormalConjectures/ErdosProblems/441.lean:113` (category research solved, Erdős 1951)
- Date: 2026-11-11

Proof idea: this is Erdős' argument, with C = 1. Let s = ⌊√N⌋. At most s elements of A are ≤ s. For elements s < a < b of A, gcd(a,b) divides b − a, so ab = gcd·lcm ≤ (b−a)N. This gives ⌊N/b⌋ + 1 ≤ ⌊N/a⌋ (`UB.key`), so a ↦ ⌊N/a⌋ is injective on the large elements. Its values are < s+1, because N < (s+1)² ≤ (s+1)a. So there are at most s+1 large elements, and |A| ≤ 2s+1 ≤ 2√N + 1 = √(4N) + 1 (`UB.card_le`). The sSup is bounded with `csSup_le'`.

Axioms: `'Erdos441.erdos_441.variants.erdos_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

Verified with `.\tools\check.ps1` (1 compile, clean). `g` was restated verbatim, with targeted Mathlib imports instead of FormalConjecturesUtil.
