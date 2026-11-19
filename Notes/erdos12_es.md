# erdos12_es

- Statement: `Erdos12.erdos_12.variants.erdos_sarkozy` (category research solved, Erdős–Sárközy)
- Source: `FormalConjectures/ErdosProblems/12.lean:104` in the checkout
- Date: 2026-11-14

Proof idea: A is a union of blocks B_k = {1 + M_k·t : 2T_k ≤ t < 3T_k}, where M_0 = 1 and
M_{k+1} = U_k!, with U_k = 1 + 3M_kT_k an upper bound for block k. Every earlier element
therefore divides M_l, so every element of a later block is ≡ 1 modulo every earlier element.
T_{k+1} > U_k is chosen (Classical.choose, from f → ∞) so that f(U_k) > 3M_k + 1. Goodness for
a < b, c with a | b + c and b ≠ c:
- all three in one block: 2a < b + c < 3a, because the block's max/min ratio is < 3/2;
- b in a's block and c later: a | b + 1, but a < b + 1 < 2a;
- both later: a | 2, but a ≥ 3.

Density: block k lies in [1, U_k] and has T_k elements, and U_k/f(U_k) < T_k. Since U_k is
strictly increasing, this holds for infinitely many N.

Axioms: `[propext, Classical.choice, Quot.sound]`
