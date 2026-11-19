# Erdos945.erdos_945.variants.equivalence

- Source: `FormalConjectures/ErdosProblems/945.lean:74` (category textbook)
- Date: 2026-10-30
- Compiles: 2 (1st: two small errors; 2nd: clean)

Proof idea. (Constant ⇒ Prop) Take O ≡ C+1. Let n+1..n+k ≤ x be a run with distinct τ. If k > N₀+1+(log x)^C (N₀ = ⌈max X₀ 1⌉), the interval [m, m+(log m)^C], m = max(n+1, N₀) ≥ X₀, lies inside (n, n+k] and contains a≠b with τa = τb, a contradiction. So k ≤ N₀+1+(log x)^C ≤ (log x)^{C+1} once log x ≥ N₀+2, and F x ≤ that bound via `csSup_le'`. (Prop ⇒ Constant) With |O| ≤ c eventually and c' = max c 0, take C = c'+1 and L = (log x)^{c'+1} ≤ x (from `isLittleO_log_rpow_rpow_atTop`). If [x, x+L] had no repeated τ, the ⌊L⌋ integers ⌈x⌉..⌈x⌉-1+⌊L⌋ would form a run ending ≤ y = x+L, so L−1 < ⌊L⌋ ≤ F y ≤ (log y)^{c'} ≤ 2^{c'}(log x)^{c'} (y ≤ x²). That contradicts (log x)^{c'+1} ≥ (2^{c'}+2)(log x)^{c'} for log x ≥ 2^{c'}+2.

Axioms: `'Erdos945.erdos_945.variants.equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]`

Note: definitions are restated locally with targeted imports (no FormalConjecturesUtil); the `category` attributes and the open sorried statements are omitted.
