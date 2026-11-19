# Erdos441.erdos_441.variants.lower_bound

- Source: FormalConjectures/ErdosProblems/441.lean:107 (category research solved)
- Statement: `∃ C : ℝ, ∀ N : ℕ, √(9 / 8 * N) - C ≤ g N`

Proof idea: with s = ⌊√⌊N/2⌋⌋ (so 2s² ≤ N), take A = [1, s] ∪ {2j : s/2 < j ≤ s}
(a variant of Erdős' construction). Any two elements have lcm ≤ N: lcm ≤ product ≤ 2s² in
the mixed and small cases, and lcm(2i, 2j) = 2·lcm(i, j) ≤ 2ij ≤ 2s² for two even elements.
The two parts are disjoint, so |A| = s + (s − ⌊s/2⌋) ≥ 3s/2, and g N ≥ |A| by le_csSup
(the set of sizes is bounded by N). Since ⌊N/2⌋ < (s+1)², N ≤ 2(s+2)², hence
√(9N/8) ≤ (3/2)(s+2) ≤ |A| + 3. So C = 3 works.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-11 (2 compiles). Verified file: work/erdos441_lb.lean (identical copy).
