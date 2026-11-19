# erdos263_folk

- Statement: `Erdos263.erdos_263.variants.folklore` (category research solved), source `FormalConjectures/ErdosProblems/263.lean:93`.
- Claim: if a_n^(1/2^n) → ∞ (no monotonicity assumed, and a_n = 0 is allowed), then Σ 1/a_n is irrational.

Proof idea: let L_m = log max(a_m, 1). Order ℕ by the lexicographic key (L_m, m), so every n has a finite predecessor set pred(n), and let S_n = Σ_{m ∈ pred n} L_m. Suppose the sum equals p/q. Take the head pred(n). Then q·∏_{pred n} b_m·tail is a positive integer. The tail consists of terms with L_m ≥ L_n, which gives tail ≤ e^{−L_n}(N1 + L_n + 3). So for every n, L_n ≤ S_n + C + log(1 + L_n). Strong induction on #pred(n) (the predecessor of maximal key gives pred(p) = pred(n) \ {p}) then shows S_n + L_n ≤ B·2^{#pred n} − #pred n − v, with B = 12 + 6C and v = 2 + C + log(1 + 2B). This works because the slack log(1 + L_n) grows only linearly in #pred(n). Now take n of maximal key among 0..N2. It has ≥ N2 predecessors, and some m ∈ pred(n) ∪ {n} has m ≥ #pred(n). For that m, L_m ≤ B·2^m, which contradicts L_m/2^m → ∞.

Axioms: `'Erdos263.erdos_263.variants.folklore' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles with targeted imports (no `import Mathlib`), with no errors and no warnings. Date: 2026-11-12. 2 compile attempts.
