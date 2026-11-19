# VoronovskajaTypeFormula.voronovskaja_theorem.bernstein_operators

- Source: `FormalConjectures/Paper/VoronovskajaTypeFormula.lean:448` (category research solved; this is the classical Voronovskaja theorem, the α = 1 case)
- Verified file: `results/voronovskaja.lean` (copy of `work/voronovskaja.lean`; targeted imports; `bernsteinTail` / `bezierBernstein` restated word for word; `@[category]` attribute dropped)

**Proof idea.** For α = 1, `rpow 1` drops out and `J_{n,k} − J_{n,k+1}` is the Bernstein basis polynomial b_{n,k}, so B_n f(x) = Σ f(k/n) b_{n,k}(x). The raw moments Σ k^i b_{n,k} for i ≤ 4 come from a shift identity, (n+1)·C(n,k) = C(n+1,k+1)·(k+1), and induction. They give the central moments Σ(k/n−x)b = 0, Σ(k/n−x)²b = x(1−x)/n and Σ(k/n−x)⁴b = x(1−x)(1+3(n−2)x(1−x))/n³ ≤ 1/n². Mathlib's Peano-form Taylor theorem (`taylor_isLittleO`, n = 2 on I) writes f(t) = f(x) + f'(x)(t−x) + ½f''(x)(t−x)² + R(t) with R = o((t−x)²). Compactness of I plus that little-o bound gives |R(t)| ≤ ε(t−x)² + K(t−x)⁴ on all of I. So n(B_n f(x) − f(x)) = ½x(1−x)f''(x) + nΣR(k/n)b, and the error term is at most ε/4 + K/n.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-01. 3 compiles (1: three unknown lemma names and a swapped `add_le_add_left`; 2: lint only; 3: clean + axioms).
