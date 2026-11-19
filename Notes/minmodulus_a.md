# minmodulus_a

- Statement: `Arxiv.«2607.08366».exists_isValidMod_minModulus` (Theorem A, Fonollosa 2026), category research solved
- Source: `FormalConjectures/Arxiv/2607.08366/MinModulus.lean:98` in the checkout
- Date: 2026-11-03

## Proof idea

Write n = p+1, L = ⌊log₂ n⌋, N = 2ⁿ − 2^L. The set is A = {2^k − 1 : k < n} mod N. All 2^k − 1 < 2^{n−1} ≤ N, so |A| = n. Let m_k be the multiplicities and T = Σ m_k 2^k. The hypotheses give Σ m_k = n and T ≡ 2ⁿ − 1 ≡ 2^L − 1 (mod N). The main tool is g_p(x) = ⌊x/2^p⌋ + popcount(x mod 2^p), the least number of powers of two ≤ 2^p that sum to x. It is defined by a recursion and is subadditive, and `key` shows Σ m_k ≥ g_p(T). Since T ≥ n ≥ 2^L, we get T = 2^L − 1 + (i+1)N, and then T + 2^L·i = 2^p(2i+1) + (2^p − 1). That gives 2i + 1 + p = g_p(T + 2^L i) ≤ g_p(T) + g_{p−L}(i) ≤ n + i, so i = 0 and T = 2ⁿ − 1. Finally, `uniq` uses induction (parity of m₀ plus `key`) to show that n powers of two summing to 2ⁿ − 1 must be 1, 2, …, 2^{n−1}, each used once. No digit-sum or p-adic library is needed. The upstream external proof (jarfo/min-modulus) is about 800 lines; this one is self-contained and about 250 lines.

## Axioms

`'Arxiv.«2607.08366».exists_isValidMod_minModulus' depends on axioms: [propext, Classical.choice, Quot.sound]`

Defs `IsValidMod` and `minModulus` are restated verbatim (targeted imports instead of FormalConjecturesUtil).
