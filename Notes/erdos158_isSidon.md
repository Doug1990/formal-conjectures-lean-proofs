# erdos158_isSidon

- Statement: `Erdos158.erdos_158.variants.isSidon'` (category research solved, [ESS94])
- Source: `FormalConjectures/ErdosProblems/158.lean` (line 67) in google-deepmind/formal-conjectures
- Proof file: `results/erdos1191_liminf.lean` (shared with `Erdos1191.erdos_1191.variants.liminf_le`, see erdos1191_liminf.md)

## Proof idea
Suppose the liminf is ⊤. Then eventually |A ∩ [0,N)|·N^{-1/2}·(log N)^{1/2} > 2e^8. We have |A ∩ [0,N)| ≤ |A ∩ [1,N]| + 1. When A ∩ [1,N] is nonempty this is at most 2|A ∩ [1,N]|, and when it is empty the inequality fails because log N ≤ N. So eventually e^8·√N ≤ |A ∩ [1,N]|·√(log N). Lemma `LM.core` (the Sidon block-counting / weighted Cauchy–Schwarz / harmonic-sum argument from the 1191 proof) shows that this is impossible for an infinite Sidon set. The checkout's corollary `erdos_158.variants.isSidon` is already proved from isSidon'. Its formal proof was not compiled here.

## Axioms
'Erdos158.erdos_158.variants.isSidon'' depends on axioms: [propext, Classical.choice, Quot.sound]

## Date
2026-11-13
