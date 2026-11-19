# erdos231

- Statement: `Erdos231.erdos_231` (category research solved), source `FormalConjectures/ErdosProblems/231.lean:121` in the checkout.
- Verified file: `work/erdos231.lean`. `results/erdos231.lean` is an identical copy. The definition `ContainsAbelianSquare`, the API lemma `containsAbelianSquare_iff` and the `Decidable` instance are copied from the source file.

Proof idea: the statement is the negation of "every string of length 2^k − 1 over k letters contains an abelian square". As the source docstring notes, k = 2 already gives a counterexample: the string [0,1,0] has no abelian square. Its decidability, via the block characterisation `containsAbelianSquare_iff`, is checked with `decide +kernel`. No `native_decide` is used. This is a cheap proof because of how the question is formalised (the interesting cases are k ≥ 4). The tag is research solved, not open, so it is not suspicious.

Axioms: `'Erdos231.erdos_231' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-10
