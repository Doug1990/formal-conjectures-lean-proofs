# tensor_maxrank_le

- Statement: `Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank` (category research solved; Blekherman–Teitler, Math. Ann. 2015, Theorem 1)
- Source: `FormalConjectures/Arxiv/0805.3777/TensorRank.lean:328` in the checkout
- Proof idea: let U be the dense open set of tensors of generic rank r, and let T be a tensor of maximal rank R. The map f(A) = T − A is a continuous surjection (an involution), so f(U) is dense. A dense set meets the nonempty open set U, so there is A ∈ U with A = T − B for some B ∈ U. Hence T = B + A with cprank A = cprank B = r. Subadditivity of `Holor.cprank` follows from Mathlib's `Holor.cprankMax_add` plus the `Nat.find` spec and minimality of `cprank` (helper lemmas `cprank_spec`, `cprank_le_of`, `cprank_add_le`). So R ≤ 2r. The definitions `IsGenericRank`, `IsMaxRank` and the scoped topology instance are restated verbatim, and the file uses targeted imports.
- Axioms: `'Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-10-31, 3 compiles (1: `Nat.find_spec` unification for `cprank_spec`; 2: accepted with only a `letI` style lint; 3: clean).
