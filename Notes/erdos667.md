# Erdős 667: monotoneOn and endpoint

- Statements: `Erdos667.erdos_667.variants.monotoneOn` (category textbook, line 89) and
  `Erdos667.erdos_667.variants.endpoint` (category research solved, line 99)
- Source: `FormalConjectures/ErdosProblems/667.lean` in the checkout
- Proof file: `results/erdos667.lean` (defs `LocallyDense`, `H`, `c` restated verbatim, targeted imports)

**Proof idea.** monotoneOn: for q ≤ q' every (p,q')-locally dense graph is (p,q)-locally dense, so
`H p q n ≤ H p q' n` (`Nat.findGreatest_mono_left`). The ratios log H / log n lie in [0,1]
(H ≤ n), so the real liminf is monotone (`liminf_le_liminf` with explicit boundedness).
Endpoint: write p = r+2. In a (r+2, C(r+1,2)+1)-locally dense graph, a vertex v with r+1
non-neighbours gives an (r+2)-set whose G-edges all avoid v, so it spans at most C(r+1,2) edges
(`edge_le`), which is a contradiction. So every vertex has at most r non-neighbours, and a greedy
argument (`greedy`) gives a clique of size ≥ n/(r+1). Hence ⌈n/(r+1)⌉ ≤ H(n) ≤ n, and
1 − log(r+1)/log n ≤ log H/log n ≤ 1. Squeezing shows the ratio tends to 1, so the liminf is 1.

`#print axioms`, both theorems: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29. Compiles: monotoneOn 2 (standalone draft), endpoint 2, combined file 1.
