# Erdos1026.erdos_1026 and Erdos1026.erdos_1026.variants.upper_bound

Source: `FormalConjectures/ErdosProblems/1026.lean`, lines 94 and 101 (both tagged research solved).

Proof idea. Upper bound (Cambie-type construction): suppose c > 1 is admissible. Take ε = (c−1)/2 and k large, and set n = k². The sequence has k blocks of k entries. Entry i gets the value x_i = k³ + (k−1−⌊i/k⌋)k + (i mod k). Values increase inside a block and decrease from one block to the next, and they are all distinct. An increasing subsequence stays inside a single block. A decreasing subsequence uses at most one entry per block. So every monotone subsequence has at most k terms (an injection into range k via i mod k or ⌊i/k⌋). Its sum is therefore at most k(k³+k²), while Σx ≥ k⁵. Admissibility would give (c−ε)k⁴ ≤ k⁴ + k³, which fails once k > 2/(c−1). The main statement IsGreatest admissibleConstants 1 combines this bound with `WES.mem_of_le_one` (the area/Cauchy–Schwarz lower bound from results/erdos1026_lb.lean, included verbatim in this file).

Axioms (both theorems): [propext, Classical.choice, Quot.sound]

Verified file: work/erdos1026_ub.lean. This file is a hand copy of it.

Date: 2026-11-09
