# bondy_one

- Statement: `Arxiv.«2606.03696».bondy_conjecture.variants.one` (category research solved; Bondy's conjecture for k = 1, which is Dirac's theorem)
- Source: `FormalConjectures/Arxiv/2606.03696/BondyLongestCycles.lean:74`
- Date: 2026-11-01
- Compiles: 3 (1: `simp only` no-op, `rw [if_neg (by omega)]` hit the wrong `ite`, `isPath_copy` did not fire under simp; 2: stuck DecidablePred from a `_` filter predicate; 3: clean apart from the linter note on the statement's unused binder `hP`)

**Proof idea.** The conclusion `P.support.length + 1 ≤ 1` is false for any walk, so the proof shows there is no vertex off a longest cycle C, i.e. Dirac's theorem. Paths are encoded as functions `g : ℕ → V` that are injective on `[0, m]` with consecutive vertices adjacent (`IsP`). Take a longest path (`Nat.findGreatest`). All neighbours of both endpoints lie on it. Then δ ≥ n/2 and pigeonhole on the index sets A = {i < m | g0 ~ g(i+1)} and B = {i < m | gm ~ gi} give the usual crossing index, which turns the path into a cycle on the same vertex set (`cycle_of_max`). If that cycle misses a vertex, connectivity (`IsKConnected G 1` with S = ∅, plus `Walk.exists_boundary_dart`) gives an edge leaving it, and the cycle "opened" at that edge is a longer path (`extend`). So there is a Hamiltonian cycle, built with `Walk.ofSupport` and `isCycle_iff_isPath_tail_and_le_length`. Its length n is at most `circumference = C.length ≤ n − 1` (C misses u). Contradiction. `IsKConnected`, `cycleLengths`, `circumference` and `offWalk` are restated verbatim from FormalConjecturesForMathlib / the source file, and the file uses targeted imports.

**Axioms:** `'Arxiv.«2606.03696».bondy_conjecture.variants.one' depends on axioms: [propext, Classical.choice, Quot.sound]`

Reusable: `IsP`, `len_bound`, `exists_max`, `head_nbr`/`tail_nbr` (endpoint neighbours of a longest path), `cycle_of_max` (Dirac/Ore crossing), `extend`, `reach_of_conn`, `bdd_cycles`. These are the starting point for `variants.two` (Nash-Williams, much harder).
