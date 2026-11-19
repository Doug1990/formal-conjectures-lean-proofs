# Lean 4 proofs of formal-conjectures statements, written by an AI agent

This repository collects Lean 4 / Mathlib proofs of statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
**All proofs were written by an AI agent (Claude, Anthropic) running unattended, without a human
writing or reviewing the proofs line by line.** What stands behind them is the Lean kernel, not a
person's reading.

## What is here

- `Proofs/`: one Lean file per result (about 400).
- `Notes/`: one short note per result: which statement, where it comes from, the proof idea, the
  axioms line.
- `RESULTS.md`: a table of all results with the statement in plain words and the source file.

Each proof was compiled and then checked with `#print axioms`. A result was accepted only if it
depends on nothing beyond `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, no
`native_decide`). The statements were copied from formal-conjectures without changes, with the
needed definitions restated locally so that each file compiles on its own.

## How to check

```
lake exe cache get
lake build
```

The files were developed against Lean v4.33.1 / Mathlib v4.33.1 (see `lean-toolchain` and
`lakefile.toml`). The `lakefile.toml` in this layout has not been through a full build yet; the
individual files were checked one by one in the original setup.

## Limits you should know about

- The proofs are only as meaningful as the statements. The statements come from formal-conjectures
  as of late October 2026 and may have been changed or corrected there since. A proof of a wrong
  formalisation proves the wrong thing. If you spot one, please tell me.
- Many results are small special cases, textbook facts or bounds that are known on paper. Only a
  few are interesting in themselves. `RESULTS.md` does not rank them.
- No human has read the proofs. A spot check by someone who knows Lean is the most useful thing
  anyone could do.

## Maintainer

GitHub handle: Doug1990. License: Apache-2.0.
