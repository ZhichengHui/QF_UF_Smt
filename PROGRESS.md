# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- Solver: Tseitin encoding into a core problem; naive enumeration of the truth values of the atoms, each assignment checked by congruence closure; returns a model or `Unsat`.
- Verification: `QFUF_heap.check_sat_correct` is proved against `spec/`, with no `sorry`; input range `smt_size p <= 2^28` (`smt_in_range`).
- Framework: the code translates with the AutoCorrode front end without placeholders.
- Benchmarks: none yet; the benchmark measurement is being re-established.
- Tests (auxiliary): `core/tests/`, `tools/fuzz.py` against z3.

## Milestones

- 2026-11-07: the core solver `solve` proved
- 2026-11-12: the translation from SMT-LIB problems and the size checks verified; top-level theorem `QFUF_heap.check_sat_correct`
