# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- Solver: Tseitin encoding into a core problem; depth-first enumeration of the truth values of the
  atoms, with two cuts on the partial assignment of atoms `0..k`: a falsified clause, and (after an
  atom set true) a congruence-closure conflict. Each leaf is checked by congruence closure; returns a
  model or `Unsat`. No propagation, no learning, no incremental closure: the search is still
  exponential in the worst case, and each node rescans every clause, and each closure check starts from scratch.
- Verification: `QFUF_heap.check_sat_correct` is proved against `spec/`, with no `sorry`; input range
  `smt_size p <= 2^28` (`smt_in_range`). The cuts are proved sound (`ext_ok_clause_false`,
  `ext_ok_cc_conflict`); `search_contract` and the top-level theorem did not change. Some proof steps
  (`search_rec_step_spec`, `clause_falsified_spec`) are positional `metis`/`blast` after `auto`, so
  they are fragile (review on #28).
- Framework: the code translates with the AutoCorrode front end without placeholders.
- Benchmarks: active suite `QF_UF_Smt-2026-11-18` (101 SMT-LIB 2024 QF_UF instances, 30 s / 4 GiB).
  Target z3 5.4.1: 101/101 in 3.52 s. qfuf (after #37): 63/101 (sat 26, unsat 37), 0 WRONG.

  | family | n | qfuf | | family | n | qfuf |
  |---|---|---|---|---|---|---|
  | 20170829-Rodin | 34 | 34 | | eq_diamond | 20 | 6 |
  | 2018-Goel-hwbench | 10 | 10 | | QG-classification | 10 | 0 |
  | 20190906-CLEARSY | 10 | 10 | | SEQ | 6 | 0 |
  | TypeSafe | 3 | 3 | | NEQ / PEQ | 4 / 4 | 0 / 0 |

  Gap to the target: 38 instances. eq_diamond needs a disequality that comes last in the atom order,
  so prefix cuts do not help; QG/SEQ/NEQ/PEQ need propagation or CDCL. `bench/run.sh` cannot check
  z3's sat models, so the z3 row compares answers only.
- Tests (auxiliary): `core/tests/solve.rs`, `core/tests/cuts.rs` (cuts and closure, answers checked
  against z3; removing a cut keeps them green, the suite guards speed), `tools/fuzz.py` against z3.

## Milestones

- 2026-11-07: the core solver `solve` proved
- 2026-11-12: the translation from SMT-LIB problems and the size checks verified; top-level theorem `QFUF_heap.check_sat_correct`
- 2026-11-18: first benchmark suite and `bench/run.sh` (#25), activated (#27), renamed
  `QF_UF_Smt-2026-11-18` (#30); target z3 101/101 in 3.52 s, qfuf 39/101 (#28)
- 2026-11-18: search cuts on a falsified clause, 39 → 59/101 (#34)
- 2026-11-18: congruence closure compares each pair once, −20 % time on the 59 solved (#36)
- 2026-11-18: search cuts on a congruence-closure conflict of the prefix, 59 → 63/101 (#37)
- 2026-11-18: regression tests for the cuts and the closure (#40); prism lists in `spec/` follow
  the implementation (#41)
