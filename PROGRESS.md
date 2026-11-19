# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

State of main `37f45e8` (after #69). PR #70 (#67) is open: watched literals, per-symbol closure
scans and a conflict-driven decision order, which it measures at 95 → 99/101. It is not described
below.

- Solver pipeline (`core/src/lib.rs`):
  1. `check_sat` runs equality elimination on the SMT-LIB problem (`eliminate`, #60). A constant
     whose every occurrence is a side of an equality with another constant inside one positively
     placed conjunction is renamed to its partner. `restore` maps a model back.
  2. Tseitin encoding into a core `Problem` (atoms are equalities between terms).
  3. `cdcl` (#61), a recursive search with one call per propagation step or decision:
     - unit propagation by rescanning every clause at every node (problem and learned clauses);
     - theory propagation from the congruence closure (#56): an atom whose sides are joined is set
       true; an atom whose sides lie in the classes of a false atom's sides is set false;
     - an incremental closure (#65): the partition and its merge log are carried down the
       recursion, and only rows whose arguments changed representative are rescanned;
     - learned clauses from closure conflicts, explained by a path in the merge log (#54) and
       confirmed by a restricted closure `rows_join`. If that fails, the clause falls back to all
       true atoms (sound, but weak);
     - 1UIP-style analysis (`analyze`) with backjumping returned as a jump level;
     - the decision order is the first unset atom;
     - the old `search` (unit + theory propagation, learning, chronological) stays as a fallback
       for a jump target whose learned clause is neither unit nor false (it should not happen).
  4. Leaves are confirmed by the closure; the answer is a model or `Unsat`.
- Verification: `QFUF_heap.check_sat_correct` is proved against `spec/` with no `sorry`. The input
  range is `smt_size p <= 2^28` (`smt_in_range`). `spec/` changed only by the locale and prism-list
  updates that `CLAUDE.md` allows (`prism_17`, #60; prism lists, #41).
  - Session `QFUF_Proof`: `QFUF_Pure` (partial assignments `pext`, `clause_ok`, closure facts),
    `QFUF_Contracts`, `QFUF_Explain` (merge log, path explanations, learned clauses),
    `QFUF_Propagate` (theory propagation), `QFUF_Analyze` (resolution `lits_ok_resolve`, sound
    whatever the reason records say), `QFUF_Incremental` (invariant `rep_for`: each carried class
    lies in the closure of the true atoms), `QFUF_Proof` (`search_contract`, `cdcl_contract`,
    `solve_spec`).
  - Session `QFUF_Top`: the SMT-LIB translation and size bounds, `QFUF_ElimSem`/`QFUF_ElimRefine`
    (elimination preserves satisfiability, `restore` gives a model), `QFUF_Top`.
  - Soundness of explanations rests on `rows_join` alone; `path_explain` and the merge log carry no
    invariant. Closedness of the incremental partition is not proved: it matters only for speed.
  - Fragile proof steps still open (reviews #58 and #62 on #28):
    `scan_row_in_spec`, `log_row_spec` (`QFUF_Explain`) and similar `scan_row_spec` steps end with
    `apply (meson wf_args order.strict_trans)+` after `auto`. `joined_unset_spec` and
    `false_pairs_spec` end with `apply (metis wf_atom)+`. `search_rec_step_spec` and
    `cdcl_rec_step_spec` (`QFUF_Proof`) depend on the goal shapes a large `auto` leaves; the
    latter's rule chain ends in `?` (`QFUF_Proof.thy:292`). Other follow-ups from #58: `scan`'s
    result is dead but still proved, `log_close` lacks #55's skip of constant rows, and the
    row/round loop exists in four copies.
- Framework: the code translates with the AutoCorrode front end without placeholders. Functions
  with mutable `Vec` locals sit at the end of `lib.rs` to keep the generated locale stable
  (ZhichengHui/AutoCorrodeRustFrontEnd#20).
- Benchmarks: active suite `QF_UF_Smt-2026-11-18` (101 SMT-LIB 2024 QF_UF instances, 30 s / 4 GiB).
  Target z3 5.4.1: 101/101 in 3.52 s. qfuf on main: **95/101, 0 WRONG**. Time on the 95 solved:
  12.37 s (#65's measurement) and 11.26 s (#70's baseline run of `68014f5`). #69 changed proofs
  only.

  | family | n | qfuf | | family | n | qfuf |
  |---|---|---|---|---|---|---|
  | 20170829-Rodin | 34 | 34 | | eq_diamond | 20 | 20 |
  | 2018-Goel-hwbench | 10 | 10 | | QG-classification | 10 | 10 |
  | 20190906-CLEARSY | 10 | 10 | | SEQ | 6 | 6 |
  | TypeSafe | 3 | 3 | | NEQ / PEQ | 4 / 4 | 0 / 2 |

  Unsolved: NEQ 4/4 and PEQ018_size4/5. #65 found these are limited by unit propagation (a full
  clause rescan and state copies at every node) and by closure rescans. #70 targets both and leaves
  NEQ016_size6 and PEQ018_size5 (99/101). On its 95 solved instances qfuf takes about 3× z3's time for all 101. `bench/run.sh` cannot
  check z3's sat models, so the z3 row compares answers only.
- Tests (auxiliary): `core/tests/` (`solve`, `cuts`, `search`, `learn`, `propagate`, `backjump`,
  `elim`, `incremental`). Answers are checked against z3, and several tests guard speed with time
  limits. `tools/fuzz.py` runs against z3. Speed-only mutants (for example, no true theory
  propagation) are not caught by tests since backjumping (#62); only the suite catches them.
- Limits: the solver is still exponential in the worst case (no restarts, no clause deletion,
  static decision order). The number of learned clauses is unbounded (`clauses_ok` puts no bound on
  them). The elimination handles only constant–constant equalities in one positive conjunction.

## Milestones

- 2026-11-07: the core solver `solve` proved
- 2026-11-12: the translation from SMT-LIB problems and the size checks verified; top-level theorem `QFUF_heap.check_sat_correct`
- 2026-11-18: first benchmark suite and `bench/run.sh` (#25), activated (#27), renamed
  `QF_UF_Smt-2026-11-18` (#30); target z3 101/101 in 3.52 s, qfuf 39/101 (#28)
- 2026-11-18: search cuts on falsified clauses and closure conflicts, 39 → 63/101 (#34, #36, #37);
  regression tests (#40); prism lists in `spec/` follow the implementation (#41)
- 2026-11-18: unit propagation on a partial assignment, 63 → 78/101 (#42); analysis of the
  unsolved instances (#52)
- 2026-11-19: learned clauses from closure conflicts, explained by a merge log, 79 → 84/101 (#54);
  the closure skips constant rows after its first round (#55)
- 2026-11-19: theory propagation from the closure, 84 → 87/101 (#57)
- 2026-11-19: `cdcl` with 1UIP-style analysis and backjumping, 87 → 90/101 (#63)
- 2026-11-19: equality elimination before the encoding, 90 → 95/101, eq_diamond 20/20 (#66)
- 2026-11-19: incremental closure and closure reasons from the carried log, −71 % time on the
  95 solved (#68)
- 2026-11-19: reviews with tests and proof clean-ups (#53, #59, #69)
