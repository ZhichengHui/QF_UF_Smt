# QF_UF_Smt

A verified SMT solver for QF_UF with models: Rust code (`core/src/lib.rs`), translated to Isabelle by
the AutoCorrode front end (`urust/`), with the top-level theorem `QFUF_heap.check_sat_correct` proved
in `proof/top/QFUF_Top.thy` against the specification in `spec/`. The SMT-LIB front end `frontend/`
(a git submodule shared with QF_BV_Smt) is trusted, not verified.

## Build and test

These commands work on the PGR compute server, where pod agents run (`tools/pod-remote.sh` sets up
PATH and HOME), and on the user's machine.

- First, in a fresh checkout or worktree: `git submodule update --init` (the front end).
- Rust: `cargo build --release`, `cargo test --release`.
- Proofs: `tools/check.sh` checks every session (on the server it runs there directly; its task
  directory is named after the checkout, so worktrees do not collide). CI runs the same check on
  every pull request.
- Differential testing: `python3 tools/fuzz.py target/release/qfuf z3 200 SEED` (random small
  problems, answers compared with z3, models checked by z3).
- After changing `core/src/lib.rs`: regenerate the translation with
  `$RT/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name QFUF core/src/lib.rs`
  (`RT=/disk/scratch/$(id -un)`; set `RUSTUP_HOME=$RT/rust/rustup`).

## Developing proofs

- Use the Isabelle Pool Server MCP (`isabelle-pool-server`) with the skills
  `isabelle-proof-development` and, for contracts, `autocorrode-contract-proofs`.
- The Pool Server cannot resolve this project's session-qualified imports. Edit the theories in
  `urust/`, `spec/`, `proof/`; run `tools/devcopy.sh`, which writes `dev/` (a flat copy with
  unqualified imports, not committed); check `dev/<Theory>.thy` with the Pool Server, giving its
  absolute path. Re-run `tools/devcopy.sh` after every edit before checking again.
- Close every file you opened with `isabelle_close` before finishing.
- Before opening a pull request, `tools/check.sh` must end with `EXIT 0`, and
  `grep -rnwE 'sorry|oops|quick_and_dirty' spec proof` must find nothing.

## Layout

- `spec/` — the specification; the meaning of `check_sat_correct` depends on nothing else.
- `urust/` — generated; never edit by hand.
- `proof/` — the core solver (`QFUF_*.thy`), its interface (`core_spec/`), the translation model
  (`smt/`), the top level (`top/`).
- `core/`, `cli/` — Rust; `frontend/` — the SMT-LIB front end (submodule); `tools/` — checks,
  fuzzing, evaluation, the pod launcher.

## The specification is fixed

- Do not edit any file in `spec/` or `tools/spec.sha256`, and do not change the `frontend`
  submodule. If a task seems to need such a change, do not make it: comment on the issue explaining
  why, and stop. CI fails when `spec/` differs from `tools/spec.sha256`, and pod refuses to open a
  pull request that touches them.
- This includes the input range `smt_in_range` in `spec/QFUF_Spec.thy`: a change of the solver must
  keep answering (`Sat` or `Unsat`) every problem of the fragment and of the range. Make the solver
  fit the range, never the range fit the solver.
- One part of `spec/` follows the generated code: the locale `QFUF_heap` in `spec/QFUF_Spec.thy` is
  `QFUF_ctx` of `urust/QFUF_Locale.thy` without its last line (the fuel). A change of the Rust code
  that changes that locale (a new type of mutable local) needs a change of `spec/`: do not make it;
  report it on the issue and stop.
- `spec/SMT_Types.thy` and `spec/SMT_Semantics.thy` are the same in the QF_UF_Smt and QF_BV_Smt
  repositories (`SMT_Types.thy` up to its `imports` line).

## Iterate on verified code

- Every change keeps all proofs and the statement of `check_sat_correct`.
- Do not weaken a contract or a lemma used by the top level to make a proof easier; do not delete a
  proved lemma that is still used.
- After three failed attempts with the same approach, change the approach.

## Tests

- A change of behaviour of the Rust code gets a test in `core/tests/` or `cli/tests/`, including
  edge cases (empty problem, single assertion, inputs at the edge of `smt_in_range`). Every `sat`
  answer in a test is checked with the front end's reference evaluator (`check_model`).

## Commits and pull requests

- Prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`, `perf:`.
- One logical change per commit; every commit builds and passes `cargo test`.
- Do not edit `CLAUDE.md`, `PLAN.md`, `.github/` or `.pod/` (pod refuses such pull requests).
