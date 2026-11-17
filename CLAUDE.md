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
  directory is named after the checkout, so worktrees do not collide). CI runs it on every pull request;
  you need not run it before opening one.
- Differential testing: `python3 tools/fuzz.py target/release/qfuf z3 200 SEED` (random small
  problems, answers compared with z3, models checked by z3).
- After changing `core/src/lib.rs`, or when CI's `translation up to date` fails: regenerate
  `urust/` with the newest front end (never pinned): `git -C $RT/AutoCorrodeRustFrontEnd pull -q`,
  `cargo build --release` there, then
  `$RT/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name QFUF core/src/lib.rs`.
  If the new translation breaks `spec/`, do not change `spec/`: report it on the issue and stop.

## Developing proofs

- Use the Isabelle Pool Server MCP (`isabelle-pool-server`) with the skills
  `isabelle-proof-development` and, for contracts, `autocorrode-contract-proofs`.
- The Pool Server cannot resolve this project's session-qualified imports. Edit the theories in
  `urust/`, `spec/`, `proof/`; run `tools/devcopy.sh`, which writes `dev/` (a flat copy with
  unqualified imports, not committed); check `dev/<Theory>.thy` with the Pool Server, giving its
  absolute path. Re-run `tools/devcopy.sh` after every edit before checking again.
- Close every file you opened with `isabelle_close` before finishing.
- Before opening a pull request, every theory you changed checks in the Pool Server without
  errors, and
  `grep -rnwE 'sorry|oops|quick_and_dirty' spec proof` must find nothing, and `tools/check-spec.sh`
  must pass.

## Layout

- `spec/` — the specification; the meaning of `check_sat_correct` depends on nothing else.
- `urust/` — generated; never edit by hand.
- `proof/` — the core solver (`QFUF_*.thy`), its interface (`core_spec/`), the translation model
  (`smt/`), the top level (`top/`).
- `core/`, `cli/` — Rust; `frontend/` — the SMT-LIB front end (submodule); `tools/` — checks,
  fuzzing, evaluation, the pod launcher.

## Rules

The rules of this repository are in `PLAN.md` (the specification and its input range, the front
end, verified code, the trusted base); follow them. In practice:

- After regenerating `urust/`, run `tools/check-spec.sh`. If it reports that the locale `QFUF_heap`
  differs from the generated one, update that locale in `spec/QFUF_Spec.thy` to match exactly (and
  say so in the pull request). That is the only change of `spec/` you may make.
- If a task seems to need any other change of `spec/`, or a change of the `frontend` submodule, do
  not make it: comment on the issue explaining why, and stop.
- After three failed attempts with the same approach, change the approach.

## Tests

- A change of behaviour of the Rust code gets a test in `core/tests/` or `cli/tests/`, including
  edge cases (empty problem, single assertion, inputs at the edge of `smt_in_range`). Every `sat`
  answer in a test is checked with the front end's reference evaluator (`check_model`).

## Commits and pull requests

- Prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`, `perf:`.
- One logical change per commit; every commit builds and passes `cargo test`.
- Write the progress entry of the session in `progress/` (pod's worker flow) and commit it with
  the change.
- Do not edit `CLAUDE.md`, `PLAN.md`, `tools/spec.sha256`, `tools/check-spec.sh`, `.github/`,
  `.pod/` or the `frontend` submodule (pod refuses such pull requests).
