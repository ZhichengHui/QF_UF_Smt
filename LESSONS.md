# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed.

## Proofs

- **Positional steps after `auto` break when the code changes.** A chain of `metis`/`blast` steps
  that relies on the number and order of the goals `auto` leaves gets reshuffled, or stops
  terminating, when `search` or the simp set changes. Close the cases by name (`subgoal` blocks, or
  one `auto` with the needed intro/dest rules); factor hard steps into small helper lemmas.
  Evidence: review of #34/#36 on #28 (#39, item 5); in #37 the old `metis ext_ok_step` step of
  `search_rec_step_spec` no longer terminated and was replaced by helpers (progress
  `20261118T154116Z_bd2cdd04`).
- **HOL-Library Word has no `word_le_nat_alias`/`word_less_nat_alias`.** From `¬ k ≤ x` to
  `unat x < unat k` use `not_le unat_mono`; for the converse `metis le_less less_asym unat_mono`.
  Evidence: progress `20261118T133000Z_1e50c24b` (#34).

## Pool Server

- **One large proof theory runs the Pool Server out of Java heap** (`OutOfMemoryError` in
  `sync_document`). Keep helper contracts and the main proof in separate theories
  (`QFUF_Contracts` / `QFUF_Proof`) and add new contracts to the smaller one. Evidence: PR #42.
- **A loop with a mutable local plus an early `return` made the Pool Server time out** on its
  contract proof. Prefer plain loops without mutable locals (split the function into two passes if
  needed). Evidence: `clause_unit` in PR #42.

## Generated code and `spec/`

- **A new mutable local can change the generated locale.** The first mutable `usize` local in the
  file reordered the prisms of `QFUF_heap`, which forces a `spec/` change. Before adding a
  mutable local of a type the file does not yet mutate, check whether a version without it works;
  if the locale changes anyway, update `spec/` only as `CLAUDE.md` allows. Evidence: PR #42
  (`clause_unit`).

## Performance and benchmarks

- **Profile before optimising, and measure after every new cut.** The closure took at most 0.07 %
  of the run time until the clause cut (#34) sent more leaves to `theory_check`; a check run at
  every node can cost more than it saves (the closure cut at every node lost eq_diamond6 in #37,
  before propagation removed most nodes in #42). Evidence: progress `20261118T143500Z_d159fd9e`,
  `20261118T154116Z_bd2cdd04`.
- **Compare against main on the same machine load.** Build main and the branch side by side and
  run both suites close together; under load an instance near the limit flips (eq_diamond12:
  25.2 s in one run, timeout in the next). Evidence: PRs #34, #37, #42.
- **`bench/run.sh` cannot check z3's sat models** (`check_model.py` rejects z3's model format and
  reports them WRONG). Compare z3's answers against `:status` only. Evidence: target comment on
  #28, progress `20261118T120101Z_9e18fa7d`.

## Tests

- **Tests guard correctness, not speed.** Removing a cut keeps every test green; only the
  benchmark suite catches it. Some closure bugs (skipping rows of constants, which is unsound
  because `wf_problem` allows duplicate constants; too few `close` rounds) are caught only by
  `core/tests/cuts.rs`, so keep it green when changing the closure or `search`. Evidence: PR #40,
  progress `20261118T155657Z_bac6a2c4`.
