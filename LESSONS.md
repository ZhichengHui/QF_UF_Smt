# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed.

## Proofs

- **Do not rely on the number or order of the goals `auto`/`crush_base` leave.** Positional
  `metis`/`meson … +` steps and positional `subgoal` blocks break, or stop terminating, when the
  code or the simp set changes. Instead state step lemmas in the exact form of the goals and apply
  them per goal: `all (solves (rule l1 l2 … ; assumption))`. Do not use `(rule …; assumption)+`: it
  stops silently at the first goal it cannot close. Goals can come back from `auto` as
  `¬ P ⟹ False`; handle them with `rotate_tac -1, erule notE` before the rules. Evidence: review
  of #34/#36 (#39, item 5); progress `20261118T154116Z_bd2cdd04` (#37),
  `20261119T070034Z_28140c14` (#57), `20261119T195542Z_3f029562` (#62),
  `20261119T225953Z_121f1554` (#70).
- **`auto` with new invariants unfolded may not terminate.** Keep the facts behind definitions with
  one intro rule per loop step (`row_joined_merge`, `consts_below_step`, …); the one-`auto` proof
  shape then still works. Evidence: progress `20261119T053304Z_2f579a37` (#55).
- **Shape contracts so `crush_base` and `auto` have little to do.**
  - Post-conditions as list equality (`r = (t1 ≠ t)`, `r = <HOL function>`) rather than pointwise
    `∀i`: `auto` substitutes them and leaves far fewer goals (#57, `20261119T070034Z_28140c14`;
    #66).
  - A loop whose ghost parameters `crush` instantiates too early: put an existential reference
    state in the precondition (as for `finish`); subgoals then gain parameters for it
    (`subgoal for g1 v1 … ref`) (#54, `20261119T014358Z_92cc04c7`).
  - Write pure helpers functionally (slices in, vectors out). `&mut` flag vectors made
    `crush_base` lose the frame of two references (#63, `20261119T120352Z_1db58506`).
  - Contracts of heuristic code (explanations, watch lists, decision order) need only lengths and
    the no-abort property, if soundness is re-checked by a verified function (`rows_join`,
    `clause_unit`, `congruent`). This kept #54, #63, #68 and #70 provable.
- **`simp` does not rewrite inside `if` branches** (default `if_weak_cong`); add `cong: if_cong`.
  Evidence: progress `20261119T131724Z_8c149aa4` (#66).
- **Name clashes:** `start` is a constant (of `range`), so a variable of that name in a lemma is a
  type error (#70). HOL-Library Word has no `word_le_nat_alias`/`word_less_nat_alias`: from
  `¬ k ≤ x` to `unat x < unat k` use `not_le unat_mono`; for the converse
  `metis le_less less_asym unat_mono` (#34, `20261118T133000Z_1e50c24b`).

## Pool Server and heaps

- **One large proof theory runs the Pool Server out of Java heap** (`OutOfMemoryError` in
  `sync_document`). Put each feature in its own theory between the existing ones (as
  `QFUF_Explain`, `QFUF_Propagate`, `QFUF_Analyze`, `QFUF_Incremental`, `QFUF_Watch`). Evidence:
  PR #42.
- **Use a task heap, and put every finished theory in it before working on the next.** Without
  one, opening a late theory failed (HTTP 500) or kept the task group `busy` for ~15 min while a
  scratch session loaded slow theories. Rules:
  - `isabelle_build_heap` on `dev/` needs a `ROOT` there,
    `session "X" = "AutoCorrode" + sessions "Micro_Rust_Std_Lib" theories …`, and the
    `urust/*_Template.thy` files; without them the parent is HOL and the build fails with
    "Bad import of theory Micro_Rust_Std_Lib…".
  - A theory in the heap cannot be checked from a working copy, even renamed (the locale
    `QFUF_ctx` already has its declarations). Put only theories that will not change in the heap.
  - After a heap rebuild, `isabelle_multi_attempt` scratch sessions may still use the old heap;
    test steps by editing the file.
  Evidence: progress `20261119T014358Z_92cc04c7`, `20261119T070034Z_28140c14`,
  `20261119T082705Z_be983059`, `20261119T120352Z_1db58506`, `20261119T131724Z_8c149aa4`,
  `20261119T225953Z_121f1554`.
- **When the Pool Server is down** (`server_recovering`, HTTP 500; #55, #58, #63, #68), check in
  batch on a task heap: build the unchanged theories with `isabelle build -b`, check the changed
  theory in a session on top of it, and replace `sorry` with `by fail` in a scratch copy so the log
  prints the goals `crush_base` leaves (25–45 s per check). A batch build has no time limit per
  step, so one slow step can hide for 10 min: run it under `timeout`, and prefer the Pool Server
  whenever it works. Evidence: progress `20261119T181050Z_7980a6dd` (#68),
  `20261119T225953Z_121f1554` (#70).

## Generated code, front end and `spec/`

- **A new mutable local type can change the generated locale.** The first mutable local of a type
  the file did not yet mutate reorders the prisms of `QFUF_heap` if its function comes early in
  `lib.rs`. Put new functions with new mutable local types at the end of `lib.rs`; then the locale
  is unchanged (#54, #57, #63). If a new type is unavoidable (`Vec<SmtTerm>` added `prism_17` in
  #66), update the locale and prism lists only as `CLAUDE.md` allows. Evidence: PR #42,
  progress `20261119T014358Z_92cc04c7`, `20261119T131724Z_8c149aa4`.
- **A loop with a mutable local plus an early `return` made the Pool Server time out** on its
  contract. Prefer plain loops without mutable locals (two passes if needed). Evidence:
  `clause_unit` in PR #42.
- **Front-end limits:** calls with more than 16 arguments become placeholders; bundle arguments
  into tuples or a queue. `vec![x]` generates stubs (`Box::new_uninit`); use a helper such as
  `one(x)`. Derived `Clone` and `PartialEq` are fine (identity and HOL equality). Evidence:
  progress `20261119T225953Z_121f1554` (#70), `20261119T131724Z_8c149aa4` (#66).

## Solver approaches measured on the suite

- **Profile before optimising, and measure after every change.** Every step since #50 began with a
  profile or counters, and the bottleneck moved each time: closure (#55, #57), then explanations
  (#63), then unit scans (#68), then the closure step again (#70). A check at every node can cost
  more than it saves (#37). Evidence: progress `20261118T143500Z_d159fd9e`,
  `20261118T210505Z_2b1ee0ab`, `20261119T181050Z_7980a6dd`, `20261119T225953Z_121f1554`.
- **What paid** (solved/101): learning 79 → 84 (#54); theory propagation 84 → 87, all from the
  *false* half (#57); 1UIP with backjumping 87 → 90 (#63); equality elimination 90 → 95 (#66);
  incremental closure with the carried merge log −71 % time (#68); watched literals, per-symbol
  closure scans and an activity decision order 95 → 99 (#70).
- **What did not pay — do not retry without a new idea:**
  - explanations by deletion minimisation (one closure per atom: 84 → 73) or by shortest paths
    over the final partition (circular); rerun the closure with a merge log instead (#54);
  - learning over the input atoms alone on large eq_diamonds (exponentially many conflicts); they
    needed equality elimination (#54, #66);
  - equality elimination on the CNF: Tseitin hides the conjunction; do it on the `SmtProblem` (#66);
  - one scan that sets every unit without watches: half the nodes, no faster (#70);
  - union by size in the closure (#68); a BerkMin decision order without cheap propagation (#63);
    skipping the closure after a propagation step (#57).
- **Compare against `origin/main`, built side by side and run at the same time.** Under load an
  instance near the limit flips (eq_diamond12: 25.2 s, then timeout). In a reused worktree the
  local `main` can be far behind (it was #26 in #68's session); use `git show origin/main:…`.
  Evidence: PRs #34, #37, #42; progress `20261119T181050Z_7980a6dd`.
- **`bench/run.sh` cannot check z3's sat models** (`check_model.py` rejects z3's model format and
  reports them WRONG). Compare z3's answers against `:status` only. Evidence: target comment on
  #28, progress `20261118T120101Z_9e18fa7d`.

## Tests

- **Tests guard correctness; speed needs the suite.** Removing a cut keeps every test green unless
  the test is built for it: free atoms before the conflict and a time limit (#58,
  `core/tests/search.rs`, `learn.rs`). Once backjumping is in place even such tests miss
  speed-only mutants (no true propagation lost dead_dnd001 but no test caught it): measure them on
  the suite. Evidence: PR #40, progress `20261119T082705Z_be983059`, `20261119T195542Z_3f029562`.
- **Two constants of the same symbol are congruent.** A closure that skips the rows of constants
  before they are merged misses conflicts (`wf_problem` allows duplicate constants). This trap
  came up in #35, #51 and #55; `core/tests/cuts.rs` catches it, so keep it green. Evidence:
  progress `20261118T155657Z_bac6a2c4`, `20261118T210505Z_2b1ee0ab`, `20261119T053304Z_2f579a37`.

## Tooling

- **`coordination <cmd> --help` runs the command.** It created issues #48 and #64 titled `--help`,
  and `create-pr --help` pushed a branch. Read the `agent-worker-flow` skill instead. Evidence:
  progress `20261119T131724Z_8c149aa4`, `20261119T181050Z_7980a6dd`.
- **Shell waits:** `pgrep -f NAME` inside an `until` loop matches the loop's own command line and
  never ends; wait for a file or an output marker. Functions run through `xargs bash -c` see only
  exported variables. Evidence: progress `20261118T210505Z_2b1ee0ab`.
