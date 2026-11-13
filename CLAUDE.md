# Rules for this repository

- `spec/` is the specification: the meaning of the top-level theorem `check_sat_correct` depends on
  nothing else. It is fixed across changes of the solver and its proofs. Do not edit any file in
  `spec/` unless the user explicitly asks for that change; if a task seems to need one, stop and
  ask.
- This includes the input range `smt_in_range` in `spec/QFUF_Spec.thy`: a change of the solver must
  keep answering (`Sat` or `Unsat`) every problem of the fragment and of the range. Make the solver
  fit the range, never the range fit the solver.
- One part of `spec/` follows the generated code: the locale `QFUF_heap` in `spec/QFUF_Spec.thy` is
  `QFUF_ctx` of `urust/QFUF_Locale.thy` without its last line (the fuel). When regenerating
  `urust/` changes that locale, update `QFUF_heap` to match it exactly and tell the user.
- `spec/SMT_Types.thy` and `spec/SMT_Semantics.thy` are the same in the QF_UF_Smt and QF_BV_Smt
  repositories (`SMT_Types.thy` up to its `imports` line).
- Check all proofs with `tools/check.sh` before committing.
