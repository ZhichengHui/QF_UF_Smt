//! The solver binary: the shared SMT-LIB front end (`frontend/`, not verified) with this
//! solver's `check_sat` (`core/`, verified). Usage: `qfuf FILE.smt2`, or the script on standard
//! input.

smtlib::bridge!(qfuf);

fn solve(p: &smtlib::SmtProblem) -> smtlib::SmtAnswer {
    answer_from_core(qfuf::check_sat(&problem_to_core(p)))
}

fn main() {
    smtlib::cli_main(solve)
}
