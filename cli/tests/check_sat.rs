//! End-to-end tests: SMT-LIB scripts through the shared front end and this solver's `check_sat`.
//! Every `sat` answer's model is checked with the front end's reference evaluator
//! (`smtlib::semantics::check_model`), and every answer is compared with the expected one.

use smtlib::{SmtAnswer, SmtProblem};

smtlib::bridge!(qfuf);

/// Runs `src` and returns the answers of its `check-sat` commands ("sat", "unsat", "unknown").
fn answers(src: &str) -> Vec<&'static str> {
    let mut got = Vec::new();
    let mut solve = |p: &SmtProblem| -> SmtAnswer {
        let a = answer_from_core(qfuf::check_sat(&problem_to_core(p)));
        match &a {
            SmtAnswer::Sat(m) => {
                assert_eq!(smtlib::semantics::check_model(p, m), Ok(true), "bad model for {src}");
                got.push("sat");
            }
            SmtAnswer::Unsat => got.push("unsat"),
            SmtAnswer::Unknown => got.push("unknown"),
        }
        a
    };
    let mut out = Vec::new();
    smtlib::script::run(src.as_bytes(), &mut solve, &mut out).unwrap();
    got
}

#[test]
fn congruence() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)
             (assert (= (f a) a))(assert (not (= (f (f a)) a)))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn three_distinct_elements() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-const a U)(declare-const b U)
             (declare-const c U)(assert (distinct a b c))(check-sat)";
    assert_eq!(answers(s), ["sat"]);
}

#[test]
fn boolean_function_congruence() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-fun p (U) Bool)(declare-const a U)
             (declare-const b U)(assert (p a))(assert (not (p b)))(assert (= a b))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn define_fun_with_parameters() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)
             (declare-const b U)(define-fun g ((y U)) U (f (f y)))
             (assert (= (g a) b))(assert (distinct a b))(check-sat)";
    assert_eq!(answers(s), ["sat"]);
}

#[test]
fn let_binding() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)
             (declare-const b U)(assert (let ((z (f a))) (and (= z b) (not (= (f a) b)))))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}

#[test]
fn ite_on_an_uninterpreted_sort() {
    let s = "(set-logic QF_UF)(declare-sort U 0)(declare-const p Bool)(declare-const a U)
             (declare-const b U)(declare-const c U)(assert (= (ite p a b) c))
             (assert (distinct a c))(assert (distinct b c))(check-sat)";
    assert_eq!(answers(s), ["unsat"]);
}
