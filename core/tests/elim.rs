//! Regression tests for the equality elimination of `check_sat` (#60): diamond chains in the style
//! of the eq_diamond family, where every `y_i` and `z_i` is eliminated, and problems where a
//! constant must not be eliminated. Every Sat model is checked by an evaluator of the general
//! problem, so a model that leaves an eliminated constant without the value of its partner fails.

use qfuf::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn konst(f: usize) -> SmtTerm {
    SmtTerm::Fun(f, Vec::new())
}

fn eq(a: SmtTerm, b: SmtTerm) -> SmtTerm {
    SmtTerm::App(SmtOp::Eq, vec![a, b])
}

fn and(ts: Vec<SmtTerm>) -> SmtTerm {
    SmtTerm::App(SmtOp::And, ts)
}

fn or(ts: Vec<SmtTerm>) -> SmtTerm {
    SmtTerm::App(SmtOp::Or, ts)
}

fn not(t: SmtTerm) -> SmtTerm {
    SmtTerm::App(SmtOp::Not, vec![t])
}

/// A problem over one uninterpreted sort with `n` constants and the assertions `asserts`.
fn problem(n: usize, asserts: Vec<SmtTerm>) -> SmtProblem {
    let funs = (0..n).map(|_| SmtFun { args: Vec::new(), ret: SmtSort::Uninterpreted(0) }).collect();
    SmtProblem { num_sorts: 1, funs, defs: Vec::new(), asserts }
}

#[derive(PartialEq, Debug)]
enum V {
    B(bool),
    E(usize),
}

fn val(v: &SmtValue) -> V {
    match v {
        SmtValue::Bool(b) => V::B(*b),
        SmtValue::Elem(e) => V::E(*e),
        SmtValue::Bv(_) => panic!("no bit-vectors here"),
    }
}

fn eval(m: &SmtModel, t: &SmtTerm) -> V {
    match t {
        SmtTerm::Fun(f, args) => {
            assert!(args.is_empty(), "only constants here");
            let i = &m.funs[*f];
            match i.entries.iter().find(|e| e.args.is_empty()) {
                Some(e) => val(&e.val),
                None => val(&i.default),
            }
        }
        SmtTerm::App(SmtOp::Eq, args) => V::B(eval(m, &args[0]) == eval(m, &args[1])),
        SmtTerm::App(SmtOp::And, args) => V::B(args.iter().all(|a| eval(m, a) == V::B(true))),
        SmtTerm::App(SmtOp::Or, args) => V::B(args.iter().any(|a| eval(m, a) == V::B(true))),
        SmtTerm::App(SmtOp::Not, args) => V::B(eval(m, &args[0]) == V::B(false)),
        _ => panic!("unexpected term"),
    }
}

/// `check_sat` on `p` within 20 s; `Some(model)` for Sat (checked against every assertion),
/// `None` for Unsat.
fn solve(p: SmtProblem) -> Option<SmtModel> {
    let (tx, rx) = mpsc::channel();
    let asserts = p.asserts.clone();
    thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let _ = tx.send(check_sat(&p));
        })
        .unwrap();
    match rx.recv_timeout(Duration::from_secs(20)).expect("check_sat within 20 s") {
        SmtAnswer::Sat(m) => {
            for (k, a) in asserts.iter().enumerate() {
                assert_eq!(eval(&m, a), V::B(true), "assertion {} false in the model", k);
            }
            Some(m)
        }
        SmtAnswer::Unsat => None,
        SmtAnswer::Unknown => panic!("Unknown"),
    }
}

/// The diamond chain `(x_i = y_i and y_i = x_{i+1}) or (x_i = z_i and z_i = x_{i+1})` for
/// `i < n`, with `x_i` = constant `3 i`, `y_i` = `3 i + 1`, `z_i` = `3 i + 2` and `x_n` = `3 n`.
fn diamond(n: usize) -> Vec<SmtTerm> {
    (0..n)
        .map(|i| {
            let (x, y, z, x1) = (3 * i, 3 * i + 1, 3 * i + 2, 3 * i + 3);
            or(vec![
                and(vec![eq(konst(x), konst(y)), eq(konst(y), konst(x1))]),
                and(vec![eq(konst(x), konst(z)), eq(konst(z), konst(x1))]),
            ])
        })
        .collect()
}

#[test]
fn diamond_unsat() {
    // eq_diamond20: x_0 != x_n with a chain that forces x_0 = x_n.
    for n in [1, 5, 20, 40] {
        let mut a = diamond(n);
        a.push(not(eq(konst(0), konst(3 * n))));
        assert!(solve(problem(3 * n + 1, a)).is_none(), "diamond {} is unsat", n);
    }
}

#[test]
fn diamond_sat_model() {
    // A sat chain: x_0 differs from an extra constant w, so x_0 and the y_i, z_i that the
    // elimination removes cannot all have the default value of the model.
    for n in [1, 3, 10] {
        let w = 3 * n + 1;
        let mut a = diamond(n);
        a.push(not(eq(konst(0), konst(w))));
        a.push(not(eq(konst(3 * n), konst(w))));
        let m = solve(problem(3 * n + 2, a)).expect("sat");
        // Each eliminated constant has the value of its partner.
        for i in 0..n {
            assert_eq!(eval(&m, &konst(3 * i + 1)), eval(&m, &konst(3 * i)));
            assert_eq!(eval(&m, &konst(3 * i + 2)), eval(&m, &konst(3 * i)));
        }
    }
}

#[test]
fn negative_conjunction_kept() {
    // c = 0, a = 1, b = 2: not (c = a and c = b), and a = b. Sat with c != a; eliminating c in
    // the negated conjunction would make it unsat.
    let a = vec![
        not(and(vec![eq(konst(0), konst(1)), eq(konst(0), konst(2))])),
        eq(konst(1), konst(2)),
    ];
    solve(problem(3, a)).expect("sat");
}

#[test]
fn two_conjunctions_kept() {
    // c = 0 occurs in two conjunctions of a disjunction: (c = a and c = b) or (c = d and c = e),
    // with a != b; only the second can hold, and c must take the value of d.
    let a = vec![
        or(vec![
            and(vec![eq(konst(0), konst(1)), eq(konst(0), konst(2))]),
            and(vec![eq(konst(0), konst(3)), eq(konst(0), konst(4))]),
        ]),
        not(eq(konst(1), konst(2))),
        not(eq(konst(0), konst(1))),
    ];
    solve(problem(5, a)).expect("sat");
}

#[test]
fn eliminated_in_two_assertions() {
    // c = 0 is eliminated into g = 1 (its conjunction then has g = g, so g stays); g also occurs in
    // another conjunction. The model must give c the value of g.
    let a = vec![
        and(vec![eq(konst(0), konst(1)), eq(konst(0), konst(3))]),
        and(vec![eq(konst(1), konst(2)), eq(konst(1), konst(4))]),
        not(eq(konst(3), konst(5))),
    ];
    let m = solve(problem(6, a)).expect("sat");
    assert_eq!(eval(&m, &konst(0)), eval(&m, &konst(1)));
}
