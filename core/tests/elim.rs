//! Regression tests for the elimination of constants (#60): `check_sat` on problems in which
//! constants occur only in `and`s at positive positions that equate them with other constants.
//! Every Sat model is checked by an independent evaluator of the general problem, and the answers
//! of random problems over constants are compared with a brute-force search.

use qfuf::*;

const U: usize = 0;

fn c(f: usize) -> SmtTerm {
    SmtTerm::Fun(f, Vec::new())
}

fn app(o: SmtOp, args: Vec<SmtTerm>) -> SmtTerm {
    SmtTerm::App(o, args)
}

fn eq(a: SmtTerm, b: SmtTerm) -> SmtTerm {
    app(SmtOp::Eq, vec![a, b])
}

fn and(args: Vec<SmtTerm>) -> SmtTerm {
    app(SmtOp::And, args)
}

fn or(args: Vec<SmtTerm>) -> SmtTerm {
    app(SmtOp::Or, args)
}

fn not(a: SmtTerm) -> SmtTerm {
    app(SmtOp::Not, vec![a])
}

/// A problem with `n` constants of the uninterpreted sort, then the symbols `extra`.
fn problem(n: usize, extra: Vec<SmtFun>, asserts: Vec<SmtTerm>) -> SmtProblem {
    let mut funs: Vec<SmtFun> = (0..n).map(|_| SmtFun { args: Vec::new(), ret: SmtSort::Uninterpreted(U) }).collect();
    funs.extend(extra);
    SmtProblem { num_sorts: 1, funs, defs: Vec::new(), asserts }
}

#[derive(Clone, PartialEq, Debug)]
enum V {
    B(bool),
    E(usize),
}

fn val(v: &SmtValue) -> V {
    match v {
        SmtValue::Bool(b) => V::B(*b),
        SmtValue::Elem(e) => V::E(*e),
        SmtValue::Bv(_) => panic!("bit-vector value"),
    }
}

fn apply(m: &SmtModel, f: usize, args: &[V]) -> V {
    let i = &m.funs[f];
    for e in &i.entries {
        if e.args.iter().map(val).collect::<Vec<_>>() == args {
            return val(&e.val);
        }
    }
    val(&i.default)
}

fn eval(m: &SmtModel, t: &SmtTerm) -> V {
    match t {
        SmtTerm::BoolConst(b) => V::B(*b),
        SmtTerm::Fun(f, args) => {
            let vs: Vec<V> = args.iter().map(|a| eval(m, a)).collect();
            apply(m, *f, &vs)
        }
        SmtTerm::App(o, args) => {
            let vs: Vec<V> = args.iter().map(|a| eval(m, a)).collect();
            let b = |v: &V| *v == V::B(true);
            match o {
                SmtOp::Not => V::B(!b(&vs[0])),
                SmtOp::And => V::B(vs.iter().all(b)),
                SmtOp::Or => V::B(vs.iter().any(b)),
                SmtOp::Eq => V::B(vs.windows(2).all(|w| w[0] == w[1])),
                _ => panic!("operator not evaluated"),
            }
        }
        _ => panic!("term not evaluated"),
    }
}

/// The answer of `check_sat`: `Some(true)` for Sat with a checked model, `Some(false)` for Unsat.
fn solve_checked(p: &SmtProblem) -> bool {
    match check_sat(p) {
        SmtAnswer::Sat(m) => {
            assert_eq!(m.funs.len(), p.funs.len());
            for f in 0..p.funs.len() {
                if p.funs[f].args.is_empty() {
                    if let V::E(e) = apply(&m, f, &[]) {
                        assert!(e < m.domains[U], "value out of the domain");
                    }
                }
            }
            for a in &p.asserts {
                assert_eq!(eval(&m, a), V::B(true), "the model falsifies an assertion");
            }
            true
        }
        SmtAnswer::Unsat => false,
        SmtAnswer::Unknown => panic!("Unknown"),
    }
}

/// The diamond chain of eq_diamond over the constants `x_i` (3i), `y_i` (3i+1), `z_i` (3i+2),
/// `i <= n`, with `x_0 = x_n` asserted equal (`last` true) or different.
fn diamond(n: usize, last: bool) -> SmtProblem {
    let x = |i: usize| c(3 * i);
    let y = |i: usize| c(3 * i + 1);
    let z = |i: usize| c(3 * i + 2);
    let mut asserts = Vec::new();
    for i in 0..n {
        asserts.push(or(vec![and(vec![eq(x(i), y(i)), eq(y(i), x(i + 1))]), and(vec![eq(x(i), z(i)), eq(z(i), x(i + 1))])]));
    }
    let e = eq(x(0), x(n));
    asserts.push(if last { e } else { not(e) });
    problem(3 * n + 3, Vec::new(), asserts)
}

#[test]
fn diamond_unsat() {
    // Exponential for the search without the elimination (eq_diamond13 timed out at 30 s).
    for n in [1, 5, 40] {
        assert!(!solve_checked(&diamond(n, false)), "diamond {n}");
    }
}

#[test]
fn diamond_sat() {
    // Every y_i and z_i is eliminated; the model gives them the values of their partners.
    for n in [1, 5, 40] {
        assert!(solve_checked(&diamond(n, true)), "diamond {n}");
    }
}

#[test]
fn guard_under_not() {
    // The `and` is not at a positive position: c (0) must stay apart from a (1) = b (2).
    let p = problem(3, Vec::new(), vec![not(and(vec![eq(c(0), c(1)), eq(c(0), c(2))])), eq(c(1), c(2))]);
    assert!(solve_checked(&p));
    // Also unsat when c is forced equal to a elsewhere.
    let p = problem(3, Vec::new(), vec![not(and(vec![eq(c(0), c(1)), eq(c(0), c(2))])), eq(c(1), c(2)), eq(c(0), c(1))]);
    assert!(!solve_checked(&p));
    // c also has a guard at a positive position, but the `and` under `not` keeps it.
    let p = problem(3, Vec::new(), vec![
        not(and(vec![eq(c(0), c(1)), eq(c(0), c(2))])),
        eq(c(1), c(2)),
        or(vec![and(vec![eq(c(0), c(1)), eq(c(1), c(1))]), eq(c(1), c(2))]),
    ]);
    assert!(solve_checked(&p));
}

#[test]
fn unguarded_occurrence() {
    // c (0) also occurs outside the `and`: it is not eliminated, and the answers stay right.
    let p = problem(4, Vec::new(), vec![or(vec![and(vec![eq(c(0), c(1)), eq(c(0), c(2))]), eq(c(0), c(3))]), not(eq(c(1), c(2))), not(eq(c(0), c(3)))]);
    assert!(!solve_checked(&p));
    let p = problem(4, Vec::new(), vec![or(vec![and(vec![eq(c(0), c(1)), eq(c(0), c(2))]), eq(c(0), c(3))]), not(eq(c(1), c(3)))]);
    assert!(solve_checked(&p));
}

#[test]
fn inside_guard() {
    // c (0) is an argument of f (symbol 3) inside its `and`: the `and` holds only with c = a (1).
    let f = SmtFun { args: vec![SmtSort::Uninterpreted(U)], ret: SmtSort::Uninterpreted(U) };
    let fc = SmtTerm::Fun(3, vec![c(0)]);
    let fa = SmtTerm::Fun(3, vec![c(1)]);
    let p = problem(3, vec![f], vec![and(vec![eq(c(0), c(1)), eq(fc, c(2))]), not(eq(fa, c(2)))]);
    assert!(!solve_checked(&p));
    let f = SmtFun { args: vec![SmtSort::Uninterpreted(U)], ret: SmtSort::Uninterpreted(U) };
    let fc = SmtTerm::Fun(3, vec![c(0)]);
    let fa = SmtTerm::Fun(3, vec![c(1)]);
    let p = problem(3, vec![f], vec![or(vec![and(vec![eq(c(0), c(1)), eq(fc, c(2))]), eq(c(1), c(2))]), eq(fa, c(1))]);
    assert!(solve_checked(&p));
}

/// A small deterministic generator (xorshift).
struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// A random formula over `k` constants, mostly `and`/`or` of equalities so that constants get
/// eliminated, with some negations.
fn formula(r: &mut Rng, k: usize, depth: usize) -> SmtTerm {
    let pick = if depth == 0 { 0 } else { r.next(6) };
    match pick {
        0 | 1 => eq(c(r.next(k)), c(r.next(k))),
        2 => not(formula(r, k, depth - 1)),
        3 | 4 => {
            let n = 1 + r.next(3);
            and((0..n).map(|_| formula(r, k, depth - 1)).collect())
        }
        _ => {
            let n = 1 + r.next(3);
            or((0..n).map(|_| formula(r, k, depth - 1)).collect())
        }
    }
}

fn holds(vals: &[usize], t: &SmtTerm) -> bool {
    match t {
        SmtTerm::Fun(f, _) => panic!("constant {f} as a formula"),
        SmtTerm::App(o, args) => match o {
            SmtOp::Not => !holds(vals, &args[0]),
            SmtOp::And => args.iter().all(|a| holds(vals, a)),
            SmtOp::Or => args.iter().any(|a| holds(vals, a)),
            SmtOp::Eq => match (&args[0], &args[1]) {
                (SmtTerm::Fun(a, _), SmtTerm::Fun(b, _)) => vals[*a] == vals[*b],
                _ => panic!("equality of non-constants"),
            },
            _ => panic!("operator"),
        },
        _ => panic!("term"),
    }
}

/// Is there an assignment of values `0..k` to the `k` constants that makes every assertion true?
fn brute(k: usize, asserts: &[SmtTerm]) -> bool {
    let mut vals = vec![0; k];
    loop {
        if asserts.iter().all(|a| holds(&vals, a)) {
            return true;
        }
        let mut i = 0;
        while i < k && vals[i] == k - 1 {
            vals[i] = 0;
            i += 1;
        }
        if i == k {
            return false;
        }
        vals[i] += 1;
    }
}

#[test]
fn random_constants() {
    let mut r = Rng(0x9e3779b97f4a7c15);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..600 {
        let k = 2 + r.next(4);
        let n = 1 + r.next(3);
        let asserts: Vec<SmtTerm> = (0..n).map(|_| formula(&mut r, k, 3)).collect();
        let expected = brute(k, &asserts);
        let p = problem(k, Vec::new(), asserts);
        assert_eq!(solve_checked(&p), expected);
        if expected { sat += 1 } else { unsat += 1 }
    }
    assert!(sat > 50 && unsat > 50, "sat {sat}, unsat {unsat}");
}
