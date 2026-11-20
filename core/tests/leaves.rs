//! Regression tests for the incremental closure (#65, #73) and the watch lists (#67), from the
//! review #77. A conflict that the closure or the unit propagation misses after a decision is
//! found only at the leaves, by `prop_holds` or `theory_check`, which refute the leaf without
//! learning a clause. The search then enumerates the free atoms decided after the conflict, 2^40
//! leaves here, so missing the conflict fails the time limit instead of only slowing the solver
//! down. The first conflict-free assignment is a model, so both problems are sat.

use qfuf::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn term(fun: usize, args: &[usize]) -> Term {
    Term { fun, args: args.to_vec() }
}

fn atom(lhs: usize, rhs: usize) -> Atom {
    Atom { lhs, rhs }
}

fn clause(lits: &[(usize, bool)]) -> Clause {
    Clause { lits: lits.iter().map(|&(a, p)| Lit { atom: a, pos: p }).collect() }
}

fn interp(m: &Model, fun: usize, args: &[usize]) -> usize {
    for e in &m.entries {
        if e.fun == fun && e.args == args {
            return e.val;
        }
    }
    0
}

fn eval(m: &Model, p: &Problem) -> bool {
    let mut vals: Vec<usize> = Vec::new();
    for t in &p.terms {
        let args: Vec<usize> = t.args.iter().map(|&x| vals[x]).collect();
        vals.push(interp(m, t.fun, &args));
    }
    p.clauses.iter().all(|c| {
        c.lits.iter().any(|l| (vals[p.atoms[l.atom].lhs] == vals[p.atoms[l.atom].rhs]) == l.pos)
    })
}

/// `p` with `k` free atoms `c_j = d_j` over fresh constants, after its own atoms and in no clause.
fn with_free(mut p: Problem, k: usize) -> Problem {
    let f0 = p.terms.len() + 1000;
    for j in 0..k {
        let c = p.terms.len();
        p.terms.push(term(f0 + 2 * j, &[]));
        p.terms.push(term(f0 + 2 * j + 1, &[]));
        p.atoms.push(atom(c, c + 1));
    }
    p
}

/// The time limit of each test.
const LIMIT: Duration = Duration::from_secs(10);

fn assert_sat(p: Problem) {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let r = match solve(&p) {
            Answer::Sat(m) => eval(&m, &p),
            Answer::Unsat => false,
        };
        let _ = tx.send(r);
    });
    let ok = rx.recv_timeout(LIMIT).unwrap_or_else(|_| panic!("no answer within {:?}", LIMIT));
    assert!(ok, "expected sat with a model of the clauses");
}

/// Terms `a`, `b`, `f(b)`, `f(a)`; atoms `a = b` (decided first), `f(a) = f(b)`; clause
/// `f(a) != f(b)`. Deciding `a = b` merges the class of `a` into that of `b`, so `f(a)` is the
/// only rescanned term, and the term it is congruent to, `f(b)`, comes first in the list of
/// `buckets` of the class of `b`. A closure round that skips the head of that list misses the
/// conflict.
#[test]
fn congruence_with_bucket_head() {
    let p = Problem {
        terms: vec![term(0, &[]), term(1, &[]), term(2, &[1]), term(2, &[0])],
        atoms: vec![atom(0, 1), atom(3, 2)],
        clauses: vec![clause(&[(1, false)])],
    };
    assert_sat(with_free(p, 40));
}

/// Atoms `p` (decided first) and `q` over fresh constants; clauses `not p or q` and
/// `not p or not q`. Unit propagation from the decision on `p` sets `q` and finds the second
/// clause false; without it, no clause is visited before the leaves.
#[test]
fn unit_after_decision() {
    let p = Problem {
        terms: (0..4).map(|c| term(c, &[])).collect(),
        atoms: vec![atom(0, 1), atom(2, 3)],
        clauses: vec![clause(&[(0, false), (1, true)]), clause(&[(0, false), (1, false)])],
    };
    assert_sat(with_free(p, 40));
}
