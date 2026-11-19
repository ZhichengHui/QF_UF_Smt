//! Regression test for the incremental closure (#65): the search carries the closed partition
//! down its recursion and rescans only the terms an argument of which changed its class. Many
//! terms that no atom touches make a closure from scratch at every node expensive, but cost the
//! incremental closure nothing. The helpers are copied from `cuts.rs`.

use qfuf::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn term(fun: usize, args: &[usize]) -> Term {
    Term { fun, args: args.to_vec() }
}

fn lit(atom: usize, pos: bool) -> Lit {
    Lit { atom, pos }
}

fn atom(lhs: usize, rhs: usize) -> Atom {
    Atom { lhs, rhs }
}

fn clause(lits: &[(usize, bool)]) -> Clause {
    Clause { lits: lits.iter().map(|&(a, p)| lit(a, p)).collect() }
}

/// eq_diamond `n`: `x_0 .. x_n`, `y_i`, `z_i`; for each `i < n`,
/// `(x_i = y_i and y_i = x_{i+1}) or (x_i = z_i and z_i = x_{i+1})`, and `x_0 != x_n`.
fn eq_diamond(n: usize) -> Problem {
    let terms: Vec<Term> = (0..3 * n + 1).map(|c| term(c, &[])).collect();
    let x = |i: usize| i;
    let y = |i: usize| n + 1 + i;
    let z = |i: usize| 2 * n + 1 + i;
    let mut atoms = Vec::new();
    let mut clauses = Vec::new();
    for i in 0..n {
        let a = atoms.len();
        atoms.push(atom(x(i), y(i)));
        atoms.push(atom(y(i), x(i + 1)));
        atoms.push(atom(x(i), z(i)));
        atoms.push(atom(z(i), x(i + 1)));
        for &p in &[a, a + 1] {
            for &q in &[a + 2, a + 3] {
                clauses.push(clause(&[(p, true), (q, true)]));
            }
        }
    }
    atoms.push(atom(x(0), x(n)));
    clauses.push(clause(&[(atoms.len() - 1, false)]));
    Problem { terms, atoms, clauses }
}

/// `p` with `2 k` extra terms, `k` fresh constants `c_j` and the terms `g_j(c_j)`, all of fresh
/// symbols and in no atom.
fn with_padding(mut p: Problem, k: usize) -> Problem {
    let f0 = p.terms.len() + 1000;
    for j in 0..k {
        let c = p.terms.len();
        p.terms.push(term(f0 + 2 * j, &[]));
        p.terms.push(term(f0 + 2 * j + 1, &[c]));
    }
    p
}

/// The time limit of the test.
const LIMIT: Duration = Duration::from_secs(10);

/// eq_diamond 10 with 4000 padding terms. With the carried partition `solve` takes about 0.2 s;
/// with a closure from scratch at every node (main before #65, with #63) about 70 s.
#[test]
fn padded_eq_diamond() {
    let p = with_padding(eq_diamond(10), 2000);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(matches!(solve(&p), Answer::Unsat));
    });
    let unsat = rx.recv_timeout(LIMIT).unwrap_or_else(|_| panic!("no answer within {:?}", LIMIT));
    assert!(unsat, "padded eq_diamond 10 should be unsat");
}
