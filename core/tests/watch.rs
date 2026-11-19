//! Regression test for unit propagation with watched literals (#67): a chain of implications
//! behind many clauses that never become unit. Propagating one atom per search node and finding
//! each unit clause by a scan from the first clause (main before #67) costs a scan of every
//! clause per atom of the chain; the watch lists visit only the clauses of the literals made
//! false.

use qfuf::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn term(fun: usize, args: &[usize]) -> Term {
    Term { fun, args: args.to_vec() }
}

fn clause(lits: &[(usize, bool)]) -> Clause {
    Clause { lits: lits.iter().map(|&(a, p)| Lit { atom: a, pos: p }).collect() }
}

/// Atoms `a_i` (`p_i = true`, `i <= n`); first `m` clauses `a_j or not a_j`, which are never unit,
/// then `a_0`, `a_i -> a_{i+1}` for `i < n`, and `not a_n`: unsat by unit propagation alone.
fn chain(n: usize, m: usize) -> Problem {
    let mut terms = vec![term(0, &[])];
    let mut atoms = Vec::new();
    for i in 0..=n {
        terms.push(term(i + 1, &[]));
        atoms.push(Atom { lhs: i + 1, rhs: 0 });
    }
    let mut clauses = Vec::new();
    for j in 0..m {
        clauses.push(clause(&[(j % (n + 1), true), (j % (n + 1), false)]));
    }
    clauses.push(clause(&[(0, true)]));
    for i in 0..n {
        clauses.push(clause(&[(i, false), (i + 1, true)]));
    }
    clauses.push(clause(&[(n, false)]));
    Problem { terms, atoms, clauses }
}

/// The time limit of the test.
const LIMIT: Duration = Duration::from_secs(10);

/// A chain of 4000 atoms behind 400,000 clauses. With the watch lists `solve` takes well under a
/// second; with one scan from the first clause per propagated atom, about 2 * 4000 scans of
/// 400,000 clauses.
#[test]
fn long_chain() {
    let p = chain(4000, 400_000);
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let _ = tx.send(matches!(solve(&p), Answer::Unsat));
        })
        .unwrap();
    let unsat = rx.recv_timeout(LIMIT).unwrap_or_else(|_| panic!("no answer within {:?}", LIMIT));
    assert!(unsat, "the chain should be unsat");
}
