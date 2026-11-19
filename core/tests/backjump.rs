//! Regression tests for conflict analysis and backjumping (#61). Each problem starts with 40 free
//! atoms (atoms over fresh constants, in no clause) that the search decides first, followed by a
//! small core that needs a decision and whose refutation does not depend on the free atoms.
//! Chronological backtracking refutes the core again under each of the 2^40 assignments of the
//! free atoms; with conflict analysis the first conflict learns a clause over the core alone and
//! the search jumps back to level 0. The problems are solved under a time limit, so that losing
//! backjumping fails a test. Every Sat model is checked by an independent evaluator and every
//! answer is compared with z3 when the `z3` binary is on PATH. The helpers up to `B` are copied
//! from `search.rs`.

use qfuf::*;
use std::io::Write;
use std::process::{Command, Stdio};
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

fn smt_term(p: &Problem, i: usize) -> String {
    let t = &p.terms[i];
    if t.args.is_empty() {
        format!("f{}_0", t.fun)
    } else {
        let a: Vec<String> = t.args.iter().map(|&x| smt_term(p, x)).collect();
        format!("(f{}_{} {})", t.fun, t.args.len(), a.join(" "))
    }
}

fn smtlib(p: &Problem) -> String {
    let mut arity = std::collections::BTreeSet::new();
    for t in &p.terms {
        arity.insert((t.fun, t.args.len()));
    }
    let mut s = String::from("(set-logic QF_UF)\n(declare-sort U 0)\n");
    for (f, n) in &arity {
        s += &format!("(declare-fun f{}_{} ({}) U)\n", f, n, "U ".repeat(*n));
    }
    for c in &p.clauses {
        let ls: Vec<String> = c
            .lits
            .iter()
            .map(|l| {
                let a = &p.atoms[l.atom];
                let e = format!("(= {} {})", smt_term(p, a.lhs), smt_term(p, a.rhs));
                if l.pos { e } else { format!("(not {})", e) }
            })
            .collect();
        s += &format!("(assert (or false {}))\n", ls.join(" "));
    }
    s + "(check-sat)\n"
}

fn z3_sat(p: &Problem) -> Option<bool> {
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(smtlib(p).as_bytes()).ok()?;
    let out = String::from_utf8(child.wait_with_output().ok()?.stdout).ok()?;
    match out.trim() {
        "sat" => Some(true),
        "unsat" => Some(false),
        o => panic!("z3: {}", o),
    }
}

/// The time limit for one problem. Every problem here takes milliseconds; without propagation or
/// the closure cut, those with 40 free atoms take about 2^40 leaves.
const LIMIT: Duration = Duration::from_secs(20);

/// Returns whether `solve` answered Sat; panics if it takes longer than `LIMIT`, if a model is
/// wrong, or if z3 disagrees.
fn check(p: Problem) -> bool {
    let text = smtlib(&p);
    let z = z3_sat(&p);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let r = match solve(&p) {
            Answer::Sat(m) => Some(eval(&m, &p)),
            Answer::Unsat => None,
        };
        let _ = tx.send(r);
    });
    let r = rx.recv_timeout(LIMIT).unwrap_or_else(|_| panic!("no answer within {:?} for\n{}", LIMIT, text));
    let sat = match r {
        Some(ok) => {
            assert!(ok, "wrong model for\n{}", text);
            true
        }
        None => false,
    };
    if let Some(z) = z {
        assert_eq!(sat, z, "z3 disagrees on\n{}", text);
    }
    sat
}

/// Builds a problem: every constant gets its own function symbol.
struct B(Problem);

impl B {
    fn new() -> B {
        B(Problem { terms: Vec::new(), atoms: Vec::new(), clauses: Vec::new() })
    }

    fn konst(&mut self) -> usize {
        let k = self.0.terms.len();
        self.0.terms.push(term(1000 + k, &[]));
        k
    }

    fn eq(&mut self, a: usize, b: usize) -> usize {
        self.0.atoms.push(atom(a, b));
        self.0.atoms.len() - 1
    }

    /// A new atom between two new constants.
    fn fresh(&mut self) -> usize {
        let (a, b) = (self.konst(), self.konst());
        self.eq(a, b)
    }

    /// `n` new atoms that occur in no clause: the search branches on them unless the branch ends.
    fn free(&mut self, n: usize) {
        for _ in 0..n {
            self.fresh();
        }
    }

    fn cl(&mut self, lits: &[(usize, bool)]) {
        self.0.clauses.push(clause(lits));
    }
}

/// The four clauses over `x`, `y`: unsatisfiable, and no clause is unit before a decision.
fn prop_core(b: &mut B) {
    let x = b.fresh();
    let y = b.fresh();
    b.cl(&[(x, true), (y, true)]);
    b.cl(&[(x, true), (y, false)]);
    b.cl(&[(x, false), (y, true)]);
    b.cl(&[(x, false), (y, false)]);
}

#[test]
fn propositional_conflict_below_free_decisions() {
    let mut b = B::new();
    b.free(40);
    prop_core(&mut b);
    assert!(!check(b.0));
}

#[test]
fn satisfiable_after_backjump() {
    // Three of the four clauses: deciding `x` true conflicts, the learned clause `not x` jumps back
    // to level 0, and `x` false, `y` true is a model.
    let mut b = B::new();
    b.free(40);
    let x = b.fresh();
    let y = b.fresh();
    b.cl(&[(x, true), (y, true)]);
    b.cl(&[(x, false), (y, true)]);
    b.cl(&[(x, false), (y, false)]);
    assert!(check(b.0));
}

#[test]
fn theory_conflict_below_free_decisions() {
    // `x` and `not x` each force `a = b`, `b = c` and `a != c`: a closure conflict under both
    // values of the decision `x`.
    let mut b = B::new();
    b.free(40);
    let (a, bb, c) = (b.konst(), b.konst(), b.konst());
    let p = b.eq(a, bb);
    let q = b.eq(bb, c);
    let r = b.eq(a, c);
    let x = b.fresh();
    for s in [true, false] {
        b.cl(&[(x, s), (p, true)]);
        b.cl(&[(x, s), (q, true)]);
        b.cl(&[(x, s), (r, false)]);
    }
    assert!(!check(b.0));
}

#[test]
fn conflict_two_levels_below() {
    // The core decides `x` and `y` after the free atoms and before 20 more free atoms; the conflict
    // under `z` (decided last) involves `x` only, so the search jumps over the later decisions.
    let mut b = B::new();
    b.free(20);
    let x = b.fresh();
    b.free(20);
    let z = b.fresh();
    let w = b.fresh();
    b.cl(&[(x, false), (z, true), (w, true)]);
    b.cl(&[(x, false), (z, true), (w, false)]);
    b.cl(&[(x, false), (z, false), (w, true)]);
    b.cl(&[(x, false), (z, false), (w, false)]);
    // `x` is false in every model; the rest is free.
    assert!(check(b.0));
}
