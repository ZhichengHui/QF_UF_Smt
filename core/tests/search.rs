//! Regression tests for the search on a partial assignment (#38): unit propagation chains, a
//! clause that becomes unit only after propagation, clauses with duplicate or complementary
//! literals, and a congruence-closure conflict found only at an inner decision node. Every Sat
//! model is checked by an independent evaluator and every answer is compared with z3 when the `z3`
//! binary is on PATH. The helpers up to `z3_sat` are copied from `cuts.rs`.
//!
//! Most problems also have 40 free atoms (atoms over fresh constants) that the search would branch
//! on if propagation or the closure cut did not end the branch first. Those problems are solved
//! under a time limit, so that losing propagation or the cut fails a test instead of only slowing
//! the solver down.

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

    fn app(&mut self, f: usize, args: &[usize]) -> usize {
        self.0.terms.push(term(f, args));
        self.0.terms.len() - 1
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

/// `e_0`, `e_0 -> e_1`, ..., `e_{n-1} -> e_n` (and `not e_n` if `unsat`), after 40 free atoms.
/// The implications come first, so that each is unit only after the previous propagation.
fn propagation_chain(n: usize, unsat: bool) -> Problem {
    let mut b = B::new();
    b.free(40);
    let e: Vec<usize> = (0..=n).map(|_| b.fresh()).collect();
    for i in 0..n {
        b.cl(&[(e[i], false), (e[i + 1], true)]);
    }
    b.cl(&[(e[0], true)]);
    if unsat {
        b.cl(&[(e[n], false)]);
    }
    b.0
}

#[test]
fn unit_propagation_chain() {
    assert!(!check(propagation_chain(20, true)));
    // The model must make every e_i true.
    assert!(check(propagation_chain(20, false)));
    // The chain in the other direction: `not e_n` propagates back to `not e_0`.
    let mut b = B::new();
    b.free(40);
    let e: Vec<usize> = (0..=20).map(|_| b.fresh()).collect();
    for i in 0..20 {
        b.cl(&[(e[i], false), (e[i + 1], true)]);
    }
    b.cl(&[(e[20], false)]);
    b.cl(&[(e[0], true), (e[5], true)]);
    assert!(!check(b.0));
}

/// `x or y or z` comes first and becomes unit only after `not x` and `not y` have propagated;
/// `z` is `a = b`, which contradicts `f(a) != f(b)` (if `conflict`) by congruence.
fn unit_after_propagation(conflict: bool) -> Problem {
    let mut b = B::new();
    b.free(40);
    let (x, y) = (b.fresh(), b.fresh());
    let (ta, tb) = (b.konst(), b.konst());
    let (fa, fb) = (b.app(7, &[ta]), b.app(7, &[tb]));
    let z = b.eq(ta, tb);
    let w = b.eq(fa, fb);
    b.cl(&[(x, true), (y, true), (z, true)]);
    b.cl(&[(x, false)]);
    b.cl(&[(y, false)]);
    if conflict {
        b.cl(&[(w, false)]);
    }
    b.0
}

#[test]
fn clause_unit_only_after_propagation() {
    assert!(!check(unit_after_propagation(true)));
    // The model must make a = b.
    assert!(check(unit_after_propagation(false)));
}

#[test]
fn two_unset_literals_are_not_unit() {
    // `a or b` first, and `a` leads to a conflict: only `b` gives a model. A clause with two
    // unset literals treated as unit for its first one would answer Unsat.
    let mut b = B::new();
    let (a, bb, c, d) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    b.cl(&[(a, true), (bb, true)]);
    b.cl(&[(a, false), (c, true)]);
    b.cl(&[(c, false), (d, true)]);
    b.cl(&[(d, false)]);
    assert!(check(b.0));
    // The same with the literal order reversed and a true literal next to an unset one: `b` is
    // true, so `b or a` must not force `a`.
    let mut b = B::new();
    let (a, bb, c) = (b.fresh(), b.fresh(), b.fresh());
    b.cl(&[(bb, true)]);
    b.cl(&[(bb, true), (a, true)]);
    b.cl(&[(a, false), (c, true)]);
    b.cl(&[(c, false)]);
    assert!(check(b.0));
}

#[test]
fn duplicate_and_complementary_literals() {
    let one = |clauses: &[&[(usize, bool)]]| {
        let mut b = B::new();
        let (a, c) = (b.fresh(), b.fresh());
        assert_eq!((a, c), (0, 1));
        for &l in clauses {
            b.cl(l);
        }
        check(b.0)
    };
    // `a or a`: a must be true.
    assert!(one(&[&[(0, true), (0, true)]]));
    assert!(!one(&[&[(0, true), (0, true)], &[(0, false)]]));
    assert!(!one(&[&[(0, false)], &[(0, true), (0, true)]]));
    // `a or not a` is a tautology, whatever else holds.
    assert!(one(&[&[(0, true), (0, false)], &[(0, false)]]));
    assert!(one(&[&[(0, false)], &[(0, true), (0, false)], &[(0, true), (1, true)]]));
    // A repeated literal next to a false one: `a or not c or a` with `c` forces `a`.
    assert!(one(&[&[(0, true), (1, false), (0, true)], &[(1, true)]]));
    assert!(!one(&[&[(0, true), (1, false), (0, true)], &[(1, true)], &[(0, false)]]));
    // Complementary literals next to a false one: `a or not a or c` with `not c`.
    assert!(one(&[&[(0, true), (0, false), (1, true)], &[(1, false)]]));
    // The empty clause.
    assert!(!one(&[&[]]));
    assert!(!one(&[&[(0, true), (0, false)], &[]]));
}

/// 3 free atoms, then `x = y`, `f(x) = f(y)`, `p = q`, then 40 free atoms; `f(x) != f(y)`, and
/// `x = y or p = q` (and `x = y or p != q` if `unsat`). Nothing propagates at the root except
/// `f(x) != f(y)`; the search decides 3 free atoms, then `x = y`, and only the closure cut ends that
/// branch before the 40 free atoms.
fn inner_closure_conflict(unsat: bool) -> Problem {
    let mut b = B::new();
    b.free(3);
    let (x, y) = (b.konst(), b.konst());
    let (fx, fy) = (b.app(7, &[x]), b.app(7, &[y]));
    let exy = b.eq(x, y);
    let efxy = b.eq(fx, fy);
    let epq = b.fresh();
    b.free(40);
    b.cl(&[(efxy, false)]);
    b.cl(&[(exy, true), (epq, true)]);
    if unsat {
        b.cl(&[(exy, true), (epq, false)]);
    }
    b.0
}

#[test]
fn closure_conflict_at_inner_decision() {
    assert!(!check(inner_closure_conflict(true)));
    // The model must make x != y and p = q.
    assert!(check(inner_closure_conflict(false)));
    // A conflict through a propagated and a decided atom: `x = y` (propagated from `not p`) and
    // `y = z` (decided true after a free atom) against `f(x) != f(z)`, with 40 free atoms after
    // them. The model must make y != z.
    let mut b = B::new();
    b.free(1);
    let (x, y, z) = (b.konst(), b.konst(), b.konst());
    let (fx, fz) = (b.app(7, &[x]), b.app(7, &[z]));
    let exy = b.eq(x, y);
    let eyz = b.eq(y, z);
    let efxz = b.eq(fx, fz);
    let (p, q) = (b.fresh(), b.fresh());
    b.free(40);
    b.cl(&[(efxz, false)]);
    b.cl(&[(exy, true), (p, true)]);
    b.cl(&[(eyz, true), (q, true)]);
    b.cl(&[(p, false)]);
    assert!(check(b.0));
}
