//! Regression tests for learning from congruence-closure conflicts (#45). In each problem the
//! same closure conflict arises under every assignment of 40 free atoms that the search decides
//! before the atoms of the conflict; without the learned clauses the search meets it 2^40 times.
//! The wide and late variants (#58) need a long explanation queue or a second closure round; an
//! explanation that misses them falls back to all true atoms and the search runs out of time.
//! Every Sat model is checked by an independent evaluator and every answer is compared with z3
//! when the `z3` binary is on PATH. The helpers up to `B` are copied from `search.rs`.

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

/// The time limit for one problem. Every problem here takes milliseconds; without learning, each
/// takes about 2^40 closure conflicts.
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

/// `f(x) != f(y)` and `z = y`, then 40 free atoms, then `x = y`, `x = z` and `e` (a fresh atom),
/// with the clause `x = y or x = z` (`or e` if `escape`). Both `x = y` and, through `z = y`,
/// `x = z` contradict `f(x) != f(y)` by congruence, only after the 40 free atoms are decided. With
/// `nested`, `f` is applied to `g(x)` and `g(y)` instead, so the explanation of the conflict goes
/// through two congruences.
fn repeated_conflict(escape: bool, nested: bool) -> Problem {
    let mut b = B::new();
    let (x, y, z) = (b.konst(), b.konst(), b.konst());
    let (fx, fy) = if nested {
        let (gx, gy) = (b.app(8, &[x]), b.app(8, &[y]));
        (b.app(7, &[gx]), b.app(7, &[gy]))
    } else {
        (b.app(7, &[x]), b.app(7, &[y]))
    };
    let efxy = b.eq(fx, fy);
    let ezy = b.eq(z, y);
    b.free(40);
    let exy = b.eq(x, y);
    let exz = b.eq(x, z);
    let e = b.fresh();
    b.cl(&[(efxy, false)]);
    b.cl(&[(ezy, true)]);
    if escape {
        b.cl(&[(exy, true), (exz, true), (e, true)]);
    } else {
        b.cl(&[(exy, true), (exz, true)]);
    }
    b.0
}

#[test]
fn learned_conflict_cuts_sibling_branches() {
    assert!(!check(repeated_conflict(false, false)));
    assert!(!check(repeated_conflict(false, true)));
    // The model must make e true.
    assert!(check(repeated_conflict(true, false)));
    assert!(check(repeated_conflict(true, true)));
}

/// `x_0 != x_n` and, for every `i < n`, `x_i = x_{i+1}` or `x_i = y_i`, `y_i = x_{i+1}` (a chain of
/// diamonds with one side split in two). Unsat: every choice joins `x_0` and `x_n`; each conflict
/// is explained by the atoms on one path, and the learned clauses must not exclude a model of a
/// satisfiable variant (`x_0 != x_n` replaced by `x_0 != y_0`). No free atoms here:
/// the learned clauses have one literal per diamond, so they cut sibling branches only together
/// with learning from propositional conflicts, a later step.
#[test]
fn learned_path_explanations() {
    for n in 1..6 {
        let mut b = B::new();
        let xs: Vec<usize> = (0..=n).map(|_| b.konst()).collect();
        let ys: Vec<usize> = (0..n).map(|_| b.konst()).collect();
        let e0n = b.eq(xs[0], xs[n]);
        let e0y = b.eq(xs[0], ys[0]);
        b.cl(&[(e0n, false)]);
        for i in 0..n {
            let d = b.eq(xs[i], xs[i + 1]);
            let l = b.eq(xs[i], ys[i]);
            let r = b.eq(ys[i], xs[i + 1]);
            let s = b.fresh();
            // s -> (l and r), and d or s.
            b.cl(&[(s, false), (l, true)]);
            b.cl(&[(s, false), (r, true)]);
            b.cl(&[(d, true), (s, true)]);
        }
        let mut sat = Problem { terms: Vec::new(), atoms: Vec::new(), clauses: Vec::new() };
        sat.terms = b.0.terms.iter().map(|t| term(t.fun, &t.args)).collect();
        sat.atoms = b.0.atoms.iter().map(|a| atom(a.lhs, a.rhs)).collect();
        sat.clauses = b.0.clauses.iter().map(|c| Clause { lits: c.lits.iter().map(|l| lit(l.atom, l.pos)).collect() }).collect();
        sat.clauses[0] = clause(&[(e0y, false)]);
        assert!(!check(b.0));
        assert!(check(sat));
    }
}

/// `repeated_conflict` with `f` applied to `filler` copies of a constant `w` before its last
/// argument: `f(w, .., w, x) != f(w, .., w, y)`. The explanation queues the argument pairs of
/// `f(w, .., x)` and `f(w, .., y)` in order, so the pair `x, y` comes after `filler` pairs `w, w`.
/// The problem has 88 terms; `explain` follows the first `2 * 88 + 1` queued pairs and, if they do
/// not explain the conflict, falls back to all true atoms, which include the 40 free atoms.
fn wide_conflict(escape: bool, filler: usize) -> Problem {
    let mut b = B::new();
    let (x, y, z, w) = (b.konst(), b.konst(), b.konst(), b.konst());
    let mut ax = vec![w; filler];
    let mut ay = vec![w; filler];
    ax.push(x);
    ay.push(y);
    let (fx, fy) = (b.app(7, &ax), b.app(7, &ay));
    let efxy = b.eq(fx, fy);
    let ezy = b.eq(z, y);
    b.free(40);
    let exy = b.eq(x, y);
    let exz = b.eq(x, z);
    let e = b.fresh();
    b.cl(&[(efxy, false)]);
    b.cl(&[(ezy, true)]);
    if escape {
        b.cl(&[(exy, true), (exz, true), (e, true)]);
    } else {
        b.cl(&[(exy, true), (exz, true)]);
    }
    assert_eq!(b.0.terms.len(), 88);
    b.0
}

/// With 100 filler pairs, the pair `x, y` is queued after the first 88 pairs but within the
/// first 177: the explanation must follow it, or the fallback keeps the free atoms in the learned
/// clauses and the unsat problem takes 2^40 conflicts. With 200 filler pairs it is past the
/// queue, the path explanation misses `x = y`, and only the check by `rows_join` keeps the
/// learned clause valid: without it the clause is `f(..x) = f(..y)`, which makes the
/// satisfiable problem unsat.
#[test]
fn learned_conflict_with_wide_terms() {
    assert!(!check(wide_conflict(false, 100)));
    assert!(check(wide_conflict(true, 100)));
    assert!(check(wide_conflict(true, 200)));
}

/// `f(x) != f(y)` with `x = g(u)`, `y = g(v)` and `z = v`, then 40 free atoms, then `u = v`,
/// `u = z` and `e`, with the clause `u = v or u = z` (`or e` if `escape`). The terms `f(x)` and
/// `f(y)` come before `g(u)` and `g(v)`, so a closure round in term order joins `g(u)` and `g(v)`
/// only after the row of `f(y)`: `f(x)` and `f(y)` join in the second round. The merge log and
/// the closure of `rows_join` both need that round, or the explanation falls back to all true
/// atoms.
fn late_congruence_conflict(escape: bool) -> Problem {
    let mut b = B::new();
    let (x, y) = (b.konst(), b.konst());
    let (fx, fy) = (b.app(7, &[x]), b.app(7, &[y]));
    let (u, v, z) = (b.konst(), b.konst(), b.konst());
    let (gu, gv) = (b.app(8, &[u]), b.app(8, &[v]));
    let efxy = b.eq(fx, fy);
    let ex = b.eq(x, gu);
    let ey = b.eq(y, gv);
    let ezv = b.eq(z, v);
    b.free(40);
    let euv = b.eq(u, v);
    let euz = b.eq(u, z);
    let e = b.fresh();
    b.cl(&[(efxy, false)]);
    b.cl(&[(ex, true)]);
    b.cl(&[(ey, true)]);
    b.cl(&[(ezv, true)]);
    if escape {
        b.cl(&[(euv, true), (euz, true), (e, true)]);
    } else {
        b.cl(&[(euv, true), (euz, true)]);
    }
    b.0
}

#[test]
fn learned_conflict_over_two_rounds() {
    assert!(!check(late_congruence_conflict(false)));
    assert!(check(late_congruence_conflict(true)));
}
