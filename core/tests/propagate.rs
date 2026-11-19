//! Regression tests for theory propagation (#56): quasigroup problems in the style of the
//! QG-classification family, where the closure of the true atoms decides many unset atoms.
//! Every Sat model is checked by an independent evaluator and every answer is compared with z3
//! when the `z3` binary is on PATH. The helpers up to `B` are copied from `learn.rs`.

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

/// The time limit for one problem.
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

    fn cl(&mut self, lits: &[(usize, bool)]) {
        self.0.clauses.push(clause(lits));
    }
}


/// A quasigroup of order `n` on the distinct constants `e_0, ..., e_{n-1}`: every product
/// `e_i * e_j` is one of them, and every row and column of the table has distinct entries. With
/// `idem`, every `e_i * e_i = e_i`; with `comm`, every `e_i * e_j = e_j * e_i`.
fn quasigroup(n: usize, idem: bool, comm: bool, qg5: bool) -> Problem {
    let mut b = B::new();
    let es: Vec<usize> = (0..n).map(|_| b.konst()).collect();
    for i in 0..n {
        for j in i + 1..n {
            let d = b.eq(es[i], es[j]);
            b.cl(&[(d, false)]);
        }
    }
    let mut prod = vec![vec![0; n]; n];
    for i in 0..n {
        for j in 0..n {
            prod[i][j] = b.app(7, &[es[i], es[j]]);
        }
    }
    for i in 0..n {
        for j in 0..n {
            let lits: Vec<(usize, bool)> = (0..n).map(|k| (b.eq(prod[i][j], es[k]), true)).collect();
            b.cl(&lits);
        }
    }
    for i in 0..n {
        for j in 0..n {
            for k in j + 1..n {
                let r = b.eq(prod[i][j], prod[i][k]);
                b.cl(&[(r, false)]);
                let c = b.eq(prod[j][i], prod[k][i]);
                b.cl(&[(c, false)]);
            }
        }
    }
    for i in 0..n {
        if idem {
            let a = b.eq(prod[i][i], es[i]);
            b.cl(&[(a, true)]);
        }
        if qg5 {
            for j in 0..n {
                // ((e_j * e_i) * e_j) * e_j = e_i
                let a1 = b.app(7, &[es[j], es[i]]);
                let a2 = b.app(7, &[a1, es[j]]);
                let a3 = b.app(7, &[a2, es[j]]);
                let a = b.eq(a3, es[i]);
                b.cl(&[(a, true)]);
            }
        }
        for j in i + 1..n {
            if comm {
                let a = b.eq(prod[i][j], prod[j][i]);
                b.cl(&[(a, true)]);
            }
        }
    }
    b.0
}

/// Idempotent quasigroups with the identity `((y * x) * y) * y = x` (QG5), also commutative ones
/// (the expected answers are z3's). Order 8 is the
/// regression test of theory propagation: with it `solve` takes about 5 s, without it (main
/// before #56) about 30 s, beyond `LIMIT`.
#[test]
fn qg5_quasigroups() {
    for n in 3..9 {
        assert_eq!(check(quasigroup(n, true, false, true)), n == 5 || n >= 7);
    }
    for n in 3..8 {
        assert_eq!(check(quasigroup(n, true, true, true)), n == 7);
    }
}

/// Quasigroups without identities, and the commutative idempotent ones (which exist exactly for
/// odd orders).
#[test]
fn quasigroups() {
    for n in 3..7 {
        assert!(check(quasigroup(n, false, false, false)));
        assert!(check(quasigroup(n, true, false, false)));
        assert_eq!(check(quasigroup(n, true, true, false)), n % 2 == 1);
    }
}
