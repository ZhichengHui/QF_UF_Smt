//! Checks every Sat answer's model with an independent evaluator, and compares Sat/Unsat with z3
//! (when the `z3` binary is on PATH) on hand-written and random problems.

use qfuf::*;
use std::io::Write;
use std::process::{Command, Stdio};

fn term(fun: usize, args: &[usize]) -> Term {
    Term { fun, args: args.to_vec() }
}

fn lit(atom: usize, pos: bool) -> Lit {
    Lit { atom, pos }
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

/// Returns whether `solve` answered Sat; panics if a model is wrong or z3 disagrees.
fn check(p: &Problem) -> bool {
    let sat = match solve(p) {
        Answer::Sat(m) => {
            assert!(eval(&m, p), "wrong model");
            true
        }
        Answer::Unsat => false,
    };
    if let Some(z) = z3_sat(p) {
        assert_eq!(sat, z, "z3 disagrees on\n{}", smtlib(p));
    }
    sat
}

#[test]
fn classic_unsat() {
    // Terms a, f(a), ..., f^5(a): f^3(a) = a, f^5(a) = a, f(a) != a.
    let mut terms = vec![term(0, &[])];
    for i in 0..5 {
        terms.push(term(1, &[i]));
    }
    let p = Problem {
        terms,
        atoms: vec![Atom { lhs: 3, rhs: 0 }, Atom { lhs: 5, rhs: 0 }, Atom { lhs: 1, rhs: 0 }],
        clauses: vec![
            Clause { lits: vec![lit(0, true)] },
            Clause { lits: vec![lit(1, true)] },
            Clause { lits: vec![lit(2, false)] },
        ],
    };
    assert!(!check(&p));
}

#[test]
fn needs_disjunction() {
    // a = b, (f(a) != f(b) or g(a) = c), c != g(b): unsat.
    let p = Problem {
        terms: vec![
            term(0, &[]),
            term(1, &[]),
            term(2, &[]),
            term(3, &[0]),
            term(3, &[1]),
            term(4, &[0]),
            term(4, &[1]),
        ],
        atoms: vec![
            Atom { lhs: 0, rhs: 1 },
            Atom { lhs: 3, rhs: 4 },
            Atom { lhs: 5, rhs: 2 },
            Atom { lhs: 2, rhs: 6 },
        ],
        clauses: vec![
            Clause { lits: vec![lit(0, true)] },
            Clause { lits: vec![lit(1, false), lit(2, true)] },
            Clause { lits: vec![lit(3, false)] },
        ],
    };
    assert!(!check(&p));
    // Without a = b it is satisfiable.
    let mut q = p;
    q.clauses.remove(0);
    assert!(check(&q));
}

#[test]
fn empty_and_trivial() {
    assert!(check(&Problem { terms: vec![], atoms: vec![], clauses: vec![] }));
    let empty_clause = Problem { terms: vec![], atoms: vec![], clauses: vec![Clause { lits: vec![] }] };
    assert!(!check(&empty_clause));
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

#[test]
fn random_against_z3() {
    let mut r = Rng(0x2545F4914F6CDD1D);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..400 {
        let nconst = 1 + r.next(3);
        let mut terms: Vec<Term> = (0..nconst).map(|c| term(c, &[])).collect();
        for _ in 0..r.next(6) {
            let i = terms.len();
            if r.next(2) == 0 {
                terms.push(term(10, &[r.next(i)]));
            } else {
                terms.push(term(11, &[r.next(i), r.next(i)]));
            }
        }
        let n = terms.len();
        let atoms: Vec<Atom> =
            (0..1 + r.next(5)).map(|_| Atom { lhs: r.next(n), rhs: r.next(n) }).collect();
        let clauses: Vec<Clause> = (0..1 + r.next(6))
            .map(|_| Clause {
                lits: (0..1 + r.next(3)).map(|_| lit(r.next(atoms.len()), r.next(3) != 0)).collect(),
            })
            .collect();
        if check(&Problem { terms, atoms, clauses }) {
            sat += 1
        } else {
            unsat += 1
        }
    }
    eprintln!("random: {} sat, {} unsat", sat, unsat);
    assert!(sat > 50 && unsat > 50);
}
