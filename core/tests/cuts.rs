//! Regression tests for the search cuts (a clause falsified by the assigned prefix, #34) and the
//! congruence closure (#36): problems where a conflict appears among the first atoms, duplicate
//! constants, congruences that need several rounds of `close`, the eq_diamond family, and larger
//! random problems. Every Sat model is checked by an independent evaluator and every answer is
//! compared with z3 when the `z3` binary is on PATH. The helpers are copied from `solve.rs`.

use qfuf::*;
use std::io::Write;
use std::process::{Command, Stdio};

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

/// Returns whether `solve` answered Sat; panics if a model is wrong or z3 disagrees.
fn check(p: &Problem) -> bool {
    let sat = match solve(p) {
        Answer::Sat(m) => {
            assert!(eval(&m, p), "wrong model for\n{}", smtlib(p));
            true
        }
        Answer::Unsat => false,
    };
    if let Some(z) = z3_sat(p) {
        assert_eq!(sat, z, "z3 disagrees on\n{}", smtlib(p));
    }
    sat
}

/// `p` with `n` extra constants and atoms `c_i = c_{i+1}` that occur in no clause, after the
/// atoms of `p`: they multiply the leaves below any prefix of `p`'s atoms by `2^n`.
fn with_free_atoms(mut p: Problem, n: usize) -> Problem {
    let base = p.terms.len();
    for i in 0..=n {
        p.terms.push(term(100 + i, &[]));
    }
    for i in 0..n {
        p.atoms.push(atom(base + i, base + i + 1));
    }
    p
}

/// `p` with a tautology `l or not l` for every atom from `first` on, so that these atoms occur
/// in clauses.
fn with_tautologies(mut p: Problem, first: usize) -> Problem {
    for k in first..p.atoms.len() {
        p.clauses.push(clause(&[(k, true), (k, false)]));
    }
    p
}

#[test]
fn clause_falsified_by_early_prefix() {
    // Atoms 0 (a = b) and 1 (b = c) are both forced by unit clauses, and the clause
    // `a != b or b != c` is falsified as soon as both are assigned; 12 later atoms are free.
    let base = Problem {
        terms: vec![term(0, &[]), term(1, &[]), term(2, &[])],
        atoms: vec![atom(0, 1), atom(1, 2)],
        clauses: vec![clause(&[(0, true)]), clause(&[(1, true)]), clause(&[(0, false), (1, false)])],
    };
    let p = with_tautologies(with_free_atoms(base, 12), 2);
    assert!(!check(&p));

    // Satisfiable variants: a later atom must be true (a cut that treats unassigned atoms as
    // assigned false would lose the model) ...
    let mut q = with_free_atoms(
        Problem {
            terms: vec![term(0, &[]), term(1, &[])],
            atoms: vec![atom(0, 1)],
            clauses: vec![clause(&[(0, false)])],
        },
        8,
    );
    q.clauses.push(clause(&[(8, true)]));
    q.clauses.push(clause(&[(0, true), (5, true)]));
    assert!(check(&q));
    // ... and an early atom must be true (a cut on a true atom would lose the model).
    let r = with_free_atoms(
        Problem {
            terms: vec![term(0, &[]), term(1, &[]), term(2, &[])],
            atoms: vec![atom(0, 1), atom(1, 2)],
            clauses: vec![clause(&[(0, true)]), clause(&[(1, true)])],
        },
        6,
    );
    assert!(check(&r));
}

#[test]
fn congruence_conflict_in_prefix() {
    // a = b and f(a) != f(b) are atoms 0 and 1; 10 later atoms are free and occur in clauses.
    let base = Problem {
        terms: vec![term(0, &[]), term(1, &[]), term(2, &[0]), term(2, &[1])],
        atoms: vec![atom(0, 1), atom(2, 3)],
        clauses: vec![clause(&[(0, true)]), clause(&[(1, false)])],
    };
    let p = with_tautologies(with_free_atoms(base, 10), 2);
    assert!(!check(&p));

    // The conflict is reached only after the clause `a = b or g(a) = g(b)` and `g(a) != g(b)`.
    let q = with_tautologies(
        with_free_atoms(
            Problem {
                terms: vec![
                    term(0, &[]),
                    term(1, &[]),
                    term(2, &[0]),
                    term(2, &[1]),
                    term(3, &[0]),
                    term(3, &[1]),
                ],
                atoms: vec![atom(4, 5), atom(0, 1), atom(2, 3)],
                clauses: vec![
                    clause(&[(0, false)]),
                    clause(&[(1, true), (0, true)]),
                    clause(&[(2, false)]),
                ],
            },
            10,
        ),
        3,
    );
    assert!(!check(&q));

    // Without `f(a) != f(b)` it is satisfiable, and the model must make f(a) = f(b).
    let mut r = with_free_atoms(
        Problem {
            terms: vec![term(0, &[]), term(1, &[]), term(2, &[0]), term(2, &[1])],
            atoms: vec![atom(0, 1), atom(2, 3)],
            clauses: vec![clause(&[(0, true)]), clause(&[(1, false), (1, true)])],
        },
        8,
    );
    r.clauses.push(clause(&[(9, true)]));
    assert!(check(&r));
}

#[test]
fn duplicate_constants() {
    // Terms 0 and 1 are the same constant (symbol 5), so are terms 2 = g(c) and 3 = g(c').
    let p = Problem {
        terms: vec![term(5, &[]), term(5, &[]), term(6, &[0]), term(6, &[1]), term(7, &[])],
        atoms: vec![atom(0, 1), atom(2, 3), atom(2, 4)],
        clauses: vec![clause(&[(0, false), (1, false)])],
    };
    assert!(!check(&p));
    let q = Problem {
        terms: vec![term(5, &[]), term(5, &[]), term(6, &[0]), term(6, &[1]), term(7, &[])],
        atoms: vec![atom(0, 1), atom(2, 3), atom(2, 4)],
        clauses: vec![clause(&[(2, true)]), clause(&[(1, false), (0, true)])],
    };
    assert!(check(&q));
    // A duplicate after other terms, only reached through a congruence of its arguments.
    let r = Problem {
        terms: vec![
            term(5, &[]),
            term(8, &[0]),
            term(9, &[1, 0]),
            term(5, &[]),
            term(8, &[3]),
            term(9, &[4, 3]),
        ],
        atoms: vec![atom(2, 5)],
        clauses: vec![clause(&[(0, false)])],
    };
    assert!(!check(&r));
}

/// Constants `x_0 .. x_n`, `y_0 .. y_n` (terms `0 .. 2n+1`), then `f(x_k)`, `f(y_k)` for
/// `k = 1 .. n` in that order, with `x_n = y_n`, `x_k = f(x_{k+1})`, `y_k = f(y_{k+1})` asserted
/// (and `x_0 != y_0` if `unsat`). Each round of `close` discovers only the congruence of the
/// last pair not yet merged, so `x_0 = y_0` needs `n` rounds that merge.
fn chain(n: usize, unsat: bool) -> Problem {
    let x = |k: usize| k;
    let y = |k: usize| n + 1 + k;
    let mut terms: Vec<Term> = (0..2 * (n + 1)).map(|c| term(c, &[])).collect();
    let mut fx = vec![0; n + 1];
    let mut fy = vec![0; n + 1];
    for k in 1..=n {
        fx[k] = terms.len();
        terms.push(term(50, &[x(k)]));
        fy[k] = terms.len();
        terms.push(term(50, &[y(k)]));
    }
    let mut atoms = vec![atom(x(n), y(n))];
    for k in 0..n {
        atoms.push(atom(x(k), fx[k + 1]));
        atoms.push(atom(y(k), fy[k + 1]));
    }
    let mut clauses: Vec<Clause> = (0..atoms.len()).map(|k| clause(&[(k, true)])).collect();
    atoms.push(atom(x(0), y(0)));
    if unsat {
        clauses.push(clause(&[(atoms.len() - 1, false)]));
    }
    Problem { terms, atoms, clauses }
}

#[test]
fn congruence_chain_over_several_rounds() {
    for n in 1..=6 {
        assert!(!check(&chain(n, true)), "chain {} should be unsat", n);
        assert!(check(&chain(n, false)), "chain {} should be sat", n);
    }
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
        // (A and B) or (C and D) in CNF.
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

#[test]
fn eq_diamond_family() {
    for n in 1..=4 {
        let p = eq_diamond(n);
        assert!(matches!(solve(&p), Answer::Unsat), "eq_diamond {} should be unsat", n);
        assert!(!check(&p));
    }
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
fn random_deeper_against_z3() {
    let mut r = Rng(0x9E3779B97F4A7C15);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..250 {
        let nconst = 1 + r.next(4);
        // Constants may repeat a symbol (duplicate constants).
        let mut terms: Vec<Term> = (0..nconst).map(|_| term(r.next(3), &[])).collect();
        for _ in 0..r.next(12) {
            let i = terms.len();
            // Prefer recent terms as arguments, for deeper nesting.
            let arg = |r: &mut Rng| i - 1 - r.next(i.min(4));
            match r.next(3) {
                0 => terms.push(term(10, &[arg(&mut r)])),
                1 => terms.push(term(11, &[arg(&mut r), arg(&mut r)])),
                _ => terms.push(term(12, &[arg(&mut r), arg(&mut r), arg(&mut r)])),
            }
        }
        let n = terms.len();
        let mut atoms: Vec<Atom> = Vec::new();
        let mut clauses: Vec<Clause> = Vec::new();
        // Sometimes a prefix `a = b`, `f(a) != f(b)` as the first atoms.
        if r.next(4) == 0 && n >= 2 {
            let (a, b) = (r.next(n), r.next(n));
            terms.push(term(10, &[a]));
            terms.push(term(10, &[b]));
            atoms.push(atom(a, b));
            atoms.push(atom(n, n + 1));
            clauses.push(clause(&[(0, true)]));
            clauses.push(clause(&[(1, false)]));
        }
        let n = terms.len();
        for _ in 0..2 + r.next(9) {
            atoms.push(atom(r.next(n), r.next(n)));
        }
        for _ in 0..1 + r.next(10) {
            let lits: Vec<(usize, bool)> =
                (0..1 + r.next(3)).map(|_| (r.next(atoms.len()), r.next(3) != 0)).collect();
            clauses.push(clause(&lits));
        }
        if check(&Problem { terms, atoms, clauses }) {
            sat += 1
        } else {
            unsat += 1
        }
    }
    eprintln!("random deeper: {} sat, {} unsat", sat, unsat);
    assert!(sat > 40 && unsat > 40);
}
