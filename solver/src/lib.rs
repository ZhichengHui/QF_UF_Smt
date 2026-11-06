//! A vanilla SMT solver for QF_UF.
//!
//! Input: a CNF formula whose atoms are equalities between ground terms built from uninterpreted
//! function symbols (constants are 0-ary symbols) over one uninterpreted sort. Terms form a DAG:
//! term `i` is `terms[i].fun(terms[i].args[0], ...)` and every argument index is smaller than `i`.
//! Propositional variables can be encoded as equalities `p = true_const`.
//!
//! Algorithm: enumerate every truth assignment of the atoms (naive backtracking). For an
//! assignment that satisfies the clauses propositionally, decide the conjunction of the asserted
//! equalities and disequalities by congruence closure; if it is consistent, read a model off the
//! congruence classes.
//!
//! The model interprets the sort as natural numbers (the class representative of each term) and
//! each function symbol by a table of entries; an application not in the table has value 0.

pub struct Term {
    pub fun: usize,
    pub args: Vec<usize>,
}

pub struct Atom {
    pub lhs: usize,
    pub rhs: usize,
}

pub struct Lit {
    pub atom: usize,
    pub pos: bool,
}

pub struct Clause {
    pub lits: Vec<Lit>,
}

pub struct Problem {
    pub terms: Vec<Term>,
    pub atoms: Vec<Atom>,
    pub clauses: Vec<Clause>,
}

/// `fun(args) = val` in the model; the first matching entry counts.
#[derive(Clone)]
pub struct Entry {
    pub fun: usize,
    pub args: Vec<usize>,
    pub val: usize,
}

pub struct Model {
    pub entries: Vec<Entry>,
}

pub enum Answer {
    Sat(Model),
    Unsat,
}

/// Does some literal of `c` hold under the atom assignment `a`?
fn clause_holds(a: &[bool], c: &Clause) -> bool {
    for i in 0..c.lits.len() {
        if a[c.lits[i].atom] == c.lits[i].pos {
            return true;
        }
    }
    false
}

/// Does every clause of `p` hold under the atom assignment `a`?
fn prop_holds(p: &Problem, a: &[bool]) -> bool {
    for i in 0..p.clauses.len() {
        if !clause_holds(a, &p.clauses[i]) {
            return false;
        }
    }
    true
}

/// Merges the class of `a` into the class of `b`.
fn merge(rep: &mut Vec<usize>, a: usize, b: usize) {
    let ra = rep[a];
    let rb = rep[b];
    for i in 0..rep.len() {
        if rep[i] == ra {
            rep[i] = rb;
        }
    }
}

/// Do terms `i` and `j` apply the same symbol to arguments of the same classes?
fn congruent(p: &Problem, rep: &[usize], i: usize, j: usize) -> bool {
    let ti = &p.terms[i];
    let tj = &p.terms[j];
    if ti.fun != tj.fun || ti.args.len() != tj.args.len() {
        return false;
    }
    for k in 0..ti.args.len() {
        if rep[ti.args[k]] != rep[tj.args[k]] {
            return false;
        }
    }
    true
}

/// Merges every term congruent to term `i` but in another class into the class of `i`'s partner;
/// returns whether it merged anything.
fn scan_row(p: &Problem, rep: &mut Vec<usize>, i: usize) -> bool {
    let mut changed = false;
    for j in 0..p.terms.len() {
        if rep[i] != rep[j] && congruent(p, rep, i, j) {
            merge(rep, i, j);
            changed = true;
        }
    }
    changed
}

/// One round of `scan_row` over all terms; returns whether it merged anything.
fn scan(p: &Problem, rep: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..p.terms.len() {
        if scan_row(p, rep, i) {
            changed = true;
        }
    }
    changed
}

/// Merges congruent terms until no two terms of different classes are congruent. Every round that
/// merges reduces the number of classes, so the `n + 1`-th round at the latest merges nothing.
fn close(p: &Problem, rep: &mut Vec<usize>) {
    for _round in 0..p.terms.len() + 1 {
        if !scan(p, rep) {
            return;
        }
    }
}

/// The model of a congruence-closed partition: each term's value is its representative.
fn build_model(p: &Problem, rep: &[usize]) -> Model {
    let n = p.terms.len();
    let mut entries = vec![Entry { fun: 0, args: Vec::new(), val: 0 }; n];
    for i in 0..n {
        let mut args = p.terms[i].args.clone();
        for k in 0..args.len() {
            args[k] = rep[args[k]];
        }
        entries[i] = Entry { fun: p.terms[i].fun, args: args, val: rep[i] };
    }
    Model { entries: entries }
}

/// A model in which exactly the atoms `k` with `a[k]` hold, if there is one.
fn theory_check(p: &Problem, a: &[bool]) -> Option<Model> {
    let n = p.terms.len();
    let mut rep = vec![0; n];
    for i in 0..n {
        rep[i] = i;
    }
    for k in 0..p.atoms.len() {
        if a[k] {
            merge(&mut rep, p.atoms[k].lhs, p.atoms[k].rhs);
        }
    }
    close(p, &mut rep);
    for k in 0..p.atoms.len() {
        if !a[k] && rep[p.atoms[k].lhs] == rep[p.atoms[k].rhs] {
            return None;
        }
    }
    Some(build_model(p, &rep))
}

/// Tries every completion of the assignment `a` of atoms `k..`.
fn search(p: &Problem, a: Vec<bool>, k: usize) -> Option<Model> {
    if k == a.len() {
        if prop_holds(p, &a) {
            return theory_check(p, &a);
        }
        return None;
    }
    let mut a1 = a.clone();
    a1[k] = true;
    let r = search(p, a1, k + 1);
    if r.is_some() {
        return r;
    }
    let mut a2 = a.clone();
    a2[k] = false;
    search(p, a2, k + 1)
}

pub fn solve(p: &Problem) -> Answer {
    match search(p, vec![false; p.atoms.len()], 0) {
        Some(m) => Answer::Sat(m),
        None => Answer::Unsat,
    }
}
