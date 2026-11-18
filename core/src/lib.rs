//! A vanilla SMT solver for QF_UF.
//!
//! Input: a CNF formula whose atoms are equalities between ground terms built from uninterpreted
//! function symbols (constants are 0-ary symbols) over one uninterpreted sort. Terms form a DAG:
//! term `i` is `terms[i].fun(terms[i].args[0], ...)` and every argument index is smaller than `i`.
//! Propositional variables can be encoded as equalities `p = true_const`.
//!
//! Algorithm: enumerate the truth assignments of the atoms by backtracking, cutting a branch as
//! soon as the assigned atoms falsify a clause. For an assignment that satisfies the clauses
//! propositionally, decide the conjunction of the asserted equalities and disequalities by
//! congruence closure; if it is consistent, read a model off the congruence classes.
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

/// Is every literal of `c` on an atom below `k` and false under `a`?
fn clause_falsified(a: &[bool], c: &Clause, k: usize) -> bool {
    for i in 0..c.lits.len() {
        if c.lits[i].atom >= k || a[c.lits[i].atom] == c.lits[i].pos {
            return false;
        }
    }
    true
}

/// Does the assignment `a` of the atoms `0..k` falsify some clause of `p`?
fn some_clause_falsified(p: &Problem, a: &[bool], k: usize) -> bool {
    for i in 0..p.clauses.len() {
        if clause_falsified(a, &p.clauses[i], k) {
            return true;
        }
    }
    false
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

/// The representatives of the terms `args`.
fn rep_args(rep: &[usize], args: &[usize]) -> Vec<usize> {
    let mut out = args.to_vec();
    for k in 0..out.len() {
        out[k] = rep[out[k]];
    }
    out
}

/// The model of a congruence-closed partition: each term's value is its representative.
fn build_model(p: &Problem, rep: &[usize]) -> Model {
    let mut entries = vec![Entry { fun: 0, args: Vec::new(), val: 0 }; p.terms.len()];
    for i in 0..p.terms.len() {
        entries[i] = Entry { fun: p.terms[i].fun, args: rep_args(rep, &p.terms[i].args), val: rep[i] };
    }
    Model { entries: entries }
}

/// The partition of `n` terms into singletons.
fn init_rep(n: usize) -> Vec<usize> {
    let mut rep = vec![0; n];
    for i in 0..n {
        rep[i] = i;
    }
    rep
}

/// Merges the two sides of every atom `k` with `a[k]`.
fn assert_eqs(p: &Problem, a: &[bool], rep: &mut Vec<usize>) {
    for k in 0..p.atoms.len() {
        if a[k] {
            merge(rep, p.atoms[k].lhs, p.atoms[k].rhs);
        }
    }
}

/// Are the two sides of every atom `k` without `a[k]` in different classes?
fn diseqs_ok(p: &Problem, a: &[bool], rep: &[usize]) -> bool {
    for k in 0..p.atoms.len() {
        if !a[k] && rep[p.atoms[k].lhs] == rep[p.atoms[k].rhs] {
            return false;
        }
    }
    true
}

/// The model of the closed partition `rep` if it keeps the sides of every unset atom apart.
/// `rep` is `&mut` although `finish` only reads it: then `theory_check` passes `rep` on without
/// reading it after `close`, which AutoCorrode's `crush` could not handle.
fn finish(p: &Problem, a: &[bool], rep: &mut Vec<usize>) -> Option<Model> {
    if diseqs_ok(p, a, rep) { Some(build_model(p, rep)) } else { None }
}

/// A model in which exactly the atoms `k` with `a[k]` hold, if there is one.
fn theory_check(p: &Problem, a: &[bool]) -> Option<Model> {
    let mut rep = init_rep(p.terms.len());
    assert_eqs(p, a, &mut rep);
    close(p, &mut rep);
    finish(p, a, &mut rep)
}

/// Tries every completion of the assignment `a` of atoms `k..`; cuts the branch as soon as the
/// assigned atoms `0..k` falsify a clause.
fn search(p: &Problem, a: Vec<bool>, k: usize) -> Option<Model> {
    if k == a.len() {
        if prop_holds(p, &a) {
            return theory_check(p, &a);
        }
        return None;
    }
    if some_clause_falsified(p, &a, k) {
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

// ---------------------------------------------------------------------------------------------
// The general problem structure: the interface to the SMT-LIB front end. These definitions are,
// word for word, those of the front end (`frontend/src/problem.rs`); see there for their meaning.

/// A sort.
pub enum SmtSort {
    Bool,
    /// `(_ BitVec w)`, `w >= 1`.
    BitVec(usize),
    /// The uninterpreted sort with this number.
    Uninterpreted(usize),
}

/// The theory function symbols of Core and FixedSizeBitVectors/QF_BV (SMT-LIB 2.6).
pub enum SmtOp {
    // Core
    Not,
    And,
    Or,
    Xor,
    Implies,
    Eq,
    Distinct,
    Ite,
    // FixedSizeBitVectors
    Concat,
    /// `(_ extract i j)`.
    Extract(usize, usize),
    Bvnot,
    Bvand,
    Bvor,
    Bvneg,
    Bvadd,
    Bvmul,
    Bvudiv,
    Bvurem,
    Bvshl,
    Bvlshr,
    Bvult,
    // QF_BV extensions
    Bvnand,
    Bvnor,
    Bvxor,
    Bvxnor,
    Bvcomp,
    Bvsub,
    Bvsdiv,
    Bvsrem,
    Bvsmod,
    Bvashr,
    /// `(_ repeat i)`.
    Repeat(usize),
    /// `(_ zero_extend i)`.
    ZeroExtend(usize),
    /// `(_ sign_extend i)`.
    SignExtend(usize),
    /// `(_ rotate_left i)`.
    RotateLeft(usize),
    /// `(_ rotate_right i)`.
    RotateRight(usize),
    Bvule,
    Bvugt,
    Bvuge,
    Bvslt,
    Bvsle,
    Bvsgt,
    Bvsge,
}

/// A term.
pub enum SmtTerm {
    BoolConst(bool),
    /// A bit-vector constant, least significant bit first.
    BvConst(Vec<bool>),
    /// The parameter with this number of the enclosing definition.
    Param(usize),
    /// A declared function symbol applied to arguments (none for a constant).
    Fun(usize, Vec<SmtTerm>),
    /// A defined function applied to arguments (one per parameter).
    Def(usize, Vec<SmtTerm>),
    /// A theory function symbol applied to arguments.
    App(SmtOp, Vec<SmtTerm>),
}

/// A declared function symbol: the sorts of its arguments and of its result.
pub struct SmtFun {
    pub args: Vec<SmtSort>,
    pub ret: SmtSort,
}

/// A defined function: the sorts of its parameters and of its result, and its body.
pub struct SmtDef {
    pub params: Vec<SmtSort>,
    pub ret: SmtSort,
    pub body: SmtTerm,
}

pub struct SmtProblem {
    pub num_sorts: usize,
    pub funs: Vec<SmtFun>,
    pub defs: Vec<SmtDef>,
    pub asserts: Vec<SmtTerm>,
}

/// A value: a truth value, a bit-vector (least significant bit first) or an element of an
/// uninterpreted sort (an index into its domain).
pub enum SmtValue {
    Bool(bool),
    Bv(Vec<bool>),
    Elem(usize),
}

/// One point of a function table: the arguments and the value there.
pub struct SmtEntry {
    pub args: Vec<SmtValue>,
    pub val: SmtValue,
}

/// The interpretation of a declared function symbol: at given arguments, the value of the first
/// entry with these arguments, and `default` if there is none (for a constant: the first entry, if
/// there is one).
pub struct SmtInterp {
    pub entries: Vec<SmtEntry>,
    pub default: SmtValue,
}

/// A model: the size of the domain of every uninterpreted sort (at least 1; the elements are
/// `Elem(0)` to `Elem(size - 1)`) and the interpretation of every declared function symbol.
pub struct SmtModel {
    pub domains: Vec<usize>,
    pub funs: Vec<SmtInterp>,
}

/// The answer to `check-sat`. `Unknown` is the answer for a problem the solver does not handle.
pub enum SmtAnswer {
    Sat(SmtModel),
    Unsat,
    Unknown,
}

// ---------------------------------------------------------------------------------------------
// Translation of a general problem into a problem of this solver.
//
// A general problem is in the fragment of this solver if no bit-vector sort, constant or function
// occurs in it. For a well-sorted problem (as the front end produces), every sort is then Bool or
// uninterpreted. All uninterpreted sorts become the one sort of this solver, and Booleans are
// encoded:
// * Two new constants TRUE and FALSE (terms 0 and 1), with the atoms `TRUE = TRUE` (atom 0,
//   always true; the truth values are its two literals) and `TRUE = FALSE` (atom 1, false by a
//   unit clause).
// * A Boolean term becomes a literal: an application of a declared symbol `p` of result sort Bool
//   is the atom `p(..) = TRUE`; the connectives, and `=`, `distinct`, `ite` on Booleans, get a new
//   literal (a new constant `v` and the atom `v = TRUE`) defined by clauses (Tseitin encoding).
// * A term of an uninterpreted sort becomes a term. A Boolean argument of a declared symbol is a
//   new constant `c` with the clauses `l -> c = TRUE` and `not l -> c = FALSE`; an `ite` of an
//   uninterpreted sort is a new constant `c` with `cond -> c = a` and `not cond -> c = b`.
// * Each assertion is a unit clause.
// Declared symbol `f` keeps its number; TRUE, FALSE and the new constants are numbered after the
// declared symbols. A definition without parameters is translated once; a definition with
// parameters is expanded where it is applied.

/// A translated term: a term of this solver, or a literal (an atom with a polarity).
pub enum Enc {
    Term(usize),
    Lit(usize, bool),
}

/// The state of the translation: the terms, atoms and clauses built so far, and the next unused
/// function symbol.
pub struct Tr {
    pub terms: Vec<Term>,
    pub atoms: Vec<Atom>,
    pub clauses: Vec<Clause>,
    pub next_fun: usize,
}

fn copy_enc(e: &Enc) -> Enc {
    match e {
        Enc::Term(i) => Enc::Term(*i),
        Enc::Lit(a, pos) => Enc::Lit(*a, *pos),
    }
}

fn add_term(s: Tr, fun: usize, args: Vec<usize>) -> (Tr, usize) {
    let k = s.terms.len();
    let mut terms = s.terms;
    terms.push(Term { fun, args });
    (Tr { terms, atoms: s.atoms, clauses: s.clauses, next_fun: s.next_fun }, k)
}

fn add_atom(s: Tr, lhs: usize, rhs: usize) -> (Tr, usize) {
    let k = s.atoms.len();
    let mut atoms = s.atoms;
    atoms.push(Atom { lhs, rhs });
    (Tr { terms: s.terms, atoms, clauses: s.clauses, next_fun: s.next_fun }, k)
}

fn add_clause(s: Tr, lits: Vec<Lit>) -> Tr {
    let mut clauses = s.clauses;
    clauses.push(Clause { lits });
    Tr { terms: s.terms, atoms: s.atoms, clauses, next_fun: s.next_fun }
}

/// A new constant (a new function symbol applied to nothing); returns its term.
fn new_const(s: Tr) -> (Tr, usize) {
    let f = s.next_fun;
    let (s, t) = add_term(Tr { terms: s.terms, atoms: s.atoms, clauses: s.clauses, next_fun: f + 1 }, f, Vec::new());
    (s, t)
}

/// A new literal: a new constant `v` and the atom `v = TRUE`.
fn new_lit(s: Tr) -> (Tr, usize) {
    let (s, v) = new_const(s);
    add_atom(s, v, 0)
}

fn lit(a: usize, pos: bool) -> Lit {
    Lit { atom: a, pos }
}

/// The literal of a translated Boolean term.
fn enc_lit(e: &Enc) -> (usize, bool) {
    match e {
        Enc::Lit(a, pos) => (*a, *pos),
        Enc::Term(_) => (0, true),
    }
}

/// The term of a translated term of an uninterpreted sort, or for a Boolean term a new constant
/// equal to TRUE or FALSE as the literal holds.
fn enc_term(s: Tr, e: &Enc) -> (Tr, usize) {
    match e {
        Enc::Term(i) => (s, *i),
        Enc::Lit(a, pos) => {
            let (s, c) = new_const(s);
            let (s, ct) = add_atom(s, c, 0);
            let (s, cf) = add_atom(s, c, 1);
            let s = add_clause(s, clause2(lit(*a, !*pos), lit(ct, true)));
            let s = add_clause(s, clause2(lit(*a, *pos), lit(cf, true)));
            (s, c)
        }
    }
}

/// A new literal equivalent to the conjunction (`conj`) or disjunction of the literals `ls`.
fn gate_andor(s: Tr, ls: &Vec<(usize, bool)>, conj: bool) -> (Tr, Enc) {
    let (s, v) = new_lit(s);
    let mut s = s;
    // conj: v -> l_i for every i, and (all l_i) -> v. disj: l_i -> v, and v -> (some l_i).
    let mut big = clause1(lit(v, conj));
    let mut i: usize = 0;
    while i < ls.len() {
        let (a, pos) = ls[i];
        if conj {
            s = add_clause(s, clause2(lit(v, false), lit(a, pos)));
        } else {
            s = add_clause(s, clause2(lit(v, true), lit(a, !pos)));
        }
        big.push(lit(a, if conj { !pos } else { pos }));
        i += 1;
    }
    let s = add_clause(s, big);
    (s, Enc::Lit(v, true))
}

fn clause1(a: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c
}

fn clause2(a: Lit, b: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c.push(b);
    c
}

fn clause3(a: Lit, b: Lit, d: Lit) -> Vec<Lit> {
    let mut c = Vec::new();
    c.push(a);
    c.push(b);
    c.push(d);
    c
}

/// A new literal equivalent to `x xor y`.
fn gate_xor(s: Tr, x: (usize, bool), y: (usize, bool)) -> (Tr, (usize, bool)) {
    let (s, v) = new_lit(s);
    let (a, pa) = x;
    let (b, pb) = y;
    let s = add_clause(s, clause3(lit(v, false), lit(a, pa), lit(b, pb)));
    let s = add_clause(s, clause3(lit(v, false), lit(a, !pa), lit(b, !pb)));
    let s = add_clause(s, clause3(lit(v, true), lit(a, !pa), lit(b, pb)));
    let s = add_clause(s, clause3(lit(v, true), lit(a, pa), lit(b, !pb)));
    (s, (v, true))
}

/// A new literal equivalent to `if c then x else y`.
fn gate_ite(s: Tr, c: (usize, bool), x: (usize, bool), y: (usize, bool)) -> (Tr, Enc) {
    let (s, v) = new_lit(s);
    let (kc, pc) = c;
    let (a, pa) = x;
    let (b, pb) = y;
    let s = add_clause(s, clause3(lit(kc, !pc), lit(a, !pa), lit(v, true)));
    let s = add_clause(s, clause3(lit(kc, !pc), lit(a, pa), lit(v, false)));
    let s = add_clause(s, clause3(lit(kc, pc), lit(b, !pb), lit(v, true)));
    let s = add_clause(s, clause3(lit(kc, pc), lit(b, pb), lit(v, false)));
    (s, Enc::Lit(v, true))
}

fn is_lit(e: &Enc) -> bool {
    match e {
        Enc::Lit(_, _) => true,
        Enc::Term(_) => false,
    }
}

/// `=` (chainable) or `distinct` (pairwise) on the translated arguments `es`.
fn enc_eq(s: Tr, es: &Vec<Enc>, distinct: bool) -> (Tr, Enc) {
    let mut s = s;
    let mut ls = Vec::new();
    let mut i: usize = 0;
    while i < es.len() {
        let mut j: usize = i + 1;
        while j < es.len() {
            if distinct || j == i + 1 {
                // The literal of es[i] = es[j].
                if is_lit(&es[i]) {
                    let (s1, (x, px)) = gate_xor(s, enc_lit(&es[i]), enc_lit(&es[j]));
                    s = s1;
                    ls.push((x, if distinct { px } else { !px }));
                } else {
                    let (s1, ti) = enc_term(s, &es[i]);
                    let (s2, tj) = enc_term(s1, &es[j]);
                    let (s3, k) = add_atom(s2, ti, tj);
                    s = s3;
                    ls.push((k, !distinct));
                }
            }
            j += 1;
        }
        i += 1;
    }
    gate_andor(s, &ls, true)
}

/// A theory function of Core applied to the translated arguments `es`.
fn enc_app(s: Tr, o: &SmtOp, es: &Vec<Enc>) -> (Tr, Enc) {
    match o {
        SmtOp::Not => {
            let (a, pos) = enc_lit(&es[0]);
            (s, Enc::Lit(a, !pos))
        }
        SmtOp::And | SmtOp::Or => {
            let mut ls = Vec::new();
            let mut i: usize = 0;
            while i < es.len() {
                ls.push(enc_lit(&es[i]));
                i += 1;
            }
            gate_andor(s, &ls, match o {
                SmtOp::And => true,
                _ => false,
            })
        }
        SmtOp::Xor => {
            let mut s = s;
            let mut acc = enc_lit(&es[0]);
            let mut i: usize = 1;
            while i < es.len() {
                let (s1, x) = gate_xor(s, acc, enc_lit(&es[i]));
                s = s1;
                acc = x;
                i += 1;
            }
            let (a, pos) = acc;
            (s, Enc::Lit(a, pos))
        }
        SmtOp::Implies => {
            // Right associative: (=> a b c) is (or (not a) (not b) c).
            let mut ls = Vec::new();
            let mut i: usize = 0;
            while i < es.len() {
                let (a, pos) = enc_lit(&es[i]);
                ls.push((a, if i + 1 < es.len() { !pos } else { pos }));
                i += 1;
            }
            gate_andor(s, &ls, false)
        }
        SmtOp::Eq => enc_eq(s, es, false),
        SmtOp::Distinct => enc_eq(s, es, true),
        SmtOp::Ite => {
            if is_lit(&es[1]) {
                gate_ite(s, enc_lit(&es[0]), enc_lit(&es[1]), enc_lit(&es[2]))
            } else {
                let (kc, pc) = enc_lit(&es[0]);
                let (s, c) = new_const(s);
                let (s, ta) = enc_term(s, &es[1]);
                let (s, tb) = enc_term(s, &es[2]);
                let (s, ka) = add_atom(s, c, ta);
                let (s, kb) = add_atom(s, c, tb);
                let s = add_clause(s, clause2(lit(kc, !pc), lit(ka, true)));
                let s = add_clause(s, clause2(lit(kc, pc), lit(kb, true)));
                (s, Enc::Term(c))
            }
        }
        _ => (s, Enc::Lit(0, true)),
    }
}

/// The translated arguments `ts`.
fn enc_args(p: &SmtProblem, dm: &Vec<Enc>, env: &Vec<Enc>, s: Tr, ts: &Vec<SmtTerm>) -> (Tr, Vec<Enc>) {
    let mut s = s;
    let mut es = Vec::new();
    let mut i: usize = 0;
    while i < ts.len() {
        let (s1, e) = enc(p, dm, env, s, &ts[i]);
        s = s1;
        es.push(e);
        i += 1;
    }
    (s, es)
}

/// The translation of `t`. `env` gives the translation of each parameter of the enclosing
/// definition, `dm` that of each definition without parameters of `p` translated so far.
fn enc(p: &SmtProblem, dm: &Vec<Enc>, env: &Vec<Enc>, s: Tr, t: &SmtTerm) -> (Tr, Enc) {
    match t {
        SmtTerm::BoolConst(b) => (s, Enc::Lit(0, *b)),
        SmtTerm::BvConst(_) => (s, Enc::Lit(0, true)),
        SmtTerm::Param(k) => (s, copy_enc(&env[*k])),
        SmtTerm::Fun(f, args) => {
            let (s, es) = enc_args(p, dm, env, s, args);
            let mut s = s;
            let mut ts = Vec::new();
            let mut i: usize = 0;
            while i < es.len() {
                let (s1, ti) = enc_term(s, &es[i]);
                s = s1;
                ts.push(ti);
                i += 1;
            }
            let (s, k) = add_term(s, *f, ts);
            match &p.funs[*f].ret {
                SmtSort::Bool => {
                    let (s, a) = add_atom(s, k, 0);
                    (s, Enc::Lit(a, true))
                }
                _ => (s, Enc::Term(k)),
            }
        }
        SmtTerm::Def(d, args) => {
            if p.defs[*d].params.len() == 0 {
                (s, copy_enc(&dm[*d]))
            } else {
                let (s, es) = enc_args(p, dm, env, s, args);
                enc(p, dm, &es, s, &p.defs[*d].body)
            }
        }
        SmtTerm::App(o, args) => {
            let (s, es) = enc_args(p, dm, env, s, args);
            enc_app(s, o, &es)
        }
    }
}

fn sort_in_fragment(s: &SmtSort) -> bool {
    match s {
        SmtSort::BitVec(_) => false,
        _ => true,
    }
}

/// Whether no bit-vector constant or function occurs in `t`.
fn term_in_fragment(t: &SmtTerm) -> bool {
    match t {
        SmtTerm::BoolConst(_) | SmtTerm::Param(_) => true,
        SmtTerm::BvConst(_) => false,
        SmtTerm::Fun(_, args) | SmtTerm::Def(_, args) => terms_in_fragment(args),
        SmtTerm::App(o, args) => {
            match o {
                SmtOp::Not | SmtOp::And | SmtOp::Or | SmtOp::Xor | SmtOp::Implies | SmtOp::Eq | SmtOp::Distinct | SmtOp::Ite => {
                    terms_in_fragment(args)
                }
                _ => false,
            }
        }
    }
}

fn terms_in_fragment(ts: &Vec<SmtTerm>) -> bool {
    let mut i: usize = 0;
    while i < ts.len() {
        if !term_in_fragment(&ts[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn sorts_in_fragment(ss: &Vec<SmtSort>) -> bool {
    let mut i: usize = 0;
    while i < ss.len() {
        if !sort_in_fragment(&ss[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether no bit-vector sort, constant or function occurs in `p`.
fn in_fragment(p: &SmtProblem) -> bool {
    let mut i: usize = 0;
    while i < p.funs.len() {
        if !sorts_in_fragment(&p.funs[i].args) || !sort_in_fragment(&p.funs[i].ret) {
            return false;
        }
        i += 1;
    }
    let mut d: usize = 0;
    while d < p.defs.len() {
        if !sorts_in_fragment(&p.defs[d].params) || !sort_in_fragment(&p.defs[d].ret) || !term_in_fragment(&p.defs[d].body) {
            return false;
        }
        d += 1;
    }
    terms_in_fragment(&p.asserts)
}

/// The problem of this solver for `p`.
fn tr_problem(p: &SmtProblem) -> Problem {
    let nf = p.funs.len();
    let s = Tr { terms: Vec::new(), atoms: Vec::new(), clauses: Vec::new(), next_fun: nf + 2 };
    let (s, _) = add_term(s, nf, Vec::new());
    let (s, _) = add_term(s, nf + 1, Vec::new());
    let (s, _) = add_atom(s, 0, 0);
    let (s, _) = add_atom(s, 0, 1);
    let mut s = add_clause(s, clause1(lit(1, false)));
    let mut dm = Vec::new();
    let no_params = Vec::new();
    let mut d: usize = 0;
    while d < p.defs.len() {
        if p.defs[d].params.len() == 0 {
            let (s1, e) = enc(p, &dm, &no_params, s, &p.defs[d].body);
            s = s1;
            dm.push(e);
        } else {
            dm.push(Enc::Lit(0, true));
        }
        d += 1;
    }
    let mut j: usize = 0;
    while j < p.asserts.len() {
        let (s1, e) = enc(p, &dm, &no_params, s, &p.asserts[j]);
        let (a, pos) = enc_lit(&e);
        s = add_clause(s1, clause1(lit(a, pos)));
        j += 1;
    }
    Problem { terms: s.terms, atoms: s.atoms, clauses: s.clauses }
}

/// The value of the constant with function symbol `f` in the model `m`: the value of the first
/// entry for `f` without arguments, 0 if there is none (as the documentation of `Model` says).
fn const_value(m: &Model, f: usize) -> usize {
    let mut i: usize = 0;
    while i < m.entries.len() {
        if m.entries[i].fun == f && m.entries[i].args.len() == 0 {
            return m.entries[i].val;
        }
        i += 1;
    }
    0
}

/// One more than the largest value in the entries of `m` (at least 1).
fn domain_size(m: &Model) -> usize {
    let mut n: usize = 1;
    let mut i: usize = 0;
    while i < m.entries.len() {
        if m.entries[i].val >= n {
            n = m.entries[i].val + 1;
        }
        let mut k: usize = 0;
        while k < m.entries[i].args.len() {
            if m.entries[i].args[k] >= n {
                n = m.entries[i].args[k] + 1;
            }
            k += 1;
        }
        i += 1;
    }
    n
}

/// The value of sort `s` for the element `v` of the model of the translation; `t` is the value
/// of TRUE.
fn value_of(s: &SmtSort, v: usize, t: usize) -> SmtValue {
    match s {
        SmtSort::Bool => SmtValue::Bool(v == t),
        _ => SmtValue::Elem(v),
    }
}

/// The table of declared symbol `f` of `p` from the entries of `m`: the entries for `f` with the
/// right number of arguments whose Boolean arguments are the value `t` of TRUE or `u` of FALSE.
fn tr_interp(p: &SmtProblem, m: &Model, f: usize, t: usize, u: usize) -> SmtInterp {
    let sig = &p.funs[f];
    let mut entries = Vec::new();
    let mut i: usize = 0;
    while i < m.entries.len() {
        let e = &m.entries[i];
        if e.fun == f && e.args.len() == sig.args.len() {
            let mut ok = true;
            let mut args = Vec::new();
            let mut k: usize = 0;
            while k < e.args.len() {
                match &sig.args[k] {
                    SmtSort::Bool => {
                        if e.args[k] != t && e.args[k] != u {
                            ok = false;
                        }
                    }
                    _ => {}
                }
                args.push(value_of(&sig.args[k], e.args[k], t));
                k += 1;
            }
            if ok {
                entries.push(SmtEntry { args, val: value_of(&sig.ret, e.val, t) });
            }
        }
        i += 1;
    }
    SmtInterp { entries, default: value_of(&sig.ret, 0, t) }
}

/// The model of `p` for the model `m` of its translation. Every uninterpreted sort has the
/// domain of `m`.
fn tr_model(p: &SmtProblem, m: &Model) -> SmtModel {
    let nf = p.funs.len();
    let t = const_value(m, nf);
    let u = const_value(m, nf + 1);
    let n = domain_size(m);
    let mut domains = Vec::new();
    let mut i: usize = 0;
    while i < p.num_sorts {
        domains.push(n);
        i += 1;
    }
    let mut funs = Vec::new();
    let mut f: usize = 0;
    while f < nf {
        funs.push(tr_interp(p, m, f, t, u));
        f += 1;
    }
    SmtModel { domains, funs }
}

// The input range. `check_sat` answers `Unknown` for a problem outside the range of the
// specification (`smt_in_range` in `spec/QFUF_Spec.thy`): its size `smt_size` (the numbers of
// declared symbols, definitions and assertions, and the nodes of the terms, an application of a
// definition with parameters counting with the nodes of the body) is above 2^28. Within the
// range, every count of the translation and of the solver stays below 2^63. The size is computed
// with additions that saturate at 2^63: each returns the exact value if it is below 2^63, and
// 2^63 otherwise.

/// The bound at which the size computation saturates: 2^63.
fn cap() -> usize {
    9223372036854775808
}

/// The largest size of the range: 2^28.
fn max_size() -> usize {
    268435456
}

/// `a + b`, saturated at `cap()`.
fn sat_add(a: usize, b: usize) -> usize {
    if a >= cap() || b >= cap() - a {
        cap()
    } else {
        a + b
    }
}

/// The number of nodes of `t` (`smt_nodes`): an application of a definition with parameters
/// counts with the nodes of its body, which `dc` gives for each definition before the current
/// one.
fn node_count(p: &SmtProblem, dc: &Vec<usize>, t: &SmtTerm) -> usize {
    match t {
        SmtTerm::Fun(_, args) => sat_add(1, node_count_args(p, dc, args)),
        SmtTerm::Def(d, args) => {
            if p.defs[*d].params.len() == 0 {
                sat_add(1, node_count_args(p, dc, args))
            } else {
                sat_add(1, sat_add(node_count_args(p, dc, args), dc[*d]))
            }
        }
        SmtTerm::App(_, args) => sat_add(1, node_count_args(p, dc, args)),
        _ => 1,
    }
}

/// The sum of the node counts of the arguments `ts`.
fn node_count_args(p: &SmtProblem, dc: &Vec<usize>, ts: &Vec<SmtTerm>) -> usize {
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < ts.len() {
        n = sat_add(n, node_count(p, dc, &ts[i]));
        i += 1;
    }
    n
}

/// The size of `p` (`smt_size`): the numbers of declared symbols, definitions and assertions,
/// and the nodes of the bodies of the definitions without parameters and of the assertions.
fn input_size(p: &SmtProblem) -> usize {
    let mut dc = Vec::new();
    let mut n: usize = sat_add(sat_add(p.funs.len(), p.defs.len()), p.asserts.len());
    let mut d: usize = 0;
    while d < p.defs.len() {
        let c = node_count(p, &dc, &p.defs[d].body);
        if p.defs[d].params.len() == 0 {
            n = sat_add(n, c);
            dc.push(0);
        } else {
            dc.push(c);
        }
        d += 1;
    }
    let mut j: usize = 0;
    while j < p.asserts.len() {
        n = sat_add(n, node_count(p, &dc, &p.asserts[j]));
        j += 1;
    }
    n
}

/// The solver on a general problem: `Unknown` outside the fragment or outside the input range
/// (see above); otherwise the problem is translated into this solver's problem and solved.
pub fn check_sat(p: &SmtProblem) -> SmtAnswer {
    if !in_fragment(p) {
        return SmtAnswer::Unknown;
    }
    if input_size(p) > max_size() {
        return SmtAnswer::Unknown;
    }
    match solve(&tr_problem(p)) {
        Answer::Sat(m) => SmtAnswer::Sat(tr_model(p, &m)),
        Answer::Unsat => SmtAnswer::Unsat,
    }
}
