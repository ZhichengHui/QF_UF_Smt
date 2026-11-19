//! A vanilla SMT solver for QF_UF.
//!
//! Input: a CNF formula whose atoms are equalities between ground terms built from uninterpreted
//! function symbols (constants are 0-ary symbols) over one uninterpreted sort. Terms form a DAG:
//! term `i` is `terms[i].fun(terms[i].args[0], ...)` and every argument index is smaller than `i`.
//! Propositional variables can be encoded as equalities `p = true_const`.
//!
//! Algorithm: enumerate the truth assignments of the atoms by backtracking with unit propagation,
//! cutting a branch as soon as the assigned atoms falsify a clause or their equalities and
//! disequalities contradict each other by congruence closure. For an assignment that satisfies the clauses
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

/// Is some literal of `c` true under the partial assignment `t`, `f`?
fn some_lit_true(t: &[bool], f: &[bool], c: &Clause) -> bool {
    for i in 0..c.lits.len() {
        if (c.lits[i].pos && t[c.lits[i].atom]) || (!c.lits[i].pos && f[c.lits[i].atom]) {
            return true;
        }
    }
    false
}

/// The index of the first literal of `c` other than literal `skip` whose atom is unset under `t`,
/// `f`; the number of literals if there is none.
fn unset_lit(t: &[bool], f: &[bool], c: &Clause, skip: usize) -> usize {
    for i in 0..c.lits.len() {
        if i != skip && !t[c.lits[i].atom] && !f[c.lits[i].atom] {
            return i;
        }
    }
    c.lits.len()
}

/// Examines clause `c` under the partial assignment in which atom `x` is true if `t[x]`, false
/// if `f[x]`, and unset otherwise. Returns `Lit { atom: t.len(), pos: true }` if every literal of
/// `c` is false, the literal itself if exactly one literal is unset and all others are false, and
/// `Lit { atom: t.len(), pos: false }` otherwise. Literals are counted by position: a clause with
/// a repeated or complementary unset literal is not unit.
fn clause_unit(t: &[bool], f: &[bool], c: &Clause) -> Lit {
    if some_lit_true(t, f, c) {
        return Lit { atom: t.len(), pos: false };
    }
    let i = unset_lit(t, f, c, c.lits.len());
    if i == c.lits.len() {
        return Lit { atom: t.len(), pos: true };
    }
    if unset_lit(t, f, c, i) < c.lits.len() {
        return Lit { atom: t.len(), pos: false };
    }
    Lit { atom: c.lits[i].atom, pos: c.lits[i].pos }
}

/// The result of `clause_unit` for the first clause of `cs` that is falsified or unit under the
/// partial assignment `t`, `f`; `Lit { atom: t.len(), pos: false }` if there is none.
fn find_unit(cs: &[Clause], t: &[bool], f: &[bool]) -> Lit {
    for i in 0..cs.len() {
        let l = clause_unit(t, f, &cs[i]);
        if l.atom < t.len() || l.pos {
            return l;
        }
    }
    Lit { atom: t.len(), pos: false }
}

/// `find_unit` on the clauses of `p`, then, if none is falsified or unit, on the learned clauses `l`.
fn next_unit(p: &Problem, l: &[Clause], t: &[bool], f: &[bool]) -> Lit {
    let u = find_unit(&p.clauses, t, f);
    if u.atom < t.len() || u.pos {
        return u;
    }
    find_unit(l, t, f)
}

/// The first atom that is neither true nor false under `t`, `f`; `t.len()` if there is none.
fn first_unset(t: &[bool], f: &[bool]) -> usize {
    for i in 0..t.len() {
        if !t[i] && !f[i] {
            return i;
        }
    }
    t.len()
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

/// Merges the class of term `i` with that of every term `j < i` that is congruent to it but in
/// another class; returns whether it merged anything. Congruence is symmetric, so the rows of all
/// terms together cover every pair.
fn scan_row(p: &Problem, rep: &mut Vec<usize>, i: usize) -> bool {
    let mut changed = false;
    for j in 0..i {
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

/// Like `scan`, but skips the rows of constants (terms without arguments). A constant is congruent
/// only to the constants of its symbol, whatever the classes, so once `scan` has merged those, their
/// rows merge nothing more.
fn scan_apps(p: &Problem, rep: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..p.terms.len() {
        if p.terms[i].args.len() > 0 {
            if scan_row(p, rep, i) {
                changed = true;
            }
        }
    }
    changed
}

/// Merges congruent terms until no two terms of different classes are congruent: one round of
/// `scan`, which also merges the constants of each symbol, then rounds of `scan_apps`. Every round
/// that merges reduces the number of classes, so the `n + 1`-th round at the latest merges nothing.
fn close(p: &Problem, rep: &mut Vec<usize>) {
    scan(p, rep);
    for _round in 0..p.terms.len() + 1 {
        if !scan_apps(p, rep) {
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

/// Merges the two sides of every atom `j < m` with `a[j]`.
fn assert_eqs(p: &Problem, a: &[bool], m: usize, rep: &mut Vec<usize>) {
    for j in 0..m {
        if a[j] {
            merge(rep, p.atoms[j].lhs, p.atoms[j].rhs);
        }
    }
}

/// Are the two sides of every atom `j < m` without `a[j]` in different classes?
fn diseqs_ok(p: &Problem, a: &[bool], m: usize, rep: &[usize]) -> bool {
    for j in 0..m {
        if !a[j] && rep[p.atoms[j].lhs] == rep[p.atoms[j].rhs] {
            return false;
        }
    }
    true
}

/// The model of the closed partition `rep` if it keeps the sides of every unset atom apart.
/// `rep` is `&mut` although `finish` only reads it: then `theory_check` passes `rep` on without
/// reading it after `close`, which AutoCorrode's `crush` could not handle.
fn finish(p: &Problem, a: &[bool], rep: &mut Vec<usize>) -> Option<Model> {
    if diseqs_ok(p, a, p.atoms.len(), rep) { Some(build_model(p, rep)) } else { None }
}

/// The first atom `j` with `f[j]` whose two sides lie in one class of `rep`; `p.atoms.len()` if
/// there is none.
fn first_joined(p: &Problem, f: &[bool], rep: &[usize]) -> usize {
    for j in 0..p.atoms.len() {
        if f[j] && rep[p.atoms[j].lhs] == rep[p.atoms[j].rhs] {
            return j;
        }
    }
    p.atoms.len()
}

/// `first_joined` on the closed partition `rep`. `rep` is `&mut` for the reason given at `finish`.
fn false_joined(p: &Problem, f: &[bool], rep: &mut Vec<usize>) -> usize {
    first_joined(p, f, rep)
}

/// A model in which exactly the atoms `k` with `a[k]` hold, if there is one.
fn theory_check(p: &Problem, a: &[bool]) -> Option<Model> {
    let mut rep = init_rep(p.terms.len());
    assert_eqs(p, a, p.atoms.len(), &mut rep);
    close(p, &mut rep);
    finish(p, a, &mut rep)
}

/// Tries every completion of the partial assignment in which atom `x` is true if `t[x]`, false if
/// `f[x]`, and unset otherwise; `l` are clauses learned so far, which every interpretation
/// satisfies. First propagates: a clause of the problem or of `l` with all literals false cuts the
/// branch, and the unset literal of a clause whose other literals are all false is set true (one
/// literal per call). Without such clauses, cuts the branch when the true and false atoms
/// contradict each other by congruence closure, learning a clause that excludes the conflict;
/// otherwise sets the unset atoms that the closure implies (`cc_propagate`), and if there are none,
/// branches on the first unset atom. Returns the learned clauses with the result.
/// Every call sets one more atom, so the calls are nested at most `p.atoms.len() + 1` deep.
fn search(p: &Problem, l: Vec<Clause>, t: Vec<bool>, f: Vec<bool>) -> (Option<Model>, Vec<Clause>) {
    let u = next_unit(p, &l, &t, &f);
    if u.atom == t.len() && u.pos {
        return (None, l);
    }
    if u.atom < t.len() {
        let mut t1 = t.clone();
        let mut f1 = f.clone();
        if u.pos {
            t1[u.atom] = true;
        } else {
            f1[u.atom] = true;
        }
        return search(p, l, t1, f1);
    }
    let (c, t2, f2) = cc_propagate(p, &t, &f);
    if c < t.len() {
        return (None, learn(l, conflict_clause(&explain(p, &t, c), c)));
    }
    if differs(&t, &t2) || differs(&f, &f2) {
        return search(p, l, t2, f2);
    }
    let k = first_unset(&t, &f);
    if k == t.len() {
        if prop_holds(p, &t) {
            return (theory_check(p, &t), l);
        }
        return (None, l);
    }
    let mut t1 = t.clone();
    t1[k] = true;
    let (r, l1) = search(p, l, t1, f.clone());
    if r.is_some() {
        return (r, l1);
    }
    let mut f2 = f.clone();
    f2[k] = true;
    search(p, l1, t.clone(), f2)
}

pub fn solve(p: &Problem) -> Answer {
    let n = p.atoms.len();
    let (rep, xs, ys, ls) = root_log(p);
    let mut head = vec![cap(); sat_add(n, n)];
    let mut nxt = Vec::new();
    let mut wl = Vec::new();
    watch_new(p, &Vec::new(), &vec![0; n], &mut head, &mut nxt, &mut wl);
    let (r, _l, _j, _w) = cdcl(p, &sym_index(p), Vec::new(), vec![false; n], vec![false; n], &Vec::new(), vec![0; n], vec![0; n],
                               vec![0; n], (head, nxt, wl, vec![0; n]), &rep, &xs, &ys, &ls, 0, 0);
    match r {
        Some(m) => Answer::Sat(m),
        None => Answer::Unsat,
    }
}

// ---------------------------------------------------------------------------------------------
// The general problem structure: the interface to the SMT-LIB front end. These definitions are,
// word for word, those of the front end (`frontend/src/problem.rs`), except for the derived `Clone`
// and `PartialEq` (the equality elimination copies terms); see there for their meaning.

/// A sort.
#[derive(Clone, PartialEq)]
pub enum SmtSort {
    Bool,
    /// `(_ BitVec w)`, `w >= 1`.
    BitVec(usize),
    /// The uninterpreted sort with this number.
    Uninterpreted(usize),
}

/// The theory function symbols of Core and FixedSizeBitVectors/QF_BV (SMT-LIB 2.6).
#[derive(Clone)]
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
#[derive(Clone)]
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
#[derive(Clone)]
pub struct SmtFun {
    pub args: Vec<SmtSort>,
    pub ret: SmtSort,
}

/// A defined function: the sorts of its parameters and of its result, and its body.
#[derive(Clone)]
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
#[derive(Clone)]
pub enum SmtValue {
    Bool(bool),
    Bv(Vec<bool>),
    Elem(usize),
}

/// One point of a function table: the arguments and the value there.
#[derive(Clone)]
pub struct SmtEntry {
    pub args: Vec<SmtValue>,
    pub val: SmtValue,
}

/// The interpretation of a declared function symbol: at given arguments, the value of the first
/// entry with these arguments, and `default` if there is none (for a constant: the first entry, if
/// there is one).
#[derive(Clone)]
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
    let (a, cs, gs) = eliminate(p);
    let q = SmtProblem { num_sorts: p.num_sorts, funs: p.funs.clone(), defs: p.defs.clone(), asserts: a };
    match solve(&tr_problem(&q)) {
        Answer::Sat(m) => SmtAnswer::Sat(restore(tr_model(&q, &m), &cs, &gs)),
        Answer::Unsat => SmtAnswer::Unsat,
    }
}

// ---------------------------------------------------------------------------------------------
// Helpers of the search with mutable locals of the types `usize`, `Vec<Lit>` and `Vec<Clause>`.
// They stay at the end of the file: the generated locale numbers the types of mutable locals in
// the order of their first occurrence, and the specification fixes that order.

/// `scan_row` restricted to the terms `j` with `rows[j]`.
fn scan_row_in(p: &Problem, rows: &[bool], rep: &mut Vec<usize>, i: usize) -> bool {
    let mut changed = false;
    for j in 0..i {
        if rows[j] && rep[i] != rep[j] && congruent(p, rep, i, j) {
            merge(rep, i, j);
            changed = true;
        }
    }
    changed
}

/// One round of `scan_row_in` over the terms `i` with `rows[i]`; returns whether it merged anything.
fn scan_rows(p: &Problem, rows: &[bool], rep: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..p.terms.len() {
        if rows[i] && scan_row_in(p, rows, rep, i) {
            changed = true;
        }
    }
    changed
}

/// Merges congruent terms among those with `rows` until a round merges nothing (at most `n + 1`
/// rounds). The result need not be closed, but it only joins terms that the closure joins.
fn close_rows(p: &Problem, rows: &[bool], rep: &mut Vec<usize>) {
    for _round in 0..p.terms.len() + 1 {
        if !scan_rows(p, rows, rep) {
            return;
        }
    }
}

/// Are terms `a` and `b` in one class of `rep`?
fn same_class(rep: &[usize], a: usize, b: usize) -> bool {
    rep[a] == rep[b]
}

/// Whether the partition `rep` joins the two sides of atom `k`.
/// `rep` is `&mut` for the reason given at `finish`.
fn joined(p: &Problem, k: usize, rep: &mut Vec<usize>) -> bool {
    same_class(rep, p.atoms[k].lhs, p.atoms[k].rhs)
}

/// Whether the equalities of the atoms `j` with `e[j]`, merged by `close_rows`, join the two
/// sides of atom `k`; if so, so does their congruence closure.
fn rows_join(p: &Problem, e: &[bool], rows: &[bool], k: usize) -> bool {
    let mut rep = init_rep(p.terms.len());
    assert_eqs(p, e, p.atoms.len(), &mut rep);
    close_rows(p, rows, &mut rep);
    joined(p, k, &mut rep)
}

/// `v[i]`, or `d` if `i` is out of bounds.
fn get_or(v: &[usize], i: usize, d: usize) -> usize {
    if i < v.len() { v[i] } else { d }
}

/// Sets `v[i]` to `x` if `i` is in bounds.
fn set_at(v: &mut Vec<usize>, i: usize, x: usize) {
    if i < v.len() {
        v[i] = x;
    }
}

/// Sets `v[i]` if `i` is in bounds.
fn set_true(v: &mut Vec<bool>, i: usize) {
    if i < v.len() {
        v[i] = true;
    }
}

/// Merges the classes of the two sides of every atom `j` with `t[j]` that `rep` keeps apart, and
/// logs each merge as the edge `(xs, ys)` with label `ls` = `j`.
fn log_atoms(p: &Problem, t: &[bool], rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>) {
    for j in 0..p.atoms.len() {
        if t[j] && rep[p.atoms[j].lhs] != rep[p.atoms[j].rhs] {
            merge(rep, p.atoms[j].lhs, p.atoms[j].rhs);
            xs.push(p.atoms[j].lhs);
            ys.push(p.atoms[j].rhs);
            ls.push(j);
        }
    }
}

/// `scan_row` that logs each merge of terms `i` and `j` as the edge `(i, j)` with label
/// `p.atoms.len()`.
fn log_row(p: &Problem, rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>, i: usize) -> bool {
    let mut changed = false;
    for j in 0..i {
        if rep[i] != rep[j] && congruent(p, rep, i, j) {
            merge(rep, i, j);
            xs.push(i);
            ys.push(j);
            ls.push(p.atoms.len());
            changed = true;
        }
    }
    changed
}

/// One round of `log_row` over all terms; returns whether it merged anything.
fn log_scan(p: &Problem, rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..p.terms.len() {
        if log_row(p, rep, xs, ys, ls, i) {
            changed = true;
        }
    }
    changed
}

/// `close` with `log_scan`.
fn log_close(p: &Problem, rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>) {
    for _round in 0..p.terms.len() + 1 {
        if !log_scan(p, rep, xs, ys, ls) {
            return;
        }
    }
}

/// The merges of a congruence closure of the atoms set in `t`, in order, as edges `(xs[i], ys[i])`
/// with label `ls[i]`: an atom `j < p.atoms.len()` whose sides are `xs[i]` and `ys[i]`, or
/// `p.atoms.len()` for a merge of the congruent terms `xs[i]` and `ys[i]`. Every edge joins two
/// classes, so the edges form a forest, and the arguments of the two terms of a congruence edge
/// are joined by earlier edges.
fn merge_log(p: &Problem, t: &[bool]) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut rep = init_rep(p.terms.len());
    let mut xs = Vec::new();
    let mut ys = Vec::new();
    let mut ls = Vec::new();
    log_atoms(p, t, &mut rep, &mut xs, &mut ys, &mut ls);
    log_close(p, &mut rep, &mut xs, &mut ys, &mut ls);
    (xs, ys, ls)
}

/// One round of a breadth-first search over the `n` terms along the edges `(xs[i], ys[i])`: a
/// reached term `y` has a predecessor `pv[y] < n` reached before it, and the index `pe[y]` of the
/// edge. Returns whether it reached a new term.
fn bfs_round(n: usize, xs: &[usize], ys: &[usize], pv: &mut Vec<usize>, pe: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..xs.len() {
        let x = xs[i];
        let y = get_or(ys, i, n);
        if x < pv.len() && y < pv.len() {
            if pv[x] < n && pv[y] == n {
                pv[y] = x;
                set_at(pe, y, i);
                changed = true;
            } else if pv[y] < n && pv[x] == n {
                pv[x] = y;
                set_at(pe, x, i);
                changed = true;
            }
        }
    }
    changed
}

/// `bfs_round` until term `b` is reached or a round reaches nothing (at most `n` rounds).
fn bfs_rounds(n: usize, xs: &[usize], ys: &[usize], b: usize, pv: &mut Vec<usize>, pe: &mut Vec<usize>) {
    for _round in 0..n {
        if get_or(pv, b, n) < n || !bfs_round(n, xs, ys, pv, pe) {
            return;
        }
    }
}

/// Breadth-first search from term `a` towards term `b` (see `bfs_round`); returns `pv` and `pe`.
fn bfs(n: usize, xs: &[usize], ys: &[usize], a: usize, b: usize) -> (Vec<usize>, Vec<usize>) {
    let mut pv = vec![n; n];
    let mut pe = vec![0; n];
    set_at(&mut pv, a, a);
    bfs_rounds(n, xs, ys, b, &mut pv, &mut pe);
    (pv, pe)
}

/// Appends the pairs of corresponding arguments of terms `u` and `v` to `qa`, `qb`.
fn push_args(p: &Problem, u: usize, v: usize, qa: &mut Vec<usize>, qb: &mut Vec<usize>) {
    if u < p.terms.len() && v < p.terms.len() {
        for r in 0..p.terms[u].args.len() {
            if r < p.terms[v].args.len() {
                qa.push(p.terms[u].args[r]);
                qb.push(p.terms[v].args[r]);
            }
        }
    }
}

/// Walks the path of the search `pv`, `pe` back from term `b` to term `a`. Each edge not `used`
/// before: an atom edge sets its atom in `e`; a congruence edge sets its two terms in `rows` and
/// appends their argument pairs to `qa`, `qb`.
fn walk(p: &Problem, xs: &[usize], ys: &[usize], ls: &[usize], pv: &[usize], pe: &[usize], a: usize, b: usize,
        e: &mut Vec<bool>, rows: &mut Vec<bool>, used: &mut Vec<bool>, qa: &mut Vec<usize>, qb: &mut Vec<usize>) {
    let n = p.terms.len();
    let m = p.atoms.len();
    let mut x = b;
    for _step in 0..n {
        if x != a && get_or(pv, x, n) < n {
            let g = get_or(pe, x, used.len());
            if g < used.len() && !used[g] {
                used[g] = true;
                let l = get_or(ls, g, m);
                if l < m {
                    set_true(e, l);
                } else {
                    let u = get_or(xs, g, n);
                    let v = get_or(ys, g, n);
                    set_true(rows, u);
                    set_true(rows, v);
                    push_args(p, u, v, qa, qb);
                }
            }
            x = get_or(pv, x, n);
        }
    }
}

/// A set of atoms whose equalities, closed under congruence, join the two sides of atom `k`, read
/// off the merge log `xs`, `ys`, `ls` (see `merge_log`): the atom edges on the path between the two
/// sides in the forest, and recursively those that explain the argument pairs of its congruence
/// edges. Returns the atoms and the terms of the congruence edges used.
fn path_explain_log(p: &Problem, xs: &[usize], ys: &[usize], ls: &[usize], k: usize) -> (Vec<bool>, Vec<bool>) {
    let n = p.terms.len();
    let mut e = vec![false; p.atoms.len()];
    let mut rows = vec![false; n];
    let mut used = vec![false; xs.len()];
    let mut qa = Vec::new();
    let mut qb = Vec::new();
    qa.push(p.atoms[k].lhs);
    qb.push(p.atoms[k].rhs);
    for i in 0..n + n + 1 {
        let a = get_or(&qa, i, n);
        let b = get_or(&qb, i, n);
        if a < n && b < n && a != b {
            let (pv, pe) = bfs(n, xs, ys, a, b);
            walk(p, xs, ys, ls, &pv, &pe, a, b, &mut e, &mut rows, &mut used, &mut qa, &mut qb);
        }
    }
    (e, rows)
}

/// `path_explain_log` on `merge_log` of the atoms set in `t`.
fn path_explain(p: &Problem, t: &[bool], k: usize) -> (Vec<bool>, Vec<bool>) {
    let (xs, ys, ls) = merge_log(p, t);
    path_explain_log(p, &xs, &ys, &ls, k)
}

/// A subset of the atoms set in `t` whose equalities, closed under congruence, join the two sides
/// of atom `k`, if those of `t` do: `path_explain`, if `rows_join` confirms it, and `t` itself
/// otherwise.
fn explain(p: &Problem, t: &[bool], k: usize) -> Vec<bool> {
    let (e, rows) = path_explain(p, t, k);
    if rows_join(p, &e, &rows, k) {
        return e;
    }
    t.to_vec()
}

/// `explain` with `path_explain_log` on the merge log `xs`, `ys`, `ls` of a closure of the atoms
/// set in `t`.
fn explain_log(p: &Problem, t: &[bool], xs: &[usize], ys: &[usize], ls: &[usize], k: usize) -> Vec<bool> {
    let (e, rows) = path_explain_log(p, xs, ys, ls, k);
    if rows_join(p, &e, &rows, k) {
        return e;
    }
    t.to_vec()
}

/// The clause "some atom set in `e` is false, or atom `k` is true".
fn conflict_clause(e: &[bool], k: usize) -> Clause {
    let mut lits = Vec::new();
    lits.push(Lit { atom: k, pos: true });
    for j in 0..e.len() {
        if e[j] {
            lits.push(Lit { atom: j, pos: false });
        }
    }
    Clause { lits: lits }
}

/// `l` with the clause `c` appended.
fn learn(l: Vec<Clause>, c: Clause) -> Vec<Clause> {
    let mut l1 = l;
    l1.push(c);
    l1
}

/// The atoms set true in `t`, and every atom unset under `t`, `f` whose two sides lie in one class
/// of `rep`.
fn joined_unset(p: &Problem, t: &[bool], f: &[bool], rep: &[usize]) -> Vec<bool> {
    let mut t1 = t.to_vec();
    for j in 0..p.atoms.len() {
        if !t[j] && !f[j] && rep[p.atoms[j].lhs] == rep[p.atoms[j].rhs] {
            t1[j] = true;
        }
    }
    t1
}

/// Does some atom set in `t1` differ from `t`?
fn differs(t: &[bool], t1: &[bool]) -> bool {
    for i in 0..t.len() {
        if t[i] != t1[i] {
            return true;
        }
    }
    false
}

/// The classes of `rep` of the two sides of every atom `b` with `f[b]`, as pairs `(us[i], vs[i])`.
fn false_pairs(p: &Problem, f: &[bool], rep: &[usize]) -> (Vec<usize>, Vec<usize>) {
    let mut us = Vec::new();
    let mut vs = Vec::new();
    for b in 0..p.atoms.len() {
        if f[b] {
            us.push(rep[p.atoms[b].lhs]);
            vs.push(rep[p.atoms[b].rhs]);
        }
    }
    (us, vs)
}

/// Is `(x, y)` or `(y, x)` one of the pairs `(us[i], vs[i])`? `vs` is at least as long as `us`.
fn has_pair(us: &[usize], vs: &[usize], x: usize, y: usize) -> bool {
    for i in 0..us.len() {
        if (us[i] == x && vs[i] == y) || (us[i] == y && vs[i] == x) {
            return true;
        }
    }
    false
}

/// The classes of `rep` of the two sides of every atom `b` with `f[b]`, as flags over the terms
/// (representatives out of bounds are left out).
fn false_sides(p: &Problem, f: &[bool], rep: &[usize]) -> Vec<bool> {
    let mut mk = vec![false; p.terms.len()];
    for b in 0..p.atoms.len() {
        if f[b] {
            set_true(&mut mk, rep[p.atoms[b].lhs]);
            set_true(&mut mk, rep[p.atoms[b].rhs]);
        }
    }
    mk
}

/// `v[i]`, or false if `i` is out of bounds.
fn flag_at(v: &[bool], i: usize) -> bool {
    i < v.len() && v[i]
}

/// The atoms set false in `f`, and every atom unset under `t`, `f` whose two sides lie in classes
/// of `rep` that the two sides of an atom set false lie in. `false_sides` filters the atoms before
/// the pairs of `false_pairs` are searched.
fn separated_unset(p: &Problem, t: &[bool], f: &[bool], rep: &[usize]) -> Vec<bool> {
    let (us, vs) = false_pairs(p, f, rep);
    let mk = false_sides(p, f, rep);
    let mut f1 = f.to_vec();
    for j in 0..p.atoms.len() {
        let x = rep[p.atoms[j].lhs];
        let y = rep[p.atoms[j].rhs];
        if !t[j] && !f[j] && x != y && flag_at(&mk, x) && flag_at(&mk, y) && has_pair(&us, &vs, x, y) {
            f1[j] = true;
        }
    }
    f1
}

/// `joined_unset` and `separated_unset` on the closed partition `rep`: the atoms set true and false
/// after theory propagation. `rep` is `&mut` for the reason given at `finish`.
fn implied(p: &Problem, t: &[bool], f: &[bool], rep: &mut Vec<usize>) -> (Vec<bool>, Vec<bool>) {
    let t1 = joined_unset(p, t, f, rep);
    let f1 = separated_unset(p, t, f, rep);
    (t1, f1)
}

/// The closure of the equalities of the atoms with `t[j]`: the first atom `c` with `f[c]` whose two
/// sides it joins (`p.atoms.len()` if there is none), and the result of `implied` (theory
/// propagation).
fn cc_propagate(p: &Problem, t: &[bool], f: &[bool]) -> (usize, Vec<bool>, Vec<bool>) {
    let mut rep = init_rep(p.terms.len());
    assert_eqs(p, t, p.atoms.len(), &mut rep);
    close(p, &mut rep);
    let c = false_joined(p, f, &mut rep);
    let (t1, f1) = implied(p, t, f, &mut rep);
    (c, t1, f1)
}

// ---------------------------------------------------------------------------------------------
// Incremental closure (`cc_step`).
//
// `cdcl` carries a partition `rep` and its merge log `xs`, `ys`, `ls` (see `merge_log`) down its
// recursion: the closure of the atoms set true when it was computed. Each class of `rep` lies in
// the congruence closure of the atoms set true, which stays so when more atoms become true.
// `cc_step` extends both: it merges the sides of the atoms set true since, and then rescans only
// the terms an argument of which changed its class: two terms that become congruent have an
// argument pair whose classes were merged, and a merge changes the representative of one of the
// two classes. Every merge joins two classes, so the log stays a forest in which the path between
// two terms does not change once they are joined; an explanation read off the log of a later
// node is the one of the node that joined them. Soundness rests only on the check of every
// explanation by `rows_join`; that the partition is closed and the log is a forest only matters
// for the speed and the quality of the explanations.

/// Does an argument of term `i` have another representative in `rep` than in `old`?
fn arg_moved(p: &Problem, old: &[usize], rep: &[usize], i: usize) -> bool {
    for k in 0..p.terms[i].args.len() {
        if old[p.terms[i].args[k]] != rep[p.terms[i].args[k]] {
            return true;
        }
    }
    false
}

/// The terms with an argument that has another representative in `rep` than in `old`.
fn moved_rows(p: &Problem, old: &[usize], rep: &[usize]) -> Vec<bool> {
    let mut rows = vec![false; p.terms.len()];
    for i in 0..p.terms.len() {
        if arg_moved(p, old, rep, i) {
            rows[i] = true;
        }
    }
    rows
}

/// The terms grouped by function symbol: `perm` lists the terms of symbol 0, then those of
/// symbol 1, and so on, and the terms of symbol `g` are `perm[start[g]..start[g + 1]]`. Only terms
/// of the same symbol can be congruent, so `log_col` looks only at those; the index is not needed
/// for soundness, which rests on `congruent` alone.
fn sym_index(p: &Problem) -> (Vec<usize>, Vec<usize>) {
    let n = p.terms.len();
    let mut m = 0;
    for i in 0..n {
        if p.terms[i].fun >= m {
            m = sat_add(p.terms[i].fun, 1);
        }
    }
    let mut start = vec![0; sat_add(m, 1)];
    for i in 0..n {
        let g = sat_add(p.terms[i].fun, 1);
        let x = sat_add(get_or(&start, g, 0), 1);
        set_at(&mut start, g, x);
    }
    for g in 0..m {
        let x = sat_add(get_or(&start, g, 0), get_or(&start, sat_add(g, 1), 0));
        set_at(&mut start, sat_add(g, 1), x);
    }
    let mut pos = start.clone();
    let mut perm = vec![0; n];
    for i in 0..n {
        let g = p.terms[i].fun;
        let k = get_or(&pos, g, n);
        set_at(&mut perm, k, i);
        set_at(&mut pos, g, sat_add(k, 1));
    }
    (perm, start)
}

/// Merges the class of term `i` with that of every term `j` of its symbol (`sym_index` `perm`,
/// `start`) that is congruent to it but in another class, and logs each merge as the edge
/// `(i, j)` with label `p.atoms.len()`; returns whether it merged anything.
fn log_col(p: &Problem, perm: &[usize], start: &[usize], rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>,
           ls: &mut Vec<usize>, i: usize) -> bool {
    let g = p.terms[i].fun;
    let mut changed = false;
    for k in get_or(start, g, 0)..get_or(start, sat_add(g, 1), 0) {
        let j = get_or(perm, k, i);
        if j < p.terms.len() && rep[i] != rep[j] && congruent(p, rep, i, j) {
            merge(rep, i, j);
            xs.push(i);
            ys.push(j);
            ls.push(p.atoms.len());
            changed = true;
        }
    }
    changed
}

/// `log_col` on every term `i` with `rows[i]`; returns whether it merged anything.
fn log_moved(p: &Problem, perm: &[usize], start: &[usize], rows: &[bool], rep: &mut Vec<usize>, xs: &mut Vec<usize>,
             ys: &mut Vec<usize>, ls: &mut Vec<usize>) -> bool {
    let mut changed = false;
    for i in 0..p.terms.len() {
        if rows[i] && log_col(p, perm, start, rep, xs, ys, ls, i) {
            changed = true;
        }
    }
    changed
}

/// Copies `rep` into `old`.
fn copy_into(old: &mut Vec<usize>, rep: &[usize]) {
    for i in 0..old.len() {
        if i < rep.len() {
            old[i] = rep[i];
        }
    }
}

/// One round of the incremental closure: `log_moved` on the terms with an argument whose
/// representative changed since `old`, after copying `rep` into `old`; returns whether it merged
/// anything.
fn round_moved(p: &Problem, perm: &[usize], start: &[usize], old: &mut Vec<usize>, rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>) -> bool {
    let rows = moved_rows(p, old, rep);
    copy_into(old, rep);
    log_moved(p, perm, start, &rows, rep, xs, ys, ls)
}

/// Rounds of `round_moved` until one merges nothing (at most `n + 1` rounds). If `old` was
/// closed, so is the result.
fn close_moved(p: &Problem, perm: &[usize], start: &[usize], old: &mut Vec<usize>, rep: &mut Vec<usize>, xs: &mut Vec<usize>, ys: &mut Vec<usize>, ls: &mut Vec<usize>) {
    for _round in 0..p.terms.len() + 1 {
        if !round_moved(p, perm, start, old, rep, xs, ys, ls) {
            return;
        }
    }
}

/// `cc_propagate` on the partition `rep0` with log `xs0`, `ys0`, `ls0`, extended by the atoms set
/// true in `t` and closed by `close_moved`; also returns the extended partition and log.
fn cc_step(p: &Problem, perm: &[usize], start: &[usize], t: &[bool], f: &[bool], rep0: &[usize], xs0: &[usize], ys0: &[usize], ls0: &[usize])
           -> (usize, Vec<bool>, Vec<bool>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut old = rep0.to_vec();
    let mut rep = rep0.to_vec();
    let mut xs = xs0.to_vec();
    let mut ys = ys0.to_vec();
    let mut ls = ls0.to_vec();
    log_atoms(p, t, &mut rep, &mut xs, &mut ys, &mut ls);
    close_moved(p, perm, start, &mut old, &mut rep, &mut xs, &mut ys, &mut ls);
    let c = false_joined(p, f, &mut rep);
    let (t1, f1) = implied(p, t, f, &mut rep);
    (c, t1, f1, rep, xs, ys, ls)
}

/// The closure of no equalities and its merge log: where `cdcl` starts. `close` and `merge_log`
/// compute the same partition, the congruence closure of no equalities.
fn root_log(p: &Problem) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut rep = init_rep(p.terms.len());
    close(p, &mut rep);
    let (xs, ys, ls) = merge_log(p, &vec![false; p.atoms.len()]);
    (rep, xs, ys, ls)
}

// ---------------------------------------------------------------------------------------------
// Conflict analysis and backjumping (`cdcl`).
//
// For every atom `x` it sets, the search records the decision level `lv[x]`, a time stamp `ts[x]`
// (increasing along a path of the search) and a reason `rs[x]`: 0 for a decision or an atom set
// without a reason, 1 for an atom whose two sides the closure joined, and `2 + i` for clause `i`
// of the problem's clauses followed by the learned ones. The records only guide the analysis:
// every clause it derives is a resolvent of clauses that hold in every model, whatever they say.
// The analysis keeps its clause as two lists of flags over the atoms, `cp` (positive literals)
// and `cn` (negative literals).

/// `v` with `v[x]` set to `y` if `x` is in bounds.
fn note(v: &[usize], x: usize, y: usize) -> Vec<usize> {
    let mut w = v.to_vec();
    set_at(&mut w, x, y);
    w
}

/// `v` with `v[j]` set to `y` for every atom `j` set in `t1` or `f1` but in neither `t` nor `f`.
fn note_new(t: &[bool], f: &[bool], t1: &[bool], f1: &[bool], v: &[usize], y: usize) -> Vec<usize> {
    let mut w = v.to_vec();
    for j in 0..t.len() {
        if j < f.len() && j < t1.len() && j < f1.len() && !t[j] && !f[j] && (t1[j] || f1[j]) {
            set_at(&mut w, j, y);
        }
    }
    w
}

/// `v` with `v[j]` set to `y` for every atom `j` set in `t1` but not in `t`.
fn note_true(t: &[bool], t1: &[bool], v: &[usize], y: usize) -> Vec<usize> {
    let mut w = v.to_vec();
    for j in 0..t.len() {
        if j < t1.len() && !t[j] && t1[j] {
            set_at(&mut w, j, y);
        }
    }
    w
}

/// The clause "atom `x` or not atom `x`".
fn tautology(x: usize) -> Clause {
    let mut lits = Vec::new();
    lits.push(Lit { atom: x, pos: true });
    lits.push(Lit { atom: x, pos: false });
    Clause { lits: lits }
}

/// A copy of clause `c`.
fn copy_clause(c: &Clause) -> Clause {
    let mut lits = Vec::new();
    for i in 0..c.lits.len() {
        lits.push(Lit { atom: c.lits[i].atom, pos: c.lits[i].pos });
    }
    Clause { lits: lits }
}

/// Clause `r - 2` of the problem's clauses followed by `l`; the tautology on `x` if there is none.
fn indexed_clause(p: &Problem, l: &[Clause], r: usize, x: usize) -> Clause {
    if r >= 2 && r - 2 < p.clauses.len() {
        return copy_clause(&p.clauses[r - 2]);
    }
    if r >= 2 && r - 2 - p.clauses.len() < l.len() {
        return copy_clause(&l[r - 2 - p.clauses.len()]);
    }
    tautology(x)
}

/// Why the closure joined the two sides of atom `x`: the clause "some atom of `path_explain_log` on
/// the merge log `xs`, `ys`, `ls` is false, or `x` is true", if `rows_join` confirms those atoms,
/// and the tautology on `x` otherwise. On the log of the search path (see `cc_step`) these atoms
/// were set true before `x`.
fn theory_reason(p: &Problem, xs: &[usize], ys: &[usize], ls: &[usize], x: usize) -> Clause {
    let (e, rows) = path_explain_log(p, xs, ys, ls, x);
    if rows_join(p, &e, &rows, x) {
        return conflict_clause(&e, x);
    }
    tautology(x)
}

/// The reason of atom `x` as a clause; the tautology on `x` if it has none.
fn reason(p: &Problem, l: &[Clause], xs: &[usize], ys: &[usize], ls: &[usize], rs: &[usize], x: usize) -> Clause {
    let r = get_or(rs, x, 0);
    if r == 1 {
        return theory_reason(p, xs, ys, ls, x);
    }
    indexed_clause(p, l, r, x)
}

/// The clause `cp`, `cn` with the literals of `c` added, except the literal of atom `x` with sign
/// `pos` (and literals of atoms out of bounds).
fn add_lits(c: &Clause, x: usize, pos: bool, cp: &[bool], cn: &[bool]) -> (Vec<bool>, Vec<bool>) {
    let mut cp1 = cp.to_vec();
    let mut cn1 = cn.to_vec();
    for i in 0..c.lits.len() {
        let a = c.lits[i].atom;
        if !(a == x && c.lits[i].pos == pos) && a < cp1.len() && a < cn1.len() {
            if c.lits[i].pos {
                cp1[a] = true;
            } else {
                cn1[a] = true;
            }
        }
    }
    (cp1, cn1)
}

/// Is atom `j` in the clause `cp`, `cn` at level `d`?
fn at_level(lv: &[usize], cp: &[bool], cn: &[bool], d: usize, j: usize) -> bool {
    (cp[j] || (j < cn.len() && cn[j])) && get_or(lv, j, d) == d
}

/// The atom of the clause `cp`, `cn` at level `d` with the highest time stamp; `cp.len()` if
/// there is none.
fn last_at(lv: &[usize], ts: &[usize], cp: &[bool], cn: &[bool], d: usize) -> usize {
    let mut x = cp.len();
    for j in 0..cp.len() {
        if at_level(lv, cp, cn, d, j) && (x == cp.len() || get_or(ts, j, 0) > get_or(ts, x, 0)) {
            x = j;
        }
    }
    x
}

/// Is an atom other than `x` in the clause `cp`, `cn` at level `d`?
fn other_at(lv: &[usize], cp: &[bool], cn: &[bool], d: usize, x: usize) -> bool {
    for j in 0..cp.len() {
        if j != x && at_level(lv, cp, cn, d, j) {
            return true;
        }
    }
    false
}

/// The highest level below `d` of an atom of the clause `cp`, `cn`; 0 if there is none.
fn level_below(lv: &[usize], cp: &[bool], cn: &[bool], d: usize) -> usize {
    let mut b = 0;
    for j in 0..cp.len() {
        let v = get_or(lv, j, d);
        if (cp[j] || (j < cn.len() && cn[j])) && v < d && v > b {
            b = v;
        }
    }
    b
}

/// One step of the analysis: if the clause `cp`, `cn` has two atoms or more at level `d`, resolves
/// it with the reason of the last of them, `x`: drops the literal of `x` that the assignment makes
/// false and adds the literals of the reason other than the one of `x` it makes true. Returns
/// whether it resolved, and the clause.
fn resolve_step(p: &Problem, l: &[Clause], t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize],
                xs: &[usize], ys: &[usize], ls: &[usize], d: usize, cp: &[bool], cn: &[bool]) -> (bool, Vec<bool>, Vec<bool>) {
    let x = last_at(lv, ts, cp, cn, d);
    if x >= cp.len() || x >= cn.len() || x >= t.len() || get_or(rs, x, 0) == 0 || !other_at(lv, cp, cn, d, x) {
        return (false, cp.to_vec(), cn.to_vec());
    }
    let r = reason(p, l, xs, ys, ls, rs, x);
    let mut cp1 = cp.to_vec();
    let mut cn1 = cn.to_vec();
    if t[x] {
        cn1[x] = false;
    } else {
        cp1[x] = false;
    }
    let (cp2, cn2) = add_lits(&r, x, t[x], &cp1, &cn1);
    (true, cp2, cn2)
}

/// The clause with the positive literals of the atoms `j` with `cp[j]` and the negative ones of
/// those with `cn[j]`.
fn lits_clause(cp: &[bool], cn: &[bool]) -> Clause {
    let mut lits = Vec::new();
    for j in 0..cp.len() {
        if cp[j] {
            lits.push(Lit { atom: j, pos: true });
        }
        if j < cn.len() && cn[j] {
            lits.push(Lit { atom: j, pos: false });
        }
    }
    Clause { lits: lits }
}

/// Conflict analysis of the clause `c`, false under the assignment `t`: resolves it with the
/// reasons of its atoms at level `d`, latest first, until one atom at level `d` is left (the first
/// unique implication point) or an atom without a reason is reached (at most `t.len() + 1` steps).
/// Returns the clause, whether it has exactly one atom at level `d`, and the highest level below
/// `d` of its atoms.
fn analyze(p: &Problem, l: &[Clause], t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize],
           xs: &[usize], ys: &[usize], ls: &[usize], d: usize, c: &Clause)
           -> (Clause, bool, usize) {
    let (cp0, cn0) = add_lits(c, t.len(), true, &vec![false; t.len()], &vec![false; t.len()]);
    let mut cp = cp0;
    let mut cn = cn0;
    let mut go = true;
    for _step in 0..t.len() + 1 {
        if go {
            let (g, cp1, cn1) = resolve_step(p, l, t, lv, ts, rs, xs, ys, ls, d, &cp, &cn);
            go = g;
            cp = cp1;
            cn = cn1;
        }
    }
    let x = last_at(lv, ts, &cp, &cn, d);
    let one = x < cp.len() && !other_at(lv, &cp, &cn, d, x);
    let b = level_below(lv, &cp, &cn, d);
    (lits_clause(&cp, &cn), one, b)
}

/// A conflict on clause `c` at level `d`: learns the clause of `analyze`. If it has exactly one
/// atom at level `d > 0`, returns a jump to the highest level `b < d` of its other atoms, where it
/// propagates; otherwise returns level `d` (the branch is refuted).
fn on_conflict(p: &Problem, l: Vec<Clause>, t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize],
               xs: &[usize], ys: &[usize], ls: &[usize], d: usize, c: &Clause) -> (Option<Model>, Vec<Clause>, usize) {
    let (a, one, b) = analyze(p, &l, t, lv, ts, rs, xs, ys, ls, d, c);
    let l1 = learn(l, a);
    if one && b < d {
        return (None, l1, b);
    }
    (None, l1, d)
}

// ---------------------------------------------------------------------------------------------
// Watched literals (`cdcl`).
//
// Clause `c` of the problem's clauses followed by the learned ones has two watch slots, `2c` and
// `2c + 1`; `wl[w]` is the position in the clause of the literal that slot `w` watches. The slots
// that watch the literal with code `lit_code` form a list: `head[code]` is its first slot,
// `nxt[w]` the slot after `w`, and `cap()` ends it. When a literal becomes false, `watch_visit`
// moves each slot that watches it to a literal of its clause that is not false, if there is one;
// the clauses where there is none, unless the other watched literal is true, are unit or false,
// and `units_at` checks them with `clause_unit`. The lists only choose the clauses to check:
// every atom is set, and every conflict found, by `clause_unit` on the clause itself, so no
// property of the lists is needed for soundness, only for finding every unit clause.

/// The code of literal `l`: `2 * atom + 1` if it is positive, `2 * atom` otherwise.
fn lit_code(l: &Lit) -> usize {
    if l.pos {
        sat_add(sat_add(l.atom, l.atom), 1)
    } else {
        sat_add(l.atom, l.atom)
    }
}

/// Is the literal `l` false under `t`, `f`? (False for an atom out of bounds.)
fn lit_false_at(t: &[bool], f: &[bool], l: &Lit) -> bool {
    if l.pos {
        l.atom < f.len() && f[l.atom]
    } else {
        l.atom < t.len() && t[l.atom]
    }
}

/// Is the literal `l` true under `t`, `f`? (False for an atom out of bounds.)
fn lit_true_at(t: &[bool], f: &[bool], l: &Lit) -> bool {
    if l.pos {
        l.atom < t.len() && t[l.atom]
    } else {
        l.atom < f.len() && f[l.atom]
    }
}

/// Where the slot of clause `c` that watches position `a` goes, the other slot watching position
/// `b`: `(0, cap(), true)` if the literal at `b` is true; otherwise `(k, lit_code, false)` for the
/// first position `k` other than `a` and `b` whose literal is not false, and `(0, cap(), false)`
/// if there is none.
fn watch_move(c: &Clause, t: &[bool], f: &[bool], a: usize, b: usize) -> (usize, usize, bool) {
    if b < c.lits.len() && lit_true_at(t, f, &c.lits[b]) {
        return (0, cap(), true);
    }
    for k in 0..c.lits.len() {
        if k != a && k != b && !lit_false_at(t, f, &c.lits[k]) {
            return (k, lit_code(&c.lits[k]), false);
        }
    }
    (0, cap(), false)
}

/// `watch_move` on clause `c` of the problem's clauses followed by `l`; `(0, cap(), true)` if
/// there is none.
fn watch_move_at(p: &Problem, l: &[Clause], c: usize, t: &[bool], f: &[bool], a: usize, b: usize) -> (usize, usize, bool) {
    if c < p.clauses.len() {
        return watch_move(&p.clauses[c], t, f, a, b);
    }
    if c - p.clauses.len() < l.len() {
        return watch_move(&l[c - p.clauses.len()], t, f, a, b);
    }
    (0, cap(), true)
}

/// Visits the slots that watch the literal with code `lc`, false under `t`, `f`: moves each one it
/// can to another literal (`watch_move_at`), and returns the clauses of the others, unless their
/// other watched literal is true.
fn watch_visit(p: &Problem, l: &[Clause], lc: usize, t: &[bool], f: &[bool], head: &mut Vec<usize>, nxt: &mut Vec<usize>,
               wl: &mut Vec<usize>) -> Vec<usize> {
    let mut cands = Vec::new();
    let mut prev = cap();
    let mut w = get_or(head, lc, cap());
    let n = nxt.len();
    for _k in 0..n {
        if w >= n {
            break;
        }
        let w1 = get_or(nxt, w, cap());
        let o = if w % 2 == 0 { w + 1 } else { w - 1 };
        let (k, code, sat) = watch_move_at(p, l, w / 2, t, f, get_or(wl, w, 0), get_or(wl, o, 0));
        if sat {
            prev = w;
        } else if code < head.len() && code != lc {
            set_at(wl, w, k);
            if prev < n {
                set_at(nxt, prev, w1);
            } else {
                set_at(head, lc, w1);
            }
            set_at(nxt, w, get_or(head, code, cap()));
            set_at(head, code, w);
        } else {
            cands.push(w / 2);
            prev = w;
        }
        w = w1;
    }
    cands
}

/// `clause_unit` on clause `c` of the problem's clauses followed by `l`; no unit if there is none.
fn clause_unit_at(p: &Problem, l: &[Clause], c: usize, t: &[bool], f: &[bool]) -> Lit {
    if c < p.clauses.len() {
        return clause_unit(t, f, &p.clauses[c]);
    }
    if c - p.clauses.len() < l.len() {
        return clause_unit(t, f, &l[c - p.clauses.len()]);
    }
    Lit { atom: t.len(), pos: false }
}

/// Checks the clauses `cs` (indices into the problem's clauses followed by `l`) in turn under the
/// assignment `t`, `f` as extended so far: sets the literal of a unit clause `c`, records level
/// `d`, reason `2 + c` and time stamp `s + q.len()` for its atom and appends the atom to `q`.
/// Returns the reason index of the first falsified clause, 0 if there is none; after one, it sets
/// nothing more.
fn units_at(p: &Problem, l: &[Clause], cs: &[usize], t: &mut Vec<bool>, f: &mut Vec<bool>, lv: &mut Vec<usize>,
            rs: &mut Vec<usize>, ts: &mut Vec<usize>, q: &mut Vec<usize>, d: usize, s: usize) -> usize {
    let mut c = 0;
    for i in 0..cs.len() {
        if c == 0 {
            let u = clause_unit_at(p, l, cs[i], t, f);
            if u.atom < t.len() {
                if u.pos {
                    set_true(t, u.atom);
                } else {
                    set_true(f, u.atom);
                }
                set_at(lv, u.atom, d);
                set_at(rs, u.atom, sat_add(2, cs[i]));
                set_at(ts, u.atom, sat_add(s, q.len()));
                q.push(u.atom);
            } else if u.pos {
                c = sat_add(2, cs[i]);
            }
        }
    }
    c
}

/// The atoms set in `t`, `f` but in neither `qt` nor `qf`: those that theory propagation set.
fn new_atoms(t: &[bool], f: &[bool], qt: &[bool], qf: &[bool]) -> Vec<usize> {
    let mut q = Vec::new();
    for j in 0..t.len() {
        if (t[j] && !(j < qt.len() && qt[j])) || (j < f.len() && f[j] && !(j < qf.len() && qf[j])) {
            q.push(j);
        }
    }
    q
}

/// Sets `act[a]` to `m` for every atom `a` of the clause `c`: the decision order (`pick`) prefers
/// the atoms of the latest learned clauses.
fn bump(c: &Clause, act: &mut Vec<usize>, m: usize) {
    for i in 0..c.lits.len() {
        set_at(act, c.lits[i].atom, m);
    }
}

/// `bump` on the last clause of `l` with `m = l.len()`.
fn bump_last(l: &[Clause], act: &mut Vec<usize>) {
    if l.len() > 0 {
        bump(&l[l.len() - 1], act, l.len());
    }
}

/// The unset atom under `t`, `f` with the highest `act` (the first of them); `t.len()` if there
/// is none.
fn pick(t: &[bool], f: &[bool], act: &[usize]) -> usize {
    let mut k = t.len();
    for j in 0..t.len() {
        if !t[j] && !(j < f.len() && f[j]) && (k == t.len() || get_or(act, j, 0) > get_or(act, k, 0)) {
            k = j;
        }
    }
    k
}

/// The list `[x]`.
fn one(x: usize) -> Vec<usize> {
    let mut v = Vec::new();
    v.push(x);
    v
}

/// `0, 1, ..., n - 1`.
fn all_ids(n: usize) -> Vec<usize> {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    v
}

/// Unit propagation from the atoms `q0`, set in `t`, `f` (at the root, `s = 0`, first every
/// clause): for each of them, and each atom it sets in turn, `watch_visit` on the
/// literal the atom makes false and `units_at` on the clauses it returns. Returns the reason
/// index of a falsified clause (0 if there is none) and the extended assignment and records.
fn watch_pass(p: &Problem, l: &[Clause], t: &[bool], f: &[bool], q0: &[usize], lv: &[usize], rs: &[usize],
              ts: &[usize], head: &mut Vec<usize>, nxt: &mut Vec<usize>, wl: &mut Vec<usize>, d: usize, s: usize)
              -> (usize, Vec<bool>, Vec<bool>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut t1 = t.to_vec();
    let mut f1 = f.to_vec();
    let mut lv1 = lv.to_vec();
    let mut rs1 = rs.to_vec();
    let mut ts1 = ts.to_vec();
    let mut q = q0.to_vec();
    let mut c = 0;
    if s == 0 {
        let cs = all_ids(sat_add(p.clauses.len(), l.len()));
        c = units_at(p, l, &cs, &mut t1, &mut f1, &mut lv1, &mut rs1, &mut ts1, &mut q, d, s);
    }
    for i in 0..t.len() {
        if c > 0 || i >= q.len() {
            break;
        }
        let a = q[i];
        let lc = if a < t1.len() && t1[a] { sat_add(a, a) } else { sat_add(sat_add(a, a), 1) };
        let cs = watch_visit(p, l, lc, &t1, &f1, head, nxt, wl);
        c = units_at(p, l, &cs, &mut t1, &mut f1, &mut lv1, &mut rs1, &mut ts1, &mut q, d, s);
    }
    (c, t1, f1, lv1, rs1, ts1)
}

/// The position other than `skip` of the literal of `c` whose atom has the highest level in `lv`
/// (the first of them); the number of literals if there is none.
fn top_level(c: &Clause, lv: &[usize], skip: usize) -> usize {
    let mut x = c.lits.len();
    for k in 0..c.lits.len() {
        if k != skip && (x == c.lits.len() || get_or(lv, c.lits[k].atom, 0) > get_or(lv, c.lits[x].atom, 0)) {
            x = k;
        }
    }
    x
}

/// Puts slot `w` first in the list of the literal with code `code`.
fn link(head: &mut Vec<usize>, nxt: &mut Vec<usize>, code: usize, w: usize) {
    set_at(nxt, w, get_or(head, code, cap()));
    set_at(head, code, w);
}

/// Adds the two slots of clause `c`, watching the literals of the two highest levels in `lv`
/// (`top_level`): after a backjump, the literal the clause propagates and one at the level of
/// the jump.
fn watch_clause(c: &Clause, lv: &[usize], head: &mut Vec<usize>, nxt: &mut Vec<usize>, wl: &mut Vec<usize>) {
    let a = top_level(c, lv, c.lits.len());
    let b0 = top_level(c, lv, a);
    let b = if b0 < c.lits.len() { b0 } else { a };
    let w = nxt.len();
    wl.push(a);
    wl.push(b);
    nxt.push(cap());
    nxt.push(cap());
    if a < c.lits.len() {
        link(head, nxt, lit_code(&c.lits[a]), w);
    }
    if b < c.lits.len() {
        link(head, nxt, lit_code(&c.lits[b]), sat_add(w, 1));
    }
}

/// Watches the clauses of the problem's clauses followed by `l` that have no slots yet (those
/// from `nxt.len() / 2` on), by `watch_clause`.
fn watch_new(p: &Problem, l: &[Clause], lv: &[usize], head: &mut Vec<usize>, nxt: &mut Vec<usize>, wl: &mut Vec<usize>) {
    for c in nxt.len() / 2..sat_add(p.clauses.len(), l.len()) {
        if c < p.clauses.len() {
            watch_clause(&p.clauses[c], lv, head, nxt, wl);
        } else if c - p.clauses.len() < l.len() {
            watch_clause(&l[c - p.clauses.len()], lv, head, nxt, wl);
        }
    }
}

/// The search with conflict analysis and backjumping: `search` on the partial assignment `t`, `f`
/// at decision level `d`, with the records `lv`, `rs`, `ts` of the set atoms (see above) and the
/// next time stamp `s`. Unit propagation (`watch_pass`) starts from the atoms `q` (those set since
/// the last propagation), with the watch lists `wt` = (`head`, `nxt`, `wl`) (see above); the
/// closure uses the symbol index `ix` (`sym_index`). A conflict (a falsified clause, or a closure
/// conflict) is analysed (`on_conflict`). Returns the result, the learned clauses, a level `j` and
/// the watch lists. Without a model: if `j >= d`, no completion of `t`, `f` is a model (the branch
/// is refuted); if `j < d`, the search returns to level `j`, where the last learned clause
/// propagates. The decision on atom `k` at level `d` handles the result of its branch: a jump to
/// level `d` propagates the last learned clause; a refuted branch `k` true continues with `k` false.
fn cdcl(p: &Problem, ix: &(Vec<usize>, Vec<usize>), l: Vec<Clause>, t: Vec<bool>, f: Vec<bool>, q: &[usize], lv: Vec<usize>,
        rs: Vec<usize>, ts: Vec<usize>, wt: (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>), rep: &[usize], xs: &[usize], ys: &[usize],
        ls: &[usize], d: usize, s: usize) -> (Option<Model>, Vec<Clause>, usize, (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>)) {
    let s1 = sat_add(s, 1);
    let (head, nxt, wl, act) = wt;
    let mut h = head;
    let mut n = nxt;
    let mut w = wl;
    let mut a = act;
    let (c0, t0, f0, lv0, rs0, ts0) = watch_pass(p, &l, &t, &f, q, &lv, &rs, &ts, &mut h, &mut n, &mut w, d, s);
    if c0 > 0 {
        if t.len() == 0 {
            return (None, l, d, (h, n, w, a));
        }
        let c = indexed_clause(p, &l, c0, 0);
        let (r, l1, j) = on_conflict(p, l, &t0, &lv0, &ts0, &rs0, xs, ys, ls, d, &c);
        watch_new(p, &l1, &lv0, &mut h, &mut n, &mut w);
        bump_last(&l1, &mut a);
        return (r, l1, j, (h, n, w, a));
    }
    if differs(&t, &t0) || differs(&f, &f0) {
        let s0 = sat_add(s, sat_add(t.len(), 1));
        return cdcl(p, ix, l, t0, f0, &Vec::new(), lv0, rs0, ts0, (h, n, w, a), rep, xs, ys, ls, d, s0);
    }
    let (c, t2, f2, rep2, xs2, ys2, ls2) = cc_step(p, &ix.0, &ix.1, &t, &f, rep, xs, ys, ls);
    if c < t.len() {
        let cl = conflict_clause(&explain_log(p, &t, &xs2, &ys2, &ls2, c), c);
        let (r, l1, j) = on_conflict(p, l, &t, &lv, &ts, &rs, &xs2, &ys2, &ls2, d, &cl);
        watch_new(p, &l1, &lv, &mut h, &mut n, &mut w);
        bump_last(&l1, &mut a);
        return (r, l1, j, (h, n, w, a));
    }
    if differs(&t, &t2) || differs(&f, &f2) {
        let lv2 = note_new(&t, &f, &t2, &f2, &lv, d);
        let rs2 = note_true(&t, &t2, &rs, 1);
        let ts2 = note_new(&t, &f, &t2, &f2, &ts, s);
        let q2 = new_atoms(&t2, &f2, &t, &f);
        return cdcl(p, ix, l, t2, f2, &q2, lv2, rs2, ts2, (h, n, w, a), &rep2, &xs2, &ys2, &ls2, d, s1);
    }
    let k = pick(&t, &f, &a);
    if k == t.len() {
        if prop_holds(p, &t) {
            return (theory_check(p, &t), l, d, (h, n, w, a));
        }
        return (None, l, d, (h, n, w, a));
    }
    let d1 = sat_add(d, 1);
    let mut t1 = t.clone();
    t1[k] = true;
    let (r, l1, j, wt1) = cdcl(p, ix, l, t1, f.clone(), &one(k), note(&lv, k, d1), rs.clone(), note(&ts, k, s), (h, n, w, a),
                               rep, xs, ys, ls, d1, s1);
    if r.is_some() {
        return (r, l1, j, wt1);
    }
    if j >= d1 {
        let mut f1 = f.clone();
        f1[k] = true;
        return cdcl(p, ix, l1, t.clone(), f1, &one(k), note(&lv, k, d), rs.clone(), note(&ts, k, s), wt1, rep, xs, ys, ls, d, s1);
    }
    if j < d {
        return (None, l1, j, wt1);
    }
    if l1.len() > 0 {
        let u1 = clause_unit(&t, &f, &l1[l1.len() - 1]);
        if u1.atom < t.len() {
            let ci = sat_add(sat_add(1, p.clauses.len()), l1.len());
            let mut t3 = t.clone();
            let mut f3 = f.clone();
            if u1.pos {
                t3[u1.atom] = true;
            } else {
                f3[u1.atom] = true;
            }
            return cdcl(p, ix, l1, t3, f3, &one(u1.atom), note(&lv, u1.atom, d), note(&rs, u1.atom, ci), note(&ts, u1.atom, s),
                        wt1, rep, xs, ys, ls, d, s1);
        }
        if u1.pos {
            return (None, l1, d, wt1);
        }
    }
    let (r2, l2) = search(p, l1, t.clone(), f.clone());
    (r2, l2, d, wt1)
}

// ---------------------------------------------------------------------------------------------
// Equality elimination: a declared constant `c` whose every occurrence is a side of an equality
// `(= c x)` or `(= x c)` with a constant `x`, all of them conjuncts of one conjunction at a positive
// position of an assertion (reached from the assertion through `and` and `or` only), is replaced
// by the other side `g` of the first of them. The conjunction implies `c = g`, so a model of the
// problem with `c` replaced is a model of the problem once `c` means what `g` means; and a model of
// the problem satisfies the problem with `c` replaced: where the conjunction holds, `c` already has
// the value of `g`, and elsewhere replacing `c` can only make the conjunction true, which keeps a
// true assertion true. One pass over the declared symbols, in order.
// These functions have mutable locals of the type `Vec<SmtTerm>`, so they stay at the end of the
// file (see above).

/// The number of applications of the declared symbol `c` in `t`, saturated at `cap()`.
fn occ(t: &SmtTerm, c: usize) -> usize {
    match t {
        SmtTerm::Fun(f, args) => sat_add(if *f == c { 1 } else { 0 }, occs(args, c)),
        SmtTerm::Def(_, args) | SmtTerm::App(_, args) => occs(args, c),
        _ => 0,
    }
}

/// `occ` summed over `ts`, saturated at `cap()`.
fn occs(ts: &Vec<SmtTerm>, c: usize) -> usize {
    let mut n: usize = 0;
    for i in 0..ts.len() {
        n = sat_add(n, occ(&ts[i], c));
    }
    n
}

/// `occ` in the assertions `a` and in the bodies of the definitions of `p`, saturated at `cap()`.
fn occ_all(p: &SmtProblem, a: &Vec<SmtTerm>, c: usize) -> usize {
    let mut n = occs(a, c);
    for d in 0..p.defs.len() {
        n = sat_add(n, occ(&p.defs[d].body, c));
    }
    n
}

/// The symbol `f` if `t` is the constant `f` (an application without arguments), `n` otherwise.
fn const_sym(t: &SmtTerm, n: usize) -> usize {
    match t {
        SmtTerm::Fun(f, args) => {
            if args.len() == 0 { *f } else { n }
        }
        _ => n,
    }
}

/// The symbol `g` if `t` is `(= c g)` or `(= g c)` for constants `c` and `g < n` other than `c`;
/// `n` otherwise.
fn eq_partner(t: &SmtTerm, c: usize, n: usize) -> usize {
    match t {
        SmtTerm::App(SmtOp::Eq, args) => {
            if args.len() != 2 {
                return n;
            }
            let x = const_sym(&args[0], n);
            let y = const_sym(&args[1], n);
            if x == c && y < n && y != c {
                return y;
            }
            if y == c && x < n && x != c {
                return x;
            }
            n
        }
        _ => n,
    }
}

/// The number of terms of `ts` for which `eq_partner` finds a partner.
fn eq_count(ts: &Vec<SmtTerm>, c: usize, n: usize) -> usize {
    let mut k: usize = 0;
    for i in 0..ts.len() {
        if eq_partner(&ts[i], c, n) < n {
            k += 1;
        }
    }
    k
}

/// The partner of the first term of `ts` for which `eq_partner` finds one; `n` if there is none.
fn first_partner(ts: &Vec<SmtTerm>, c: usize, n: usize) -> usize {
    for i in 0..ts.len() {
        let g = eq_partner(&ts[i], c, n);
        if g < n {
            return g;
        }
    }
    n
}

/// Searches the positive positions of `t` (`t` itself and, below an `and` or `or`, its arguments)
/// for a conjunction with `tot` conjuncts for which `eq_partner` finds a partner; returns the
/// first partner in the first such conjunction, `n` if there is none.
fn find_conj(t: &SmtTerm, c: usize, tot: usize, n: usize) -> usize {
    match t {
        SmtTerm::App(SmtOp::And, args) => {
            if eq_count(args, c, n) == tot {
                return first_partner(args, c, n);
            }
            find_conjs(args, c, tot, n)
        }
        SmtTerm::App(SmtOp::Or, args) => find_conjs(args, c, tot, n),
        _ => n,
    }
}

/// `find_conj` on the terms of `ts` in turn; the first result below `n`, or `n`.
fn find_conjs(ts: &Vec<SmtTerm>, c: usize, tot: usize, n: usize) -> usize {
    for i in 0..ts.len() {
        let g = find_conj(&ts[i], c, tot, n);
        if g < n {
            return g;
        }
    }
    n
}

/// The symbol that replaces the declared symbol `c` in the assertions `a` of `p` (with the
/// definitions of `p`), or `p.funs.len()` if `c` is not eliminated: `c` and its partner are
/// constants of the same sort, and every occurrence of `c` is in the conjunction `find_conj` found.
fn elim_partner(p: &SmtProblem, a: &Vec<SmtTerm>, c: usize) -> usize {
    let n = p.funs.len();
    if p.funs[c].args.len() != 0 {
        return n;
    }
    let tot = occ_all(p, a, c);
    if tot == 0 || tot >= cap() {
        return n;
    }
    let g = find_conjs(a, c, tot, n);
    if g < n && p.funs[g].args.len() == 0 && p.funs[g].ret == p.funs[c].ret {
        return g;
    }
    n
}

/// `t` with every application of the symbol `c` replaced by one of `g`.
fn rename(t: &SmtTerm, c: usize, g: usize) -> SmtTerm {
    match t {
        SmtTerm::Fun(f, args) => SmtTerm::Fun(if *f == c { g } else { *f }, renames(args, c, g)),
        SmtTerm::Def(d, args) => SmtTerm::Def(*d, renames(args, c, g)),
        SmtTerm::App(o, args) => SmtTerm::App(o.clone(), renames(args, c, g)),
        _ => t.clone(),
    }
}

/// `rename` on every term of `ts`.
fn renames(ts: &Vec<SmtTerm>, c: usize, g: usize) -> Vec<SmtTerm> {
    let mut out = Vec::new();
    for i in 0..ts.len() {
        out.push(rename(&ts[i], c, g));
    }
    out
}

/// The assertions of `p` after equality elimination, and the eliminated symbols `cs[i]` with
/// their replacements `gs[i]`, in the order of elimination.
fn eliminate(p: &SmtProblem) -> (Vec<SmtTerm>, Vec<usize>, Vec<usize>) {
    let mut a = p.asserts.clone();
    let mut cs = Vec::new();
    let mut gs = Vec::new();
    for c in 0..p.funs.len() {
        let g = elim_partner(p, &a, c);
        if g < p.funs.len() {
            a = renames(&a, c, g);
            cs.push(c);
            gs.push(g);
        }
    }
    (a, cs, gs)
}

/// The model `m` of the problem after elimination, made a model of the problem before: in
/// reverse order of elimination, each eliminated symbol `cs[i]` gets the table of `gs[i]`.
fn restore(m: SmtModel, cs: &Vec<usize>, gs: &Vec<usize>) -> SmtModel {
    let mut funs = m.funs;
    for k in 0..cs.len() {
        let i = cs.len() - 1 - k;
        if cs[i] < funs.len() && i < gs.len() && gs[i] < funs.len() {
            let v = funs[gs[i]].clone();
            funs[cs[i]] = v;
        }
    }
    SmtModel { domains: m.domains, funs: funs }
}
