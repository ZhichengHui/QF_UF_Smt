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
    let (r, _l, _j) = cdcl(p, Vec::new(), vec![false; n], vec![false; n], vec![0; n], vec![0; n], vec![0; n], 0, 0);
    match r {
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

/// A set of atoms set in `t` whose equalities, closed under congruence, join the two sides of atom
/// `k`, read off `merge_log`: the atom edges on the path between the two sides in the forest, and
/// recursively those that explain the argument pairs of its congruence edges. Returns the atoms
/// and the terms of the congruence edges used.
fn path_explain(p: &Problem, t: &[bool], k: usize) -> (Vec<bool>, Vec<bool>) {
    let n = p.terms.len();
    let (xs, ys, ls) = merge_log(p, t);
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
            let (pv, pe) = bfs(n, &xs, &ys, a, b);
            walk(p, &xs, &ys, &ls, &pv, &pe, a, b, &mut e, &mut rows, &mut used, &mut qa, &mut qb);
        }
    }
    (e, rows)
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

/// The atoms set false in `f`, and every atom unset under `t`, `f` whose two sides lie in classes
/// of `rep` that the two sides of an atom set false lie in.
fn separated_unset(p: &Problem, t: &[bool], f: &[bool], rep: &[usize]) -> Vec<bool> {
    let (us, vs) = false_pairs(p, f, rep);
    let mut f1 = f.to_vec();
    for j in 0..p.atoms.len() {
        let x = rep[p.atoms[j].lhs];
        let y = rep[p.atoms[j].rhs];
        if !t[j] && !f[j] && x != y && has_pair(&us, &vs, x, y) {
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

/// The atoms set true in `t` with a time stamp below `s`.
fn true_before(t: &[bool], ts: &[usize], s: usize) -> Vec<bool> {
    let mut e = vec![false; t.len()];
    for j in 0..t.len() {
        if t[j] && get_or(ts, j, s) < s {
            e[j] = true;
        }
    }
    e
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

/// Why the closure joined the two sides of atom `x`: the clause "some atom set true before `x` is
/// false, or `x` is true", with the atoms that `path_explain` finds if `rows_join` confirms them,
/// and the tautology on `x` otherwise.
fn theory_reason(p: &Problem, t: &[bool], ts: &[usize], x: usize) -> Clause {
    let e0 = true_before(t, ts, get_or(ts, x, 0));
    let (e, rows) = path_explain(p, &e0, x);
    if rows_join(p, &e, &rows, x) {
        return conflict_clause(&e, x);
    }
    tautology(x)
}

/// The reason of atom `x` as a clause; the tautology on `x` if it has none.
fn reason(p: &Problem, l: &[Clause], t: &[bool], ts: &[usize], rs: &[usize], x: usize) -> Clause {
    let r = get_or(rs, x, 0);
    if r == 1 {
        return theory_reason(p, t, ts, x);
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
fn resolve_step(p: &Problem, l: &[Clause], t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize], d: usize,
                cp: &[bool], cn: &[bool]) -> (bool, Vec<bool>, Vec<bool>) {
    let x = last_at(lv, ts, cp, cn, d);
    if x >= cp.len() || x >= cn.len() || x >= t.len() || get_or(rs, x, 0) == 0 || !other_at(lv, cp, cn, d, x) {
        return (false, cp.to_vec(), cn.to_vec());
    }
    let r = reason(p, l, t, ts, rs, x);
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
fn analyze(p: &Problem, l: &[Clause], t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize], d: usize, c: &Clause)
           -> (Clause, bool, usize) {
    let (cp0, cn0) = add_lits(c, t.len(), true, &vec![false; t.len()], &vec![false; t.len()]);
    let mut cp = cp0;
    let mut cn = cn0;
    let mut go = true;
    for _step in 0..t.len() + 1 {
        if go {
            let (g, cp1, cn1) = resolve_step(p, l, t, lv, ts, rs, d, &cp, &cn);
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
fn on_conflict(p: &Problem, l: Vec<Clause>, t: &[bool], lv: &[usize], ts: &[usize], rs: &[usize], d: usize,
               c: &Clause) -> (Option<Model>, Vec<Clause>, usize) {
    let (a, one, b) = analyze(p, &l, t, lv, ts, rs, d, c);
    let l1 = learn(l, a);
    if one && b < d {
        return (None, l1, b);
    }
    (None, l1, d)
}

/// The reason index (`2 + i`) of the first clause of the problem's clauses followed by `l` that
/// is falsified or unit under `t`, `f`: the clause on which `next_unit` stops; 0 if there is none.
fn unit_index(p: &Problem, l: &[Clause], t: &[bool], f: &[bool]) -> usize {
    for i in 0..p.clauses.len() {
        let u = clause_unit(t, f, &p.clauses[i]);
        if u.atom < t.len() || u.pos {
            return sat_add(2, i);
        }
    }
    for i in 0..l.len() {
        let u = clause_unit(t, f, &l[i]);
        if u.atom < t.len() || u.pos {
            return sat_add(sat_add(2, p.clauses.len()), i);
        }
    }
    0
}

/// The search with conflict analysis and backjumping: `search` on the partial assignment `t`, `f`
/// at decision level `d`, with the records `lv`, `rs`, `ts` of the set atoms (see above) and the
/// next time stamp `s`. A conflict (a falsified clause, or a closure conflict) is analysed
/// (`on_conflict`). Returns the result, the learned clauses and a level `j`. Without a model: if
/// `j >= d`, no completion of `t`, `f` is a model (the branch is refuted); if `j < d`, the search
/// returns to level `j`, where the last learned clause propagates. The decision on atom `k` at
/// level `d` handles the result of its branch: a jump to level `d` propagates the last learned
/// clause; a refuted branch `k` true continues with `k` false.
fn cdcl(p: &Problem, l: Vec<Clause>, t: Vec<bool>, f: Vec<bool>, lv: Vec<usize>, rs: Vec<usize>, ts: Vec<usize>,
        d: usize, s: usize) -> (Option<Model>, Vec<Clause>, usize) {
    let s1 = sat_add(s, 1);
    let u = next_unit(p, &l, &t, &f);
    if u.atom == t.len() && u.pos {
        if t.len() == 0 {
            return (None, l, d);
        }
        let c = indexed_clause(p, &l, unit_index(p, &l, &t, &f), 0);
        return on_conflict(p, l, &t, &lv, &ts, &rs, d, &c);
    }
    if u.atom < t.len() {
        let ci = unit_index(p, &l, &t, &f);
        let mut t1 = t.clone();
        let mut f1 = f.clone();
        if u.pos {
            t1[u.atom] = true;
        } else {
            f1[u.atom] = true;
        }
        return cdcl(p, l, t1, f1, note(&lv, u.atom, d), note(&rs, u.atom, ci), note(&ts, u.atom, s), d, s1);
    }
    let (c, t2, f2) = cc_propagate(p, &t, &f);
    if c < t.len() {
        let cl = conflict_clause(&explain(p, &t, c), c);
        return on_conflict(p, l, &t, &lv, &ts, &rs, d, &cl);
    }
    if differs(&t, &t2) || differs(&f, &f2) {
        let lv2 = note_new(&t, &f, &t2, &f2, &lv, d);
        let rs2 = note_true(&t, &t2, &rs, 1);
        let ts2 = note_new(&t, &f, &t2, &f2, &ts, s);
        return cdcl(p, l, t2, f2, lv2, rs2, ts2, d, s1);
    }
    let k = first_unset(&t, &f);
    if k == t.len() {
        if prop_holds(p, &t) {
            return (theory_check(p, &t), l, d);
        }
        return (None, l, d);
    }
    let d1 = sat_add(d, 1);
    let mut t1 = t.clone();
    t1[k] = true;
    let (r, l1, j) = cdcl(p, l, t1, f.clone(), note(&lv, k, d1), rs.clone(), note(&ts, k, s), d1, s1);
    if r.is_some() {
        return (r, l1, j);
    }
    if j >= d1 {
        let mut f1 = f.clone();
        f1[k] = true;
        return cdcl(p, l1, t.clone(), f1, note(&lv, k, d), rs.clone(), note(&ts, k, s), d, s1);
    }
    if j < d {
        return (None, l1, j);
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
            return cdcl(p, l1, t3, f3, note(&lv, u1.atom, d), note(&rs, u1.atom, ci), note(&ts, u1.atom, s), d, s1);
        }
        if u1.pos {
            return (None, l1, d);
        }
    }
    let (r2, l2) = search(p, l1, t.clone(), f.clone());
    (r2, l2, d)
}
