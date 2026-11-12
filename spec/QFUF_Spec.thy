theory QFUF_Spec
  imports SMT_Semantics
begin

section \<open>The top-level specification of the QF\_UF solver\<close>

text \<open>
  Source: \<^verbatim>\<open>core/src/lib.rs\<close>. The specified function is \<^verbatim>\<open>pub fn solve(p: &Problem) -> Answer\<close>;
  the translation passes \<^verbatim>\<open>p\<close> by value.

  A problem is a CNF formula over equalities between ground terms of one uninterpreted sort. Term
  \<open>i\<close> of \<^const>\<open>Problem_terms\<close> applies function symbol \<^const>\<open>Term_fun\<close> (a number; constants are
  0-ary symbols) to the terms whose indices are listed in \<^const>\<open>Term_args\<close>. Atom \<open>k\<close> is the
  equality between the terms \<^const>\<open>Atom_lhs\<close> and \<^const>\<open>Atom_rhs\<close>. A literal is an atom index
  with a polarity, a clause is a disjunction of literals, and the problem is the conjunction of its
  clauses.
\<close>

subsection \<open>Semantics of problems\<close>

text \<open>An interpretation is a function \<open>I\<close>: \<open>I f vs\<close> is the value of symbol \<open>f\<close> applied to the values
  \<open>vs\<close>. \<open>I f\<close> is a function on lists, so the same symbol applied to different numbers of arguments
  gives unrelated values.\<close>

function term_val :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Term list \<Rightarrow> nat \<Rightarrow> 'd\<close> where
  \<open>term_val I ts i =
     I (unat (Term_fun (ts ! i)))
       (List.map (\<lambda>x. if unat x < i then term_val I ts (unat x) else undefined) (Term_args (ts ! i)))\<close>
  by auto
termination
  by (relation \<open>measure (\<lambda>(_, _, i). i)\<close>) auto

declare term_val.simps [simp del]

text \<open>\<^const>\<open>term_val\<close> \<open>I ts i\<close> is the value of term \<open>i\<close> under \<open>I\<close>. The guard \<open>unat x < i\<close> makes the
  recursion well-founded.\<close>

definition atom_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Atom \<Rightarrow> bool\<close> where
  \<open>atom_true I p at \<equiv>
     term_val I (Problem_terms p) (unat (Atom_lhs at)) = term_val I (Problem_terms p) (unat (Atom_rhs at))\<close>

definition lit_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_true I p l \<equiv> atom_true I p (Problem_atoms p ! unat (Lit_atom l)) = Lit_pos l\<close>

definition clause_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_true I p c \<equiv> \<exists>l \<in> set (Clause_lits c). lit_true I p l\<close>

definition problem_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> bool\<close> where
  \<open>problem_true I p \<equiv> \<forall>c \<in> set (Problem_clauses p). clause_true I p c\<close>

text \<open>\<^const>\<open>atom_true\<close>: both sides of the atom have the same value. \<^const>\<open>lit_true\<close>: the
  atom's truth value equals the literal's polarity. \<^const>\<open>clause_true\<close>: some literal holds.
  \<^const>\<open>problem_true\<close>: every clause holds.\<close>

definition satisfiable :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>satisfiable p \<equiv> \<exists>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p\<close>

text \<open>\<^const>\<open>satisfiable\<close>: some interpretation over \<^typ>\<open>nat\<close> makes the problem true. The domain is
  fixed to \<^typ>\<open>nat\<close> because a HOL formula cannot quantify over types.\<close>

subsection \<open>Models\<close>

definition model_interp :: \<open>Model \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where
  \<open>model_interp m f vs \<equiv>
     (case List.find (\<lambda>e. unat (Entry_fun e) = f \<and> List.map unat (Entry_args e) = vs) (Model_entries m) of
        Some e \<Rightarrow> unat (Entry_val e)
      | None \<Rightarrow> 0)\<close>

text \<open>\<^const>\<open>model_interp\<close> \<open>m\<close> is the interpretation that the documentation of \<^verbatim>\<open>Model\<close> in
  \<^verbatim>\<open>lib.rs\<close> describes: symbol \<open>f\<close> applied to \<open>vs\<close> has the value of the first entry with symbol \<open>f\<close>
  and arguments \<open>vs\<close>, and the value 0 if there is no such entry. Entries store \<^verbatim>\<open>usize\<close> values,
  which the translation represents as 64-bit words; \<^term>\<open>unat\<close> reads them as natural numbers.\<close>

subsection \<open>Preconditions\<close>

definition wf_problem :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>wf_problem p \<equiv>
     (\<forall>i < length (Problem_terms p). \<forall>x \<in> set (Term_args (Problem_terms p ! i)). unat x < i) \<and>
     (\<forall>at \<in> set (Problem_atoms p).
        unat (Atom_lhs at) < length (Problem_terms p) \<and> unat (Atom_rhs at) < length (Problem_terms p)) \<and>
     (\<forall>c \<in> set (Problem_clauses p). \<forall>l \<in> set (Clause_lits c).
        unat (Lit_atom l) < length (Problem_atoms p))\<close>

text \<open>\<^const>\<open>wf_problem\<close> has three parts:
  \<^item> Every argument index of term \<open>i\<close> is smaller than \<open>i\<close>. The terms then form a DAG in index
    order, which \<^const>\<open>term_val\<close> needs to give every term a value: the guard \<open>unat x < i\<close> in
    \<^const>\<open>term_val\<close> then always holds, and the \<^const>\<open>undefined\<close> branch is not taken. The
    condition also puts the argument indices in bounds.
  \<^item> The two term indices of every atom are in bounds.
  \<^item> The atom index of every literal is in bounds.
  Rust panics on an out-of-bounds index, and the contract excludes aborts, so the indices must be in
  bounds.\<close>

definition sizes_ok :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>sizes_ok p \<equiv>
     length (Problem_terms p) < 2^63 \<and> (\<forall>t \<in> set (Problem_terms p). length (Term_args t) < 2^63) \<and>
     length (Problem_atoms p) < 2^63 \<and>
     length (Problem_clauses p) < 2^63 \<and> (\<forall>c \<in> set (Problem_clauses p). length (Clause_lits c) < 2^63)\<close>

text \<open>\<^const>\<open>sizes_ok\<close>: every \<^verbatim>\<open>Vec\<close> in the problem has fewer than \<open>2^63\<close> elements. Rust ensures
  this for a \<^verbatim>\<open>Vec\<close> of non-zero-sized elements, because an allocation has at most
  \<^verbatim>\<open>isize::MAX\<close> bytes. The translation represents a \<^verbatim>\<open>Vec\<close> as a HOL list, which has no such
  bound, so the contract states it.\<close>

subsection \<open>The contract\<close>

context QFUF_ctx
begin

definition solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> problem_true (model_interp m) p
         | Answer_Unsat \<Rightarrow> \<not> satisfiable p\<rangle> in
     make_function_contract pre post\<close>

text \<open>\<^const>\<open>solve_contract\<close> \<open>p\<close>:
  \<^item> Precondition: \<^const>\<open>wf_problem\<close> \<open>p\<close> and \<^const>\<open>sizes_ok\<close> \<open>p\<close>. The contract does not mention
    the fuel \<^term>\<open>urust_fuel\<close>; how much fuel \<^verbatim>\<open>solve\<close> needs is part of the specification
    \<open>solve_correct\<close> below, not of the contract.
  \<^item> Answer \<^verbatim>\<open>Sat(m)\<close>: \<^const>\<open>model_interp\<close> \<open>m\<close> makes the problem true.
  \<^item> Answer \<^verbatim>\<open>Unsat\<close>: no interpretation over \<^typ>\<open>nat\<close> makes the problem true.
  \<^item> \<^const>\<open>make_function_contract\<close> makes the abort postcondition false, so the translated program
    does not panic. The translation does not model memory exhaustion or stack overflow, so this
    says nothing about aborts for these reasons.
  \<^item> \<^term>\<open>can_alloc_reference\<close> is AutoCorrode's permission to allocate the solver's mutable
    locals; the postcondition returns it to the caller.\<close>

end

subsection \<open>The specification\<close>

text \<open>The translation defines the recursive function \<^verbatim>\<open>search\<close> by unfolding it
  \<open>urust_fuel\<close> times, where \<open>urust_fuel\<close> is the last parameter of the locale
  \<^locale>\<open>QFUF_ctx\<close>; the innermost unfolding panics. \<^verbatim>\<open>solve\<close> therefore satisfies
  \<^const>\<open>QFUF_ctx.solve_contract\<close> only when the fuel is large enough for the problem, and the specification
  says that enough fuel exists: for every problem that satisfies the precondition there is a bound
  such that \<^verbatim>\<open>solve\<close> satisfies the contract in every instance of \<^locale>\<open>QFUF_ctx\<close> whose fuel
  is at least the bound.

  The fuel is a parameter of \<^locale>\<open>QFUF_ctx\<close>, so this statement ranges over instances of the
  locale and is made outside it. The assumptions of \<^locale>\<open>QFUF_ctx\<close> do not mention the fuel, so
  its instances that differ only in the fuel share their assumptions. The locale \<^verbatim>\<open>QFUF_heap\<close>
  below has the parameters and assumptions of \<^locale>\<open>QFUF_ctx\<close> except the fuel (it repeats the
  locale \<^verbatim>\<open>QFUF_ctx\<close> of \<^verbatim>\<open>urust/QFUF_Locale.thy\<close> without its last line); each value of the
  fuel gives an instance of \<^locale>\<open>QFUF_ctx\<close> with the parameters of \<^verbatim>\<open>QFUF_heap\<close>.\<close>

locale QFUF_heap =
  reference reference_types
  + ref_1: reference_allocatable reference_types _ _ _ _ _ _ _ prism_1 \<comment> \<open>bool\<close>
  + ref_2: reference_allocatable reference_types _ _ _ _ _ _ _ prism_2 \<comment> \<open>(64 word) list\<close>
  + ref_3: reference_allocatable reference_types _ _ _ _ _ _ _ prism_3 \<comment> \<open>Entry list\<close>
  + ref_4: reference_allocatable reference_types _ _ _ _ _ _ _ prism_4 \<comment> \<open>bool list\<close>
  + ref_5: reference_allocatable reference_types _ _ _ _ _ _ _ prism_5 \<comment> \<open>Term list\<close>
  + ref_6: reference_allocatable reference_types _ _ _ _ _ _ _ prism_6 \<comment> \<open>Atom list\<close>
  + ref_7: reference_allocatable reference_types _ _ _ _ _ _ _ prism_7 \<comment> \<open>Clause list\<close>
  + ref_8: reference_allocatable reference_types _ _ _ _ _ _ _ prism_8 \<comment> \<open>Tr\<close>
  + ref_9: reference_allocatable reference_types _ _ _ _ _ _ _ prism_9 \<comment> \<open>Lit list\<close>
  + ref_10: reference_allocatable reference_types _ _ _ _ _ _ _ prism_10 \<comment> \<open>64 word\<close>
  + ref_11: reference_allocatable reference_types _ _ _ _ _ _ _ prism_11 \<comment> \<open>((64 word) \<times> bool \<times> tnil) list\<close>
  + ref_12: reference_allocatable reference_types _ _ _ _ _ _ _ prism_12 \<comment> \<open>((64 word) \<times> bool \<times> tnil)\<close>
  + ref_13: reference_allocatable reference_types _ _ _ _ _ _ _ prism_13 \<comment> \<open>Enc list\<close>
  + ref_14: reference_allocatable reference_types _ _ _ _ _ _ _ prism_14 \<comment> \<open>SmtEntry list\<close>
  + ref_15: reference_allocatable reference_types _ _ _ _ _ _ _ prism_15 \<comment> \<open>SmtValue list\<close>
  + ref_16: reference_allocatable reference_types _ _ _ _ _ _ _ prism_16 \<comment> \<open>SmtInterp list\<close>
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and prism_1 :: \<open>('gv, bool) prism\<close>
  and prism_2 :: \<open>('gv, (64 word) list) prism\<close>
  and prism_3 :: \<open>('gv, Entry list) prism\<close>
  and prism_4 :: \<open>('gv, bool list) prism\<close>
  and prism_5 :: \<open>('gv, Term list) prism\<close>
  and prism_6 :: \<open>('gv, Atom list) prism\<close>
  and prism_7 :: \<open>('gv, Clause list) prism\<close>
  and prism_8 :: \<open>('gv, Tr) prism\<close>
  and prism_9 :: \<open>('gv, Lit list) prism\<close>
  and prism_10 :: \<open>('gv, 64 word) prism\<close>
  and prism_11 :: \<open>('gv, ((64 word) \<times> bool \<times> tnil) list) prism\<close>
  and prism_12 :: \<open>('gv, ((64 word) \<times> bool \<times> tnil)) prism\<close>
  and prism_13 :: \<open>('gv, Enc list) prism\<close>
  and prism_14 :: \<open>('gv, SmtEntry list) prism\<close>
  and prism_15 :: \<open>('gv, SmtValue list) prism\<close>
  and prism_16 :: \<open>('gv, SmtInterp list) prism\<close>
begin

abbreviation solve :: \<open>nat \<Rightarrow> Problem \<Rightarrow> ('s, Answer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>solve fuel \<equiv>
     QFUF_ctx.solve update_raw_fun dereference_raw_fun reference_raw_fun prism_1 prism_2 prism_3 prism_4 fuel\<close>

abbreviation solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract \<equiv> QFUF_ctx.solve_contract can_alloc_reference\<close>

text \<open>\<open>solve fuel\<close> is the translation's \<^verbatim>\<open>solve\<close> in the instance of \<^locale>\<open>QFUF_ctx\<close> with the
  parameters of \<^verbatim>\<open>QFUF_heap\<close> and the fuel \<open>fuel\<close>; \<open>solve_contract\<close> is \<^const>\<open>QFUF_ctx.solve_contract\<close>
  of that instance, which is the same for every fuel. Outside its locale, a constant defined in
  \<^locale>\<open>QFUF_ctx\<close> takes as its first arguments the locale parameters on which its definition
  depends: \<^verbatim>\<open>solve\<close> depends on the three reference operations, the four prisms and the fuel,
  \<^const>\<open>QFUF_ctx.solve_contract\<close> only on \<^term>\<open>can_alloc_reference\<close>.\<close>

definition solve_correct where
  \<open>solve_correct \<Gamma> \<equiv>
     \<forall>p. wf_problem p \<and> sizes_ok p \<longrightarrow> (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p)\<close>

text \<open>\<^const>\<open>solve_correct\<close> \<open>\<Gamma>\<close> is the statement to prove: for every problem \<open>p\<close> that satisfies
  the precondition of \<^const>\<open>QFUF_ctx.solve_contract\<close> there is a bound \<open>N\<close> such that, in every
  instance of \<^locale>\<open>QFUF_ctx\<close> with fuel at least \<open>N\<close>, \<^verbatim>\<open>solve\<close> \<open>p\<close> satisfies
  \<^const>\<open>QFUF_ctx.solve_contract\<close> \<open>p\<close>. \<^verbatim>\<open>QFUF_Proof\<close> proves it as the theorem
  \<open>solve_correct\<close>.\<close>

end


section \<open>The specification of the solver on general problems\<close>

text \<open>
  The Rust entry point on general problems is \<^verbatim>\<open>pub fn check_sat(p: &SmtProblem) -> SmtAnswer\<close>,
  translated to \<^verbatim>\<open>QFUF_ctx.check_sat\<close>. Its specification uses the semantics of
  \<^verbatim>\<open>SMT_Semantics\<close> (the same theory in both solvers) and differs from that of the QF\_BV solver
  in the fragment (this solver handles the problems without bit-vectors) and in the size of
  problems for which it may answer \<^verbatim>\<open>Unknown\<close>.\<close>

fun smt_sort_no_bv :: \<open>SmtSort \<Rightarrow> bool\<close> where
  \<open>smt_sort_no_bv (SmtSort_BitVec w) = False\<close>
| \<open>smt_sort_no_bv _ = True\<close>

text \<open>The theory functions of Core.\<close>
fun smt_core_op :: \<open>SmtOp \<Rightarrow> bool\<close> where
  \<open>smt_core_op SmtOp_Not = True\<close>
| \<open>smt_core_op SmtOp_And = True\<close>
| \<open>smt_core_op SmtOp_Or = True\<close>
| \<open>smt_core_op SmtOp_Xor = True\<close>
| \<open>smt_core_op SmtOp_Implies = True\<close>
| \<open>smt_core_op SmtOp_Eq = True\<close>
| \<open>smt_core_op SmtOp_Distinct = True\<close>
| \<open>smt_core_op SmtOp_Ite = True\<close>
| \<open>smt_core_op _ = False\<close>

text \<open>No bit-vector constant or function occurs in a term.\<close>
fun smt_term_no_bv :: \<open>SmtTerm \<Rightarrow> bool\<close> where
  \<open>smt_term_no_bv (SmtTerm_BoolConst b) = True\<close>
| \<open>smt_term_no_bv (SmtTerm_BvConst bs) = False\<close>
| \<open>smt_term_no_bv (SmtTerm_Param k) = True\<close>
| \<open>smt_term_no_bv (SmtTerm_Fun f args) = (\<forall>a \<in> set args. smt_term_no_bv a)\<close>
| \<open>smt_term_no_bv (SmtTerm_Def d args) = (\<forall>a \<in> set args. smt_term_no_bv a)\<close>
| \<open>smt_term_no_bv (SmtTerm_App op args) = (smt_core_op op \<and> (\<forall>a \<in> set args. smt_term_no_bv a))\<close>

text \<open>The fragment of this solver: no bit-vector sort, constant or function occurs in the problem.\<close>
definition smt_fragment :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_fragment p \<equiv>
     (\<forall>f \<in> set (SmtProblem_funs p). (\<forall>s \<in> set (SmtFun_args f). smt_sort_no_bv s) \<and> smt_sort_no_bv (SmtFun_ret f)) \<and>
     (\<forall>d \<in> set (SmtProblem_defs p). (\<forall>s \<in> set (SmtDef_params d). smt_sort_no_bv s) \<and>
        smt_sort_no_bv (SmtDef_ret d) \<and> smt_term_no_bv (SmtDef_body d)) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). smt_term_no_bv t)\<close>

context QFUF_ctx
begin

definition check_sat_contract :: \<open>SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort) function_contract\<close> where
  \<open>check_sat_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>smt_wf p \<and> smt_repr_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           SmtAnswer_Sat m \<Rightarrow> smt_is_model p m
         | SmtAnswer_Unsat \<Rightarrow> \<not> smt_satisfiable p
         | SmtAnswer_Unknown \<Rightarrow> \<not> smt_fragment p \<or> \<not> smt_sizes_ok p\<rangle> in
     make_function_contract pre post\<close>

text \<open>\<^const>\<open>check_sat_contract\<close> \<open>p\<close>:
  \<^item> Precondition: \<open>p\<close> is well-sorted (\<^const>\<open>smt_wf\<close>), and every list in it has fewer than
    \<open>2^63\<close> elements (\<^const>\<open>smt_repr_ok\<close>, which holds for every value of a Rust program).
  \<^item> \<^verbatim>\<open>Sat(m)\<close>: \<open>m\<close> is a model of \<open>p\<close>. \<^verbatim>\<open>Unsat\<close>: \<open>p\<close> has no model. \<^verbatim>\<open>Unknown\<close>: \<open>p\<close> is not in
    the fragment of this solver, or it is large (\<^const>\<open>smt_size_bound\<close> \<open>p\<close> is not below
    \<open>2^64\<close>). For a problem in the fragment with \<^const>\<open>smt_sizes_ok\<close> the answer is \<^verbatim>\<open>Sat\<close>
    or \<^verbatim>\<open>Unsat\<close>. (The solver checks a bound on the size of the problem it translates \<open>p\<close> into,
    so it may also answer \<^verbatim>\<open>Sat\<close> or \<^verbatim>\<open>Unsat\<close> for a larger problem.)
  \<^item> No panic (the abort postcondition is false), as for \<^const>\<open>solve_contract\<close>. The program
    logic does not model the exhaustion of memory or of the stack, so the contract says nothing
    about them.\<close>

end

context QFUF_heap
begin

abbreviation check_sat :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>check_sat fuel \<equiv>
     QFUF_ctx.check_sat update_raw_fun dereference_raw_fun reference_raw_fun
       prism_1 prism_2 prism_3 prism_4 prism_5 prism_6 prism_7 prism_8 prism_9 prism_10 prism_11 prism_12
       prism_13 prism_14 prism_15 prism_16 fuel\<close>

abbreviation check_sat_contract :: \<open>SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort) function_contract\<close> where
  \<open>check_sat_contract \<equiv> QFUF_ctx.check_sat_contract can_alloc_reference\<close>

definition check_sat_correct where
  \<open>check_sat_correct \<Gamma> \<equiv>
     \<forall>p. smt_wf p \<and> smt_repr_ok p \<longrightarrow> (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p)\<close>

text \<open>\<^const>\<open>check_sat_correct\<close> \<open>\<Gamma>\<close> is the top-level statement: for every problem that satisfies the
  precondition of \<^const>\<open>QFUF_ctx.check_sat_contract\<close> there is a bound \<open>N\<close> such that, with any
  fuel at least \<open>N\<close>, \<^verbatim>\<open>check_sat\<close> satisfies the contract. \<^verbatim>\<open>QFUF_Top\<close> proves it as the theorem
  \<open>check_sat_correct\<close>.\<close>

end

end
