theory QFUF_Spec
  imports SMT_Semantics
begin

section \<open>The top-level specification\<close>

text \<open>
  This theory, with \<^verbatim>\<open>SMT_Types\<close> and \<^verbatim>\<open>SMT_Semantics\<close> that it builds on, is the whole
  specification of the solver: the meaning of the top-level theorem depends on nothing outside
  \<^verbatim>\<open>spec/\<close>. The proofs (\<^verbatim>\<open>proof/\<close>) and the solver may change; this directory changes only
  when the specification does.

  The Rust entry point is \<^verbatim>\<open>pub fn check_sat(p: &SmtProblem) -> SmtAnswer\<close>
  (\<^verbatim>\<open>core/src/lib.rs\<close>), translated to \<^verbatim>\<open>QFUF_ctx.check_sat\<close>. The statement
  \<open>check_sat_correct\<close> at the end of this theory: for every well-sorted problem there is a bound
  \<open>N\<close> such that, with any fuel at least \<open>N\<close>, \<^verbatim>\<open>check_sat\<close> satisfies its contract. The
  contract allows the answer \<^verbatim>\<open>Sat\<close> only with a model, \<^verbatim>\<open>Unsat\<close> only for a problem without a
  model, and \<^verbatim>\<open>Unknown\<close> only for a problem outside the fragment of this solver or above the size
  bound of \<^verbatim>\<open>SMT_Semantics\<close>.

  Trusted, not proved here:
  \<^item> The translation (AutoCorrode) gives the Rust program its meaning. The theorem is about the
    translated function; that it carries over to the compiled Rust program rests on the
    translation.
  \<^item> The statement is made in the locale \<open>QFUF_heap\<close>, whose assumptions describe a heap with one
    kind of reference per type of mutable local. They are those of AutoCorrode's reference model,
    and the theorem holds for every heap that satisfies them.
  \<^item> The front end (\<^verbatim>\<open>frontend/\<close>), which turns SMT-LIB text into a \<^typ>\<open>SmtProblem\<close> and a
    \<^typ>\<open>SmtModel\<close> back into text, is not verified.
\<close>

subsection \<open>The fragment\<close>

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


subsection \<open>The contract\<close>

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
  \<^item> No panic (the abort postcondition is false). The program
    logic does not model the exhaustion of memory or of the stack, so the contract says nothing
    about them.\<close>

end

subsection \<open>The statement over all instances with enough fuel\<close>

text \<open>The translation bounds every loop without an iteration bound and every recursion by the
  fuel \<^verbatim>\<open>urust_fuel\<close>, the last parameter of \<^locale>\<open>QFUF_ctx\<close>, and panics when it runs out.
  A statement that quantifies over the fuel is therefore made outside that locale. The
  assumptions of \<^locale>\<open>QFUF_ctx\<close> do not mention the fuel, so its instances that differ only in
  the fuel share their assumptions. The locale \<open>QFUF_heap\<close> has the parameters and assumptions of
  \<^locale>\<open>QFUF_ctx\<close> except the fuel (it repeats \<^verbatim>\<open>urust/QFUF_Locale.thy\<close> without its last
  line); each value of the fuel gives an instance of \<^locale>\<open>QFUF_ctx\<close> with the parameters of
  \<open>QFUF_heap\<close>.\<close>

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
