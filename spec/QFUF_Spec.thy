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
  model, and \<^verbatim>\<open>Unknown\<close> only for a problem outside the fragment of this solver or outside
  its input range (\<open>smt_in_range\<close>).

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

definition smt_sort_no_bv :: \<open>SmtSort \<Rightarrow> bool\<close> where
  \<open>smt_sort_no_bv srt \<equiv>
     (case srt of
        SmtSort_BitVec w \<Rightarrow> False
      | _ \<Rightarrow> True)\<close>

lemma smt_sort_no_bv_simps [simp]:
  \<open>smt_sort_no_bv (SmtSort_BitVec w) = False\<close>
  \<open>smt_sort_no_bv SmtSort_Bool = True\<close>
  \<open>smt_sort_no_bv (SmtSort_Uninterpreted a0) = True\<close>
  by (simp_all add: smt_sort_no_bv_def)

text \<open>The theory functions of Core.\<close>
definition smt_core_op :: \<open>SmtOp \<Rightarrow> bool\<close> where
  \<open>smt_core_op op \<equiv>
     (case op of
        SmtOp_Not \<Rightarrow> True
      | SmtOp_And \<Rightarrow> True
      | SmtOp_Or \<Rightarrow> True
      | SmtOp_Xor \<Rightarrow> True
      | SmtOp_Implies \<Rightarrow> True
      | SmtOp_Eq \<Rightarrow> True
      | SmtOp_Distinct \<Rightarrow> True
      | SmtOp_Ite \<Rightarrow> True
      | _ \<Rightarrow> False)\<close>

lemma smt_core_op_simps [simp]:
  \<open>smt_core_op SmtOp_Not = True\<close>
  \<open>smt_core_op SmtOp_And = True\<close>
  \<open>smt_core_op SmtOp_Or = True\<close>
  \<open>smt_core_op SmtOp_Xor = True\<close>
  \<open>smt_core_op SmtOp_Implies = True\<close>
  \<open>smt_core_op SmtOp_Eq = True\<close>
  \<open>smt_core_op SmtOp_Distinct = True\<close>
  \<open>smt_core_op SmtOp_Ite = True\<close>
  \<open>smt_core_op SmtOp_Concat = False\<close>
  \<open>smt_core_op (SmtOp_Extract a0 a1) = False\<close>
  \<open>smt_core_op SmtOp_Bvnot = False\<close>
  \<open>smt_core_op SmtOp_Bvand = False\<close>
  \<open>smt_core_op SmtOp_Bvor = False\<close>
  \<open>smt_core_op SmtOp_Bvneg = False\<close>
  \<open>smt_core_op SmtOp_Bvadd = False\<close>
  \<open>smt_core_op SmtOp_Bvmul = False\<close>
  \<open>smt_core_op SmtOp_Bvudiv = False\<close>
  \<open>smt_core_op SmtOp_Bvurem = False\<close>
  \<open>smt_core_op SmtOp_Bvshl = False\<close>
  \<open>smt_core_op SmtOp_Bvlshr = False\<close>
  \<open>smt_core_op SmtOp_Bvult = False\<close>
  \<open>smt_core_op SmtOp_Bvnand = False\<close>
  \<open>smt_core_op SmtOp_Bvnor = False\<close>
  \<open>smt_core_op SmtOp_Bvxor = False\<close>
  \<open>smt_core_op SmtOp_Bvxnor = False\<close>
  \<open>smt_core_op SmtOp_Bvcomp = False\<close>
  \<open>smt_core_op SmtOp_Bvsub = False\<close>
  \<open>smt_core_op SmtOp_Bvsdiv = False\<close>
  \<open>smt_core_op SmtOp_Bvsrem = False\<close>
  \<open>smt_core_op SmtOp_Bvsmod = False\<close>
  \<open>smt_core_op SmtOp_Bvashr = False\<close>
  \<open>smt_core_op (SmtOp_Repeat a0) = False\<close>
  \<open>smt_core_op (SmtOp_ZeroExtend a0) = False\<close>
  \<open>smt_core_op (SmtOp_SignExtend a0) = False\<close>
  \<open>smt_core_op (SmtOp_RotateLeft a0) = False\<close>
  \<open>smt_core_op (SmtOp_RotateRight a0) = False\<close>
  \<open>smt_core_op SmtOp_Bvule = False\<close>
  \<open>smt_core_op SmtOp_Bvugt = False\<close>
  \<open>smt_core_op SmtOp_Bvuge = False\<close>
  \<open>smt_core_op SmtOp_Bvslt = False\<close>
  \<open>smt_core_op SmtOp_Bvsle = False\<close>
  \<open>smt_core_op SmtOp_Bvsgt = False\<close>
  \<open>smt_core_op SmtOp_Bvsge = False\<close>
  by (simp_all add: smt_core_op_def)

text \<open>No bit-vector constant or function occurs in a term.\<close>
fun smt_term_no_bv :: \<open>SmtTerm \<Rightarrow> bool\<close> where
  \<open>smt_term_no_bv (SmtTerm_BoolConst b) = True\<close>
| \<open>smt_term_no_bv (SmtTerm_BvConst bs) = False\<close>
| \<open>smt_term_no_bv (SmtTerm_Param k) = True\<close>
| \<open>smt_term_no_bv (SmtTerm_Fun f args) = (\<forall>a \<in> set (rvec_elems args). smt_term_no_bv a)\<close>
| \<open>smt_term_no_bv (SmtTerm_Def d args) = (\<forall>a \<in> set (rvec_elems args). smt_term_no_bv a)\<close>
| \<open>smt_term_no_bv (SmtTerm_App op args) = (smt_core_op op \<and> (\<forall>a \<in> set (rvec_elems args). smt_term_no_bv a))\<close>

text \<open>The fragment of this solver: no bit-vector sort, constant or function occurs in the problem.\<close>
definition smt_fragment :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_fragment p \<equiv>
     (\<forall>f \<in> set (rvec_elems (SmtProblem_funs p)).
        (\<forall>s \<in> set (rvec_elems (SmtFun_args f)). smt_sort_no_bv s) \<and> smt_sort_no_bv (SmtFun_ret f)) \<and>
     (\<forall>d \<in> set (rvec_elems (SmtProblem_defs p)). (\<forall>s \<in> set (rvec_elems (SmtDef_params d)). smt_sort_no_bv s) \<and>
        smt_sort_no_bv (SmtDef_ret d) \<and> smt_term_no_bv (SmtDef_body d)) \<and>
     (\<forall>t \<in> set (rvec_elems (SmtProblem_asserts p)). smt_term_no_bv t)\<close>


subsection \<open>The input range\<close>

text \<open>The problems on which this solver promises an answer other than \<^verbatim>\<open>Unknown\<close> (besides
  being in its fragment). The range is part of the specification and fixed: it is stated with the
  measures of \<^verbatim>\<open>SMT_Semantics\<close>, which describe the problem as written, and does not depend on
  how the solver works. A change of the solver must keep answering every problem of the range.
  The range of this solver: \<^const>\<open>smt_size\<close> at most \<open>2^28\<close> (about \<open>2.7 \<cdot> 10^8\<close>).
  The largest QF\_UF problem of the SMT-LIB 2025 release has size about \<open>1.5 \<cdot> 10^6\<close>.\<close>
definition smt_in_range :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_in_range p \<equiv> smt_size p \<le> 2 ^ 28\<close>

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
         | SmtAnswer_Unknown \<Rightarrow> \<not> smt_fragment p \<or> \<not> smt_in_range p\<rangle> in
     make_function_contract pre post\<close>

text \<open>\<^const>\<open>check_sat_contract\<close> \<open>p\<close>:
  \<^item> Precondition: \<open>p\<close> is well-sorted (\<^const>\<open>smt_wf\<close>), and every \<^verbatim>\<open>Vec\<close> in it has fewer
    than \<open>2^63\<close> elements (\<^const>\<open>smt_repr_ok\<close>, which holds for every value of a Rust program).
  \<^item> \<^verbatim>\<open>Sat(m)\<close>: \<open>m\<close> is a model of \<open>p\<close>. \<^verbatim>\<open>Unsat\<close>: \<open>p\<close> has no model. \<^verbatim>\<open>Unknown\<close>: \<open>p\<close> is not in
    the fragment of this solver, or not in its range (\<^const>\<open>smt_in_range\<close>). For a problem in
    the fragment and in the range the answer is \<^verbatim>\<open>Sat\<close> or \<^verbatim>\<open>Unsat\<close>.
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
  \<open>QFUF_heap\<close>. The abbreviation \<open>check_sat\<close> below passes to \<^verbatim>\<open>QFUF_ctx.check_sat\<close> the prisms
  of the locale that this function takes, in order. Like the locale, this list follows the
  implementation (\<^verbatim>\<open>tools/check-spec.sh\<close> checks its form, type checking that it is the
  function's list); the contract is stated on the input and output types only.\<close>

locale QFUF_heap =
  reference reference_types
  + ref_1: reference_allocatable reference_types _ _ _ _ _ _ _ prism_1 \<comment> \<open>bool\<close>
  + ref_2: reference_allocatable reference_types _ _ _ _ _ _ _ prism_2 \<comment> \<open>(64 word) rvec\<close>
  + ref_3: reference_allocatable reference_types _ _ _ _ _ _ _ prism_3 \<comment> \<open>Entry rvec\<close>
  + ref_4: reference_allocatable reference_types _ _ _ _ _ _ _ prism_4 \<comment> \<open>bool rvec\<close>
  + ref_5: reference_allocatable reference_types _ _ _ _ _ _ _ prism_5 \<comment> \<open>Term rvec\<close>
  + ref_6: reference_allocatable reference_types _ _ _ _ _ _ _ prism_6 \<comment> \<open>Atom rvec\<close>
  + ref_7: reference_allocatable reference_types _ _ _ _ _ _ _ prism_7 \<comment> \<open>Clause rvec\<close>
  + ref_8: reference_allocatable reference_types _ _ _ _ _ _ _ prism_8 \<comment> \<open>Tr\<close>
  + ref_9: reference_allocatable reference_types _ _ _ _ _ _ _ prism_9 \<comment> \<open>Lit rvec\<close>
  + ref_10: reference_allocatable reference_types _ _ _ _ _ _ _ prism_10 \<comment> \<open>64 word\<close>
  + ref_11: reference_allocatable reference_types _ _ _ _ _ _ _ prism_11 \<comment> \<open>((64 word) \<times> bool \<times> tnil) rvec\<close>
  + ref_12: reference_allocatable reference_types _ _ _ _ _ _ _ prism_12 \<comment> \<open>((64 word) \<times> bool \<times> tnil)\<close>
  + ref_13: reference_allocatable reference_types _ _ _ _ _ _ _ prism_13 \<comment> \<open>Enc rvec\<close>
  + ref_14: reference_allocatable reference_types _ _ _ _ _ _ _ prism_14 \<comment> \<open>SmtEntry rvec\<close>
  + ref_15: reference_allocatable reference_types _ _ _ _ _ _ _ prism_15 \<comment> \<open>SmtValue rvec\<close>
  + ref_16: reference_allocatable reference_types _ _ _ _ _ _ _ prism_16 \<comment> \<open>SmtInterp rvec\<close>
  + ref_17: reference_allocatable reference_types _ _ _ _ _ _ _ prism_17 \<comment> \<open>SmtTerm rvec\<close>
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and prism_1 :: \<open>('gv, bool) prism\<close>
  and prism_2 :: \<open>('gv, (64 word) rvec) prism\<close>
  and prism_3 :: \<open>('gv, Entry rvec) prism\<close>
  and prism_4 :: \<open>('gv, bool rvec) prism\<close>
  and prism_5 :: \<open>('gv, Term rvec) prism\<close>
  and prism_6 :: \<open>('gv, Atom rvec) prism\<close>
  and prism_7 :: \<open>('gv, Clause rvec) prism\<close>
  and prism_8 :: \<open>('gv, Tr) prism\<close>
  and prism_9 :: \<open>('gv, Lit rvec) prism\<close>
  and prism_10 :: \<open>('gv, 64 word) prism\<close>
  and prism_11 :: \<open>('gv, ((64 word) \<times> bool \<times> tnil) rvec) prism\<close>
  and prism_12 :: \<open>('gv, ((64 word) \<times> bool \<times> tnil)) prism\<close>
  and prism_13 :: \<open>('gv, Enc rvec) prism\<close>
  and prism_14 :: \<open>('gv, SmtEntry rvec) prism\<close>
  and prism_15 :: \<open>('gv, SmtValue rvec) prism\<close>
  and prism_16 :: \<open>('gv, SmtInterp rvec) prism\<close>
  and prism_17 :: \<open>('gv, SmtTerm rvec) prism\<close>
begin

abbreviation check_sat :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> ('s, SmtAnswer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>check_sat fuel \<equiv>
     QFUF_ctx.check_sat update_raw_fun dereference_raw_fun reference_raw_fun
       prism_1 prism_2 prism_3 prism_4 prism_5 prism_6 prism_7 prism_8 prism_9 prism_10 prism_11 prism_12
       prism_13 prism_14 prism_15 prism_16 prism_17 fuel\<close>

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
