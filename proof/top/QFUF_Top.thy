theory QFUF_Top
  imports "QFUF_Proof.QFUF_Proof" QFUF_SmtSize QFUF_SmtBound QFUF_SmtRefine QFUF_ElimRefine
begin

section \<open>The top-level theorem\<close>

text \<open>\<^verbatim>\<open>check_sat\<close> satisfies \<^const>\<open>QFUF_ctx.check_sat_contract\<close> for every fuel at least
  \<open>fuel_top\<close> of the problem. The proof composes the contracts of \<^verbatim>\<open>in_fragment\<close>,
  \<^verbatim>\<open>input_size\<close>, \<^verbatim>\<open>eliminate\<close>, \<^verbatim>\<open>tr_problem\<close>, \<^verbatim>\<open>solve\<close> (with the bounds on its
  model), \<^verbatim>\<open>tr_model\<close> and \<^verbatim>\<open>restore\<close> with the semantic correctness of the translation
  (\<^verbatim>\<open>QFUF_SmtModel\<close>) and of the equality elimination (\<^verbatim>\<open>QFUF_ElimSem\<close>), and the size bounds
  (\<^verbatim>\<open>QFUF_SmtBound\<close>). The problem after elimination, \<open>elim_q\<close>, is the one translated.\<close>

lemma dsize_step_le: \<open>n \<le> B \<Longrightarrow> unat x < B \<Longrightarrow> dsize_step n x \<le> B\<close>
  by (simp add: dsize_step_def)

lemma foldl_dsize_le: \<open>n \<le> B \<Longrightarrow> \<forall>x \<in> set xs. unat x < B \<Longrightarrow> foldl dsize_step n xs \<le> B\<close>
  by (induction xs arbitrary: n) (auto simp: dsize_step_le)

lemma domain_size_le:
  assumes \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < B \<and> (\<forall>a \<in> set (Entry_args e). unat a < B)\<close> \<open>1 \<le> B\<close>
  shows \<open>domain_size_m m \<le> B\<close>
proof -
  have \<open>foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) n es \<le> B\<close>
    if \<open>n \<le> B\<close> \<open>set es \<subseteq> set (Model_entries m)\<close> for n es
    using that
  proof (induction es arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons e es)
    have e: \<open>unat (Entry_val e) < B\<close> \<open>\<forall>a \<in> set (Entry_args e). unat a < B\<close>
      using assms(1) Cons.prems(2) by auto
    have \<open>foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e) \<le> B\<close>
      by (rule foldl_dsize_le[OF dsize_step_le[OF Cons.prems(1) e(1)] e(2)])
    then show ?case using Cons.IH Cons.prems(2) by simp
  qed
  then show ?thesis using assms(2) by (simp add: domain_size_m_def)
qed

lemma isz_le:
  fixes x xa :: \<open>64 word\<close>
  shows \<open>unat x = sat T \<Longrightarrow> unat xa = 268435456 \<Longrightarrow> \<not> xa < x \<Longrightarrow> T \<le> 2 ^ 28\<close>
  by (simp add: word_less_nat_alt sat_def min_def split: if_splits)

lemma isz_gt:
  fixes x xa :: \<open>64 word\<close>
  shows \<open>unat x = sat T \<Longrightarrow> unat xa = 268435456 \<Longrightarrow> xa < x \<Longrightarrow> \<not> T \<le> 2 ^ 28\<close>
  by (simp add: word_less_nat_alt sat_def min_def split: if_splits)

lemma isz_usize: \<open>isize_m p \<le> 2 ^ 28 \<Longrightarrow> usize_m p < 2 ^ 63\<close>
  using in_range_usize[of p] by (simp add: isize_smt_size)

text \<open>The problem after equality elimination.\<close>
definition elim_q :: \<open>SmtProblem \<Rightarrow> SmtProblem\<close> where
  \<open>elim_q p \<equiv> wa p (fst (eliminate_m p))\<close>

text \<open>A fuel sufficient for every loop and recursion of \<^verbatim>\<open>check_sat\<close> on \<open>p\<close>.\<close>
definition fuel_top :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>fuel_top p \<equiv> QFUF_ctx.tr_fuel p + QFUF_ctx.tr_fuel (elim_q p) + isize_fuel p +
     Suc (length (Problem_atoms (tr_problem_m (elim_q p))))\<close>

lemma isize_fuel_ge:
  \<open>Suc (size_list size (SmtProblem_asserts p)) \<le> isize_fuel p\<close>
  \<open>d \<in> set (SmtProblem_defs p) \<Longrightarrow> Suc (size (SmtDef_body d)) \<le> isize_fuel p\<close>
proof -
  show \<open>Suc (size_list size (SmtProblem_asserts p)) \<le> isize_fuel p\<close>
    by (simp add: isize_fuel_def size_list_conv_sum_list)
  show \<open>d \<in> set (SmtProblem_defs p) \<Longrightarrow> Suc (size (SmtDef_body d)) \<le> isize_fuel p\<close>
    using member_le_sum_list[of \<open>size (SmtDef_body d)\<close> \<open>map (\<lambda>e. size (SmtDef_body e)) (SmtProblem_defs p)\<close>]
    by (auto simp: isize_fuel_def)
qed

context QFUF_ctx
begin

lemma check_sat_spec:
  assumes F: \<open>fuel_top p \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; check_sat p \<Turnstile>\<^sub>F check_sat_contract p\<close>
proof (cases \<open>smt_wf p \<and> smt_repr_ok p\<close>)
  case False
  then show ?thesis
    apply -
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (auto simp add: check_sat_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case True
  then have W: \<open>smt_wf p\<close> and R: \<open>smt_repr_ok p\<close> by simp_all
  obtain a cs gs where E: \<open>eliminate_m p = (a, cs, gs)\<close> by (cases \<open>eliminate_m p\<close>) auto
  let ?q = \<open>wa p a\<close>
  have q: \<open>elim_q p = ?q\<close> by (simp add: elim_q_def E)
  note EC = eliminate_correct[OF R E]
  have Wq: \<open>smt_wf ?q\<close> and Rq: \<open>smt_repr_ok ?q\<close> using EC W by simp_all
  have NF: \<open>tr_fuel p \<le> urust_fuel\<close> \<open>tr_fuel ?q \<le> urust_fuel\<close> \<open>isize_fuel p \<le> urust_fuel\<close>
    \<open>length (Problem_atoms (tr_problem_m ?q)) < urust_fuel\<close>
    using F by (simp_all add: fuel_top_def q)
  have IP: \<open>if_pre urust_fuel p\<close> using in_fragment_pre[OF R NF(1)] .
  have US: \<open>isize_pre urust_fuel p\<close> using isize_pre_wf[OF W R NF(3)] .
  have EP: \<open>elim_pre p\<close>
    using R NF(3) isize_fuel_ge(1)[of p] isize_fuel_ge(2)[where p=p] by (fastforce simp: elim_pre_def)
  have LE: \<open>length cs < 2 ^ 64\<close> \<open>length gs < 2 ^ 64\<close>
    using eliminate_lengths[OF E] R by (auto simp: smt_repr_ok_def)
  have OK: \<open>tr_bounded ?q \<and> sizes_ok (tr_problem_m ?q)\<close> if \<open>usize_m p < 2 ^ 63\<close>
    using usize_tr_ok[OF _ Wq] that EC(4) by simp
  have TP: \<open>tr_pre urust_fuel ?q\<close> if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
    using tr_problem_pre[OF Wq _ Rq conjunct1[OF OK[OF that(2)]] NF(2)] that(1) EC(3) by simp
  have WP: \<open>wf_problem (tr_problem_m ?q) \<and> sizes_ok (tr_problem_m ?q)\<close> if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
    using tr_wf_problem[OF Wq _ conjunct1[OF OK[OF that(2)]]] OK[OF that(2)] that(1) EC(3) by simp
  have B: \<open>isize_m p \<le> 2 ^ 28\<close> if \<open>smt_in_range p\<close> using that by (simp add: smt_in_range_def isize_smt_size)
  have MP: \<open>tm_pre urust_fuel ?q m\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
       \<open>length (Model_entries m) \<le> length (Problem_terms (tr_problem_m ?q))\<close>
       \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms (tr_problem_m ?q)) \<and>
          (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms (tr_problem_m ?q))) \<and>
          (\<exists>t \<in> set (Problem_terms (tr_problem_m ?q)). length (Entry_args e) \<le> length (Term_args t))\<close> for m
    using tr_model_pre[OF conjunct2[OF OK[OF that(2)]] Rq NF(2)] that(3,4) by blast
  have MC: \<open>smt_is_model ?q (tr_model_m ?q m)\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close> \<open>problem_true (model_interp m) (tr_problem_m ?q)\<close>
       \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms (tr_problem_m ?q)) \<and>
          (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms (tr_problem_m ?q))) \<and>
          (\<exists>t \<in> set (Problem_terms (tr_problem_m ?q)). length (Entry_args e) \<le> length (Term_args t))\<close> for m
  proof -
    have s: \<open>length (Problem_terms (tr_problem_m ?q)) < 2 ^ 63\<close> using OK[OF that(2)] by (simp add: sizes_ok_def)
    have d: \<open>domain_size_m m \<le> max 1 (length (Problem_terms (tr_problem_m ?q)))\<close>
      by (rule domain_size_le) (use that(4) in auto)
    have \<open>domain_size_m m < 2 ^ 64\<close> using d s by simp
    then show ?thesis using tr_model_correct[OF Wq _ conjunct1[OF OK[OF that(2)]] that(3)] that(1) EC(3) by simp
  qed
  have MR: \<open>smt_is_model p (restore_m M cs gs) \<and> length (SmtModel_funs M) < 2 ^ 64\<close> if \<open>smt_is_model ?q M\<close> for M
    using EC(8)[OF that] that R by (auto simp: smt_is_model_def smt_model_wf_def Let_def smt_repr_ok_def)
  have UC: \<open>\<not> smt_satisfiable p\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close> \<open>\<not> satisfiable (tr_problem_m ?q)\<close>
    using tr_complete[OF Wq _ conjunct1[OF OK[OF that(2)]]] that(1,3) EC(3,7) by auto
  show ?thesis
    apply (crush_boot f: check_sat_def contract: check_sat_contract_def)
    apply (crush_base specs add: solve_vals_spec[OF NF(4)] contracts add: solve_contract_vals_def
        simp add: IP US W R EP E LE wa_def[symmetric])
    subgoal for x xa xc
      apply (cases xc; crush_base simp add: LE)
      apply (all \<open>frule isz_le, assumption, assumption, drule isz_usize\<close>)
      using UC MC MP MR[OF MC] LE by auto
    subgoal using WP isz_le isz_usize by blast
    subgoal using WP isz_le isz_usize by blast
    subgoal using TP isz_le isz_usize by blast
    subgoal using B isz_gt by blast
    done
qed

end

subsection \<open>The statement over all instances with enough fuel\<close>

context QFUF_heap
begin

theorem check_sat_correct:
  shows \<open>check_sat_correct \<Gamma>\<close>
proof (unfold check_sat_correct_def, intro allI impI)
  fix p :: SmtProblem
  assume \<open>smt_wf p \<and> smt_repr_ok p\<close>
  have \<open>\<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p\<close> if \<open>fuel_top p \<le> fuel\<close> for fuel
    by (rule QFUF_ctx.check_sat_spec[OF QFUF_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; check_sat fuel p \<Turnstile>\<^sub>F check_sat_contract p\<close>
    by (intro exI[of _ \<open>fuel_top p\<close>]) simp
qed

end

end
