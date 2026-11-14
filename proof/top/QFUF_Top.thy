theory QFUF_Top
  imports "QFUF_Proof.QFUF_Proof" QFUF_SmtSize QFUF_SmtBound QFUF_SmtRefine
begin

section \<open>The top-level theorem\<close>

text \<open>\<^verbatim>\<open>check_sat\<close> satisfies \<^const>\<open>QFUF_ctx.check_sat_contract\<close> for every fuel at least
  \<open>fuel_top\<close> of the problem. The proof composes the contracts of \<^verbatim>\<open>in_fragment\<close>,
  \<^verbatim>\<open>input_size\<close>, \<^verbatim>\<open>tr_problem\<close>, \<^verbatim>\<open>solve\<close> (with the bounds on its model) and
  \<^verbatim>\<open>tr_model\<close> with the semantic correctness of the translation (\<^verbatim>\<open>QFUF_SmtModel\<close>) and the
  size bounds (\<^verbatim>\<open>QFUF_SmtBound\<close>).\<close>

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

text \<open>A fuel sufficient for every loop and recursion of \<^verbatim>\<open>check_sat\<close> on \<open>p\<close>.\<close>
definition fuel_top :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>fuel_top p \<equiv> QFUF_ctx.tr_fuel p + isize_fuel p + Suc (length (Problem_atoms (tr_problem_m p)))\<close>

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
  let ?q = \<open>tr_problem_m p\<close>
  have NF: \<open>tr_fuel p \<le> urust_fuel\<close> \<open>isize_fuel p \<le> urust_fuel\<close> \<open>length (Problem_atoms ?q) < urust_fuel\<close>
    using F by (simp_all add: fuel_top_def)
  have IP: \<open>if_pre urust_fuel p\<close> using in_fragment_pre[OF R NF(1)] .
  have US: \<open>isize_pre urust_fuel p\<close> using isize_pre_wf[OF W R NF(2)] .
  have OK: \<open>tr_bounded p \<and> sizes_ok ?q\<close> if \<open>usize_m p < 2 ^ 63\<close> using usize_tr_ok[OF that W] .
  have TP: \<open>tr_pre urust_fuel p\<close> if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
    using tr_problem_pre[OF W that(1) R conjunct1[OF OK[OF that(2)]] NF(1)] .
  have WP: \<open>wf_problem ?q \<and> sizes_ok ?q\<close> if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
    using tr_wf_problem[OF W that(1) conjunct1[OF OK[OF that(2)]]] OK[OF that(2)] by simp
  have B: \<open>isize_m p \<le> 2 ^ 28\<close> if \<open>smt_in_range p\<close> using that by (simp add: smt_in_range_def isize_smt_size)
  have MP: \<open>tm_pre urust_fuel p m\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close>
       \<open>length (Model_entries m) \<le> length (Problem_terms ?q)\<close>
       \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms ?q) \<and>
          (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms ?q)) \<and>
          (\<exists>t \<in> set (Problem_terms ?q). length (Entry_args e) \<le> length (Term_args t))\<close> for m
    using tr_model_pre[OF conjunct2[OF OK[OF that(2)]] R NF(1)] that(3,4) by blast
  have MC: \<open>smt_is_model p (tr_model_m p m)\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close> \<open>problem_true (model_interp m) ?q\<close>
       \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms ?q) \<and>
          (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms ?q)) \<and>
          (\<exists>t \<in> set (Problem_terms ?q). length (Entry_args e) \<le> length (Term_args t))\<close> for m
  proof -
    have s: \<open>length (Problem_terms ?q) < 2 ^ 63\<close> using OK[OF that(2)] by (simp add: sizes_ok_def)
    have d: \<open>domain_size_m m \<le> max 1 (length (Problem_terms ?q))\<close>
      by (rule domain_size_le) (use that(4) in auto)
    have \<open>domain_size_m m < 2 ^ 64\<close> using d s by simp
    then show ?thesis using tr_model_correct[OF W that(1) conjunct1[OF OK[OF that(2)]] that(3)] by simp
  qed
  have UC: \<open>\<not> smt_satisfiable p\<close>
    if \<open>smt_fragment p\<close> \<open>usize_m p < 2 ^ 63\<close> \<open>\<not> satisfiable ?q\<close>
    using tr_complete[OF W that(1) conjunct1[OF OK[OF that(2)]]] that(3) by blast
  show ?thesis
    apply (crush_boot f: check_sat_def contract: check_sat_contract_def)
    apply (crush_base specs add: solve_vals_spec[OF NF(3)] contracts add: solve_contract_vals_def
        simp add: IP US W R)
    subgoal for x xa xb
      apply (cases xb; crush_base)
      apply (all \<open>frule isz_le, assumption, assumption, drule isz_usize\<close>)
      using UC MC MP by auto
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
