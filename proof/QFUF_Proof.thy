theory QFUF_Proof
  imports QFUF_Analyze
begin

context QFUF_ctx
begin

subsection \<open>Search\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>search\<close>. Its precondition requires fewer than \<open>k\<close> atoms
  to be unset, so the innermost function is never called. The learned clauses \<open>l\<close> hold in every
  model of the problem, before and after.\<close>
definition search_contract :: \<open>nat \<Rightarrow> Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('s, Model option \<times> Clause list \<times> tnil, 'abort) function_contract\<close> where
  \<open>search_contract k p l t f \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and>
         length f = length (Problem_atoms p) \<and> unset_count t f < k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>(case fst r of
           None \<Rightarrow> \<not> pext p t f
         | Some m \<Rightarrow> problem_true (model_interp m) p \<and> model_vals_ok p m) \<and>
         clauses_ok p (fst (snd r))\<rangle> in
     make_function_contract pre post\<close>

lemma find_result_le:
  \<open>find_result p t f r \<Longrightarrow> unat (Lit_atom r) \<le> length t\<close>
  unfolding find_result_def by simp

text \<open>The facts of \<^verbatim>\<open>QFUF_Contracts\<close> for the steps of the search, in the form of the goals
  that \<open>crush_base\<close> leaves.\<close>

lemma step_unit_none:
  \<open>find_result p t f x \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom x) < length (Problem_atoms p) \<Longrightarrow> Lit_pos x \<Longrightarrow>
   \<not> pext p (t[unat (Lit_atom x) := True]) f \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>find_result p t f x \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom x) < length (Problem_atoms p) \<Longrightarrow> \<not> Lit_pos x \<Longrightarrow>
   \<not> pext p t (f[unat (Lit_atom x) := True]) \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  using search_unit_none by fastforce+

lemma step_unit_fuel:
  \<open>find_result p t f x \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom x) < length (Problem_atoms p) \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count (t[unat (Lit_atom x) := True]) f < k\<close>
  \<open>find_result p t f x \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom x) < length (Problem_atoms p) \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count t (f[unat (Lit_atom x) := True]) < k\<close>
  using search_unit_fuel[of p t f x k] by simp_all

lemma step_branch_fuel:
  \<open>length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat j \<le> length (Problem_atoms p) \<Longrightarrow> unat j \<noteq> length (Problem_atoms p) \<Longrightarrow>
   \<not> t ! unat j \<Longrightarrow> \<not> f ! unat j \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count (t[unat j := True]) f < k\<close>
  \<open>length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat j \<le> length (Problem_atoms p) \<Longrightarrow> unat j \<noteq> length (Problem_atoms p) \<Longrightarrow>
   \<not> t ! unat j \<Longrightarrow> \<not> f ! unat j \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count t (f[unat j := True]) < k\<close>
  using search_branch_fuel[of \<open>unat j\<close> t f k] by simp_all

lemma step_leaf:
  \<open>wf_problem p \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow> \<forall>j < length (Problem_atoms p). t ! j \<or> f ! j \<Longrightarrow>
   \<not> prop_true p t \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>length t = length (Problem_atoms p) \<Longrightarrow> \<forall>j < length (Problem_atoms p). t ! j \<or> f ! j \<Longrightarrow>
   \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. atom_vals I p \<noteq> t \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  using search_leaf_none search_leaf_theory_none by fastforce+

text \<open>A closure conflict: the cut, and the learned clause.\<close>

lemma step_learn:
  assumes \<open>set (Clause_lits cl) = conflict_lits e c (length (Problem_atoms p))\<close>
      and \<open>wf_problem p\<close> \<open>length (Problem_atoms p) < 9223372036854775808\<close> \<open>clauses_ok p l\<close>
      and \<open>unat c < length (Problem_atoms p)\<close> \<open>length e = length (Problem_atoms p)\<close>
      and \<open>(unat (Atom_lhs (Problem_atoms p ! unat c)), unat (Atom_rhs (Problem_atoms p ! unat c)))
             \<in> cc p (asserted p e (length (Problem_atoms p)))\<close>
      and \<open>length (Clause_lits cl) \<le> Suc (length (Problem_atoms p))\<close>
  shows \<open>clauses_ok p (l @ [cl])\<close>
proof (rule clauses_ok_append[OF assms(4)])
  show \<open>clause_ok p cl\<close>
    using assms by (intro conflict_lits_clause_ok[where e=e and k=c]) auto
  show \<open>length (Clause_lits cl) < 2^64\<close>
    using assms(3,8) by simp
qed

lemma step_conflict:
  \<open>conflict_result p t f a \<Longrightarrow> wf_problem p \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow>
   unat a < length (Problem_atoms p) \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>conflict_result p t f a \<Longrightarrow> unat a < length (Problem_atoms p) \<Longrightarrow>
   (unat (Atom_lhs (Problem_atoms p ! unat a)), unat (Atom_rhs (Problem_atoms p ! unat a)))
     \<in> cc p (asserted p t (length (Problem_atoms p)))\<close>
  using conflict_result_none unfolding conflict_result_def by blast+

lemma step_falsified:
  \<open>find_result p t f x \<Longrightarrow> length t = n \<Longrightarrow> unat (Lit_atom x) = n \<Longrightarrow> Lit_pos x \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  unfolding find_result_def by simp

text \<open>Theory propagation: the recursive call on the extended assignment \<open>t2\<close>, \<open>f2\<close>.\<close>

lemma step_implied:
  \<open>implied_ok p t f rs t2 f2 \<Longrightarrow> wf_problem p \<Longrightarrow> length t = length (Problem_atoms p) \<Longrightarrow>
   \<not> pext p t2 f2 \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>implied_ok p t f rs t2 f2 \<Longrightarrow> length t = n \<Longrightarrow> length t2 = n\<close>
  \<open>implied_ok p t f rs t2 f2 \<Longrightarrow> length f = n \<Longrightarrow> length f2 = n\<close>
  using pext_implied unfolding implied_ok_def by blast+

lemma step_implied_fuel:
  \<open>implied_ok p t f rs t2 f2 \<Longrightarrow> length t = n \<Longrightarrow> length f = n \<Longrightarrow> t2 \<noteq> t \<Longrightarrow>
   unset_count t f < Suc k \<Longrightarrow> unset_count t2 f2 < k\<close>
  \<open>implied_ok p t f rs t2 f2 \<Longrightarrow> length t = n \<Longrightarrow> length f = n \<Longrightarrow> f2 \<noteq> f \<Longrightarrow>
   unset_count t f < Suc k \<Longrightarrow> unset_count t2 f2 < k\<close>
  using implied_fuel by fastforce+

lemma step_branch_none:
  \<open>\<not> pext p (t[j := True]) f \<Longrightarrow> \<not> pext p t (f[j := True]) \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  using search_branch_none by blast

lemma step_leaf_some:
  \<open>wf_problem p \<Longrightarrow> prop_true p (atom_vals I p) \<Longrightarrow> problem_true I p\<close>
  using search_leaf_some by blast

lemma search_rec_step_spec:
  assumes \<open>\<And>l t f. \<Gamma>; R p l t f \<Turnstile>\<^sub>F search_contract k p l t f\<close>
  shows \<open>\<Gamma>; search_rec_step R p l t f \<Turnstile>\<^sub>F search_contract (Suc k) p l t f\<close>
  apply (crush_boot f: search_rec_step_def contract: search_contract_def)
  apply (crush_base specs add: assms prop_holds_spec theory_check_spec next_unit_spec cc_propagate_spec
        differs_spec explain_spec conflict_clause_spec learn_spec first_unset_spec
      contracts add: search_contract_def prop_holds_contract_def theory_check_contract_def
        next_unit_contract_def cc_propagate_contract_def differs_contract_def explain_contract_def
        conflict_clause_contract_def learn_contract_def first_unset_contract_def
      simp add: unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq word64_eq_of_nat_iff)
  apply (auto simp add: word_less_nat_alt unat_of_nat_lt63 Option.is_none_def split: option.splits
      dest: find_result_le)
  apply ((rule step_unit_none step_unit_fuel step_branch_none step_branch_fuel step_leaf step_leaf_some
        step_implied step_implied_fuel step_learn step_conflict step_falsified wf_lit; assumption)+)
  done

lemma search_rec_spec:
  shows \<open>\<Gamma>; (search_rec_step ^^ k) R p l t f \<Turnstile>\<^sub>F search_contract k p l t f\<close>
proof (induction k arbitrary: l t f)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: search_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule search_rec_step_spec) (rule Suc.IH)
qed

lemma search_spec:
  shows \<open>\<Gamma>; search p l t f \<Turnstile>\<^sub>F search_contract urust_fuel p l t f\<close>
  unfolding search_def by (rule search_rec_spec)

subsection \<open>The top-level contract\<close>

lemma unset_count_replicate:
  \<open>unset_count (replicate n False) (replicate n False) = n\<close>
proof -
  have \<open>{j. j < length (replicate n False) \<and> \<not> replicate n False ! j \<and> \<not> replicate n False ! j} = {..<n}\<close>
    by auto
  then show ?thesis unfolding unset_count_def by simp
qed

lemma solve_spec:
  assumes fuel: \<open>length (Problem_atoms p) < urust_fuel\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
  apply (crush_boot f: solve_def contract: solve_contract_def)
  apply (crush_base specs add: search_spec contracts add: search_contract_def split!: option.splits
      simp add: fuel unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq pext_start unset_count_replicate Answer_Sat_mk_def
        clauses_ok_def)
  done

text \<open>The contract of \<^verbatim>\<open>solve\<close> with, for a model, the bound on its values and arguments.\<close>
definition solve_contract_vals :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract_vals p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> problem_true (model_interp m) p \<and>
             length (Model_entries m) \<le> length (Problem_terms p) \<and>
             (\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms p) \<and>
                (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms p)) \<and>
                (\<exists>t \<in> set (Problem_terms p). length (Entry_args e) \<le> length (Term_args t)))
         | Answer_Unsat \<Rightarrow> \<not> satisfiable p\<rangle> in
     make_function_contract pre post\<close>

lemma solve_vals_spec:
  assumes fuel: \<open>length (Problem_atoms p) < urust_fuel\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract_vals p\<close>
  apply (crush_boot f: solve_def contract: solve_contract_vals_def)
  apply (crush_base specs add: search_spec contracts add: search_contract_def split!: option.splits
      simp add: fuel unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq pext_start unset_count_replicate Answer_Sat_mk_def
        clauses_ok_def)
  apply (auto simp add: model_vals_ok_def)?
  done

text \<open>\<open>solve_spec\<close> needs fewer atoms than fuel: \<^verbatim>\<open>search\<close> is called with
  \<open>k = 0, 1, \<dots>, n\<close> for \<open>n\<close> atoms, so the calls are nested \<open>n + 1\<close> deep.\<close>

end

subsection \<open>The specification\<close>

context QFUF_heap
begin

lemma QFUF_ctxI:
  \<open>QFUF_ctx update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
     new_gref_can_store can_alloc_reference prism_1 prism_2 prism_3 prism_4 prism_5 prism_6 prism_7 prism_8
     prism_9 prism_10 prism_11 prism_12 prism_13 prism_14 prism_15 prism_16\<close>
  by intro_locales

text \<open>\<^verbatim>\<open>QFUF_heap\<close> has the assumptions of \<^locale>\<open>QFUF_ctx\<close>, so its parameters with any fuel
  form an instance of \<^locale>\<open>QFUF_ctx\<close>, and the contract lemmas of \<^locale>\<open>QFUF_ctx\<close> apply.\<close>

text \<open>The statement of the specification, \<^const>\<open>solve_correct\<close> in \<^verbatim>\<open>QFUF_Spec\<close>. The bound
  is \<open>length (Problem_atoms p) + 1\<close>, the fuel that \<open>QFUF_ctx.solve_spec\<close> needs.\<close>
theorem solve_correct:
  shows \<open>solve_correct \<Gamma>\<close>
proof (unfold solve_correct_def, intro allI impI)
  fix p
  have \<open>\<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close> if \<open>length (Problem_atoms p) < fuel\<close> for fuel
    by (rule QFUF_ctx.solve_spec[OF QFUF_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F solve_contract p\<close>
    by (intro exI[of _ \<open>length (Problem_atoms p) + 1\<close>]) simp
qed

end

end
