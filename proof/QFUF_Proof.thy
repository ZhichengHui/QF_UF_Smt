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

subsection \<open>The search with conflict analysis and backjumping\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>cdcl\<close> at decision level \<open>d\<close>. Without a model, the result
  level \<open>j\<close> says whether the branch is refuted (\<open>d \<le> j\<close>: no completion of \<open>t\<close>, \<open>f\<close> is a model)
  or the search jumps back to level \<open>j < d\<close>, which claims nothing. The levels, reasons and time
  stamps only guide the analysis, so the contract does not mention them. The fallback to
  \<^const>\<open>search\<close> needs fewer atoms than fuel.\<close>
definition cdcl_contract :: \<open>nat \<Rightarrow> Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow>
      ('s, Model option \<times> Clause list \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  \<open>cdcl_contract k p l t f d \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and>
         length f = length (Problem_atoms p) \<and> unset_count t f < k \<and> length (Problem_atoms p) < urust_fuel\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>(case fst r of
           None \<Rightarrow> d \<le> fst (snd (snd r)) \<longrightarrow> \<not> pext p t f
         | Some m \<Rightarrow> problem_true (model_interp m) p \<and> model_vals_ok p m) \<and>
         clauses_ok p (fst (snd r))\<rangle> in
     make_function_contract pre post\<close>

text \<open>A jump to the level of the decision: the last learned clause is unit or false there. The
  index \<open>len(l) - 1\<close> is in bounds even if the length of \<open>l\<close> does not fit a word.\<close>
lemma last_idx_lt:
  assumes h: \<open>0 < unat (word_of_nat n :: 64 word)\<close>
  shows \<open>unat (word_of_nat n - 1 :: 64 word) < n\<close>
proof -
  have \<open>(word_of_nat n :: 64 word) \<noteq> 0\<close> using h by auto
  then have \<open>unat (word_of_nat n - 1 :: 64 word) = unat (word_of_nat n :: 64 word) - 1\<close> by (rule unat_minus_one)
  then show ?thesis using h unat_of_nat_le[of n] by linarith
qed

lemma last_idx_one:
  \<open>0 < unat (w :: 64 word) \<Longrightarrow> 1 \<le> w\<close>
  by (simp add: word_le_nat_alt)

lemma step_last_find:
  assumes \<open>clauses_ok p l\<close> \<open>0 < unat (word_of_nat (length l) :: 64 word)\<close>
      and \<open>unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u\<close>
      and \<open>length t = length (Problem_atoms p)\<close> \<open>length f = length (Problem_atoms p)\<close>
  shows \<open>find_result p t f u\<close>
  using assms last_idx_lt[OF assms(2)]
  by (intro find_result_clause[where c=\<open>l ! unat (word_of_nat (length l) - 1 :: 64 word)\<close>])
    (auto simp add: clauses_ok_def)

lemma step_last_none:
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u \<Longrightarrow>
   length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom u) < length (Problem_atoms p) \<Longrightarrow> Lit_pos u \<Longrightarrow>
   \<not> pext p (t[unat (Lit_atom u) := True]) f \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u \<Longrightarrow>
   length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom u) < length (Problem_atoms p) \<Longrightarrow> \<not> Lit_pos u \<Longrightarrow>
   \<not> pext p t (f[unat (Lit_atom u) := True]) \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u \<Longrightarrow>
   length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   \<not> unat (Lit_atom u) < length (Problem_atoms p) \<Longrightarrow> Lit_pos u \<Longrightarrow> pext p t f \<Longrightarrow> False\<close>
  using step_last_find[of p l t f u] unfolding find_result_def by auto

lemma step_last_fuel:
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u \<Longrightarrow>
   length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom u) < length (Problem_atoms p) \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count (t[unat (Lit_atom u) := True]) f < k\<close>
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   unit_result t f (l ! unat (word_of_nat (length l) - 1 :: 64 word)) u \<Longrightarrow>
   length t = length (Problem_atoms p) \<Longrightarrow> length f = length (Problem_atoms p) \<Longrightarrow>
   unat (Lit_atom u) < length (Problem_atoms p) \<Longrightarrow> unset_count t f < Suc k \<Longrightarrow>
   unset_count t (f[unat (Lit_atom u) := True]) < k\<close>
  using step_last_find[of p l t f u] search_unit_fuel[of p t f u k] by simp_all

lemma step_last_pre:
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   length (Clause_lits (l ! unat (word_of_nat (length l) - 1 :: 64 word))) < 18446744073709551616\<close>
  \<open>clauses_ok p l \<Longrightarrow> 0 < unat (word_of_nat (length l) :: 64 word) \<Longrightarrow>
   a \<in> set (Clause_lits (l ! unat (word_of_nat (length l) - 1 :: 64 word))) \<Longrightarrow>
   unat (Lit_atom a) < length (Problem_atoms p)\<close>
  using last_idx_lt[of \<open>length l\<close>] nth_mem[of \<open>unat (word_of_nat (length l) - 1 :: 64 word)\<close> l]
  unfolding clauses_ok_def clause_ok_def by auto

text \<open>The clause of a closure conflict, as \<^verbatim>\<open>on_conflict\<close> needs it.\<close>
lemma step_conflict_fits:
  assumes \<open>set (Clause_lits cl) = conflict_lits e c (length (Problem_atoms p))\<close>
      and \<open>wf_problem p\<close> \<open>length (Problem_atoms p) < 9223372036854775808\<close>
      and \<open>unat c < length (Problem_atoms p)\<close> \<open>length e = length (Problem_atoms p)\<close>
      and \<open>(unat (Atom_lhs (Problem_atoms p ! unat c)), unat (Atom_rhs (Problem_atoms p ! unat c)))
             \<in> cc p (asserted p e (length (Problem_atoms p)))\<close>
      and \<open>length (Clause_lits cl) \<le> Suc (length (Problem_atoms p))\<close>
  shows \<open>clause_fits p cl\<close>
  using assms conflict_lits_clause_ok[of p c e cl] unfolding clause_fits_def by simp

text \<open>A falsified clause when there are no atoms.\<close>
lemma step_empty_conflict:
  assumes \<open>find_result p t f x\<close> \<open>Lit_atom x = 0\<close> \<open>Lit_pos x\<close>
      and \<open>(word_of_nat (length (Problem_atoms p)) :: 64 word) = 0\<close> \<open>length (Problem_atoms p) < 9223372036854775808\<close>
      and \<open>length t = length (Problem_atoms p)\<close> \<open>pext p t f\<close>
  shows False
proof -
  have \<open>length (Problem_atoms p) = 0\<close>
    using assms(4,5) unat_of_nat_eq[of \<open>length (Problem_atoms p)\<close>, where 'a=64] by simp
  then show False using assms(1,2,3,6,7) unfolding find_result_def by simp
qed

lemma unset_count_le:
  \<open>unset_count t f \<le> length t\<close>
proof -
  have \<open>{j. j < length t \<and> \<not> t ! j \<and> \<not> f ! j} \<subseteq> {..<length t}\<close> by auto
  then show ?thesis unfolding unset_count_def by (metis card_lessThan card_mono finite_lessThan)
qed

lemma step_fallback_fuel:
  \<open>length t = length (Problem_atoms p) \<Longrightarrow> length (Problem_atoms p) < urust_fuel \<Longrightarrow> unset_count t f < urust_fuel\<close>
  using unset_count_le[of t f] by simp

lemma cdcl_rec_step_spec:
  assumes \<open>\<And>l t f lv rs ts d s. \<Gamma>; R p l t f lv rs ts d s \<Turnstile>\<^sub>F cdcl_contract k p l t f d\<close>
  shows \<open>\<Gamma>; cdcl_rec_step R p l t f lv rs ts d s \<Turnstile>\<^sub>F cdcl_contract (Suc k) p l t f d\<close>
  apply (crush_boot f: cdcl_rec_step_def contract: cdcl_contract_def)
  apply (crush_base specs add: assms sat_add_ok_spec next_unit_spec unit_index_spec indexed_clause_spec on_conflict_spec
        note_spec note_new_spec note_true_spec cc_propagate_spec explain_spec conflict_clause_spec differs_spec
        first_unset_spec prop_holds_spec theory_check_spec clause_unit_spec search_spec
      contracts add: cdcl_contract_def sat_add_ok_contract_def next_unit_contract_def unit_index_contract_def
        indexed_clause_contract_def on_conflict_contract_def note_contract_def cc_propagate_contract_def
        explain_contract_def conflict_clause_contract_def differs_contract_def first_unset_contract_def
        prop_holds_contract_def theory_check_contract_def clause_unit_contract_def search_contract_def
      simp add: unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq word64_eq_of_nat_iff)
  apply (auto simp add: word_less_nat_alt unat_of_nat_lt63 Option.is_none_def split: option.splits
      dest: find_result_le)
  apply ((rule step_unit_none step_unit_fuel step_branch_none step_branch_fuel step_leaf step_leaf_some
        step_implied step_implied_fuel step_conflict step_falsified wf_lit step_last_none step_last_fuel
        step_last_pre last_idx_lt last_idx_one step_conflict_fits step_fallback_fuel; assumption)+)?
  apply (rule step_empty_conflict; assumption)
  done

lemma cdcl_rec_spec:
  shows \<open>\<Gamma>; (cdcl_rec_step ^^ k) R p l t f lv rs ts d s \<Turnstile>\<^sub>F cdcl_contract k p l t f d\<close>
proof (induction k arbitrary: l t f lv rs ts d s)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: cdcl_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule cdcl_rec_step_spec) (rule Suc.IH)
qed

lemma cdcl_spec:
  shows \<open>\<Gamma>; cdcl p l t f lv rs ts d s \<Turnstile>\<^sub>F cdcl_contract urust_fuel p l t f d\<close>
  unfolding cdcl_def by (rule cdcl_rec_spec)

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
  apply (crush_base specs add: cdcl_spec contracts add: cdcl_contract_def split!: option.splits
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
  apply (crush_base specs add: cdcl_spec contracts add: cdcl_contract_def split!: option.splits
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
     prism_9 prism_10 prism_11 prism_12 prism_13 prism_14 prism_15 prism_16 prism_17\<close>
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
