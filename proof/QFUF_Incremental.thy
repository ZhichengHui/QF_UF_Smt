theory QFUF_Incremental
  imports QFUF_Analyze
begin

section \<open>Incremental closure\<close>

text \<open>\<^verbatim>\<open>cdcl\<close> carries a partition down its recursion. Its invariant: each class lies in the
  congruence closure of the atoms set true. That the partition is closed is not needed for
  soundness, only for the speed of the search.\<close>

subsection \<open>Pure facts\<close>

definition rep_for :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>rep_for p t rs \<equiv> wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p) \<and> reps_lt p rs \<and>
     rep_sound p (asserted p t (length (Problem_atoms p))) rs\<close>

lemma rep_for_mono:
  assumes \<open>rep_for p t rs\<close> \<open>\<forall>j < length (Problem_atoms p). t ! j \<longrightarrow> t' ! j\<close>
  shows \<open>rep_for p t' rs\<close>
proof -
  have \<open>asserted p t (length (Problem_atoms p)) \<subseteq> asserted p t' (length (Problem_atoms p))\<close>
    using assms(2) unfolding asserted_def by blast
  then show ?thesis
    using assms(1) cc_mono unfolding rep_for_def rep_sound_def by blast
qed

lemma rep_for_update:
  assumes \<open>rep_for p t rs\<close> \<open>length t = length (Problem_atoms p)\<close>
  shows \<open>rep_for p (t[i := True]) rs\<close>
proof (rule rep_for_mono[OF assms(1)], intro allI impI)
  fix j assume \<open>j < length (Problem_atoms p)\<close> \<open>t ! j\<close>
  then show \<open>t[i := True] ! j\<close> using assms(2) by (cases \<open>i = j\<close>) simp_all
qed

lemma rep_for_implied:
  assumes \<open>implied_ok p t f rs' t2 f2\<close> \<open>length t = length (Problem_atoms p)\<close> \<open>rep_for p t rs\<close>
  shows \<open>rep_for p t2 rs\<close>
proof (rule rep_for_mono[OF assms(3)], intro allI impI)
  fix j assume \<open>j < length (Problem_atoms p)\<close> \<open>t ! j\<close>
  moreover have \<open>\<forall>j < length t. t ! j \<longrightarrow> t2 ! j\<close>
    using assms(1) unfolding implied_ok_def by blast
  ultimately show \<open>t2 ! j\<close> using assms(2) by simp
qed

lemma rep_for_cc_inv:
  \<open>cc_inv p (asserted p t (length (Problem_atoms p))) rs \<Longrightarrow> rep_for p t rs\<close>
  unfolding cc_inv_def rep_ok_def rep_for_def by simp

lemma rep_for_empty:
  assumes \<open>cc_inv p {} rs\<close>
  shows \<open>rep_for p t rs\<close>
proof -
  have \<open>rep_sound p (asserted p t (length (Problem_atoms p))) rs\<close>
    using assms cc_mono[of _ _ p \<open>{}\<close>] unfolding cc_inv_def rep_ok_def rep_sound_def by blast
  then show ?thesis using assms unfolding cc_inv_def rep_ok_def rep_for_def by simp
qed

lemma rep_for_length:
  \<open>rep_for p t rs \<Longrightarrow> length rs = length (Problem_terms p)\<close>
  by (simp add: rep_for_def)

text \<open>The invariant of \<^verbatim>\<open>log_atoms\<close> after the atoms below \<open>k\<close>.\<close>
definition atoms_inv :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>atoms_inv p t k rs \<equiv> rep_for p t rs \<and> rep_has (asserted p t k) rs\<close>

lemma atoms_inv_0:
  \<open>rep_for p t rs \<Longrightarrow> atoms_inv p t 0 rs\<close>
  by (simp add: atoms_inv_def rep_has_def)

lemma atoms_inv_end:
  \<open>atoms_inv p t (length (Problem_atoms p)) rs \<Longrightarrow> cc_inv p (asserted p t (length (Problem_atoms p))) rs\<close>
  using asserted_bounded[of p \<open>length (Problem_atoms p)\<close> t]
  unfolding atoms_inv_def rep_for_def cc_inv_def rep_ok_def by auto

lemma atoms_inv_skip:
  assumes \<open>atoms_inv p t k rs\<close> \<open>\<not> t ! k\<close>
  shows \<open>atoms_inv p t (Suc k) rs\<close>
  using assms by (simp add: atoms_inv_def asserted_Suc)

lemma atoms_inv_joined:
  assumes \<open>atoms_inv p t k rs\<close>
      and \<open>rs ! unat (Atom_lhs (Problem_atoms p ! k)) = rs ! unat (Atom_rhs (Problem_atoms p ! k))\<close>
  shows \<open>atoms_inv p t (Suc k) rs\<close>
  using assms by (simp add: atoms_inv_def asserted_Suc rep_has_def)

context QFUF_ctx
begin

lemma atoms_inv_merge:
  assumes \<open>atoms_inv p t k rs\<close> \<open>k < length (Problem_atoms p)\<close> \<open>t ! k\<close>
  shows \<open>atoms_inv p t (Suc k)
           (merge_list rs (unat (Atom_lhs (Problem_atoms p ! k))) (unat (Atom_rhs (Problem_atoms p ! k))))\<close>
proof -
  let ?l = \<open>unat (Atom_lhs (Problem_atoms p ! k))\<close> and ?r = \<open>unat (Atom_rhs (Problem_atoms p ! k))\<close>
  let ?A = \<open>asserted p t (length (Problem_atoms p))\<close>
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms p)\<close>
    and sound: \<open>rep_sound p ?A rs\<close> and has: \<open>rep_has (asserted p t k) rs\<close> and lt: \<open>reps_lt p rs\<close>
    using assms(1) unfolding atoms_inv_def rep_for_def by simp_all
  have lr: \<open>?l < length rs\<close> \<open>?r < length rs\<close> using wf_atom[OF wf assms(2)] n by simp_all
  have \<open>(?l, ?r) \<in> ?A\<close> using assms(2,3) unfolding asserted_def by blast
  then have \<open>rep_sound p ?A (merge_list rs ?l ?r)\<close>
    using rep_sound_merge[OF sound lr] cc.base by blast
  moreover have \<open>rep_has (asserted p t (Suc k)) (merge_list rs ?l ?r)\<close>
  proof -
    have \<open>\<forall>(i, j) \<in> asserted p t k. i < length rs \<and> j < length rs\<close>
      using asserted_bounded[OF wf, of k t] assms(2) n by auto
    then have \<open>rep_has (asserted p t k) (merge_list rs ?l ?r)\<close>
      using has unfolding rep_has_def by (auto intro: merge_list_keeps)
    then show ?thesis using merge_list_joins[OF lr] assms(3) unfolding rep_has_def by (auto simp add: asserted_Suc)
  qed
  moreover have \<open>reps_lt p (merge_list rs ?l ?r)\<close>
    using lt lr(2) reps_lt_merge by blast
  ultimately show ?thesis
    using assms(1) n unfolding atoms_inv_def rep_for_def by simp
qed

lemma atoms_inv_lt:
  assumes \<open>atoms_inv p t k rs\<close> \<open>j < length (Problem_atoms p)\<close>
  shows \<open>unat (Atom_lhs (Problem_atoms p ! j)) < length rs\<close> \<open>unat (Atom_rhs (Problem_atoms p ! j)) < length rs\<close>
    \<open>length rs < 18446744073709551616\<close>
  using assms wf_atom[of p j] unfolding atoms_inv_def rep_for_def sizes_ok_def by auto

subsection \<open>Contracts\<close>

definition log_atoms_inv_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>log_atoms_inv_contract p t rep g rs xs gx xv ys gy yv ls gl lv \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>rep_for p t rs \<and> length t = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms p))) rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_atoms_inv_spec:
  shows \<open>\<Gamma>; log_atoms p t rep xs ys ls \<Turnstile>\<^sub>F log_atoms_inv_contract p t rep g rs xs gx xv ys gy yv ls gl lv\<close>
  apply (crush_boot f: log_atoms_def contract: log_atoms_inv_contract_def)
  apply (crush_base simp add: rep_for_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>atoms_inv p t k rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: merge_spec contracts add: merge_contract_def inline: vec_push_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: rep_for_def unat_of_nat_lt63 intro: atoms_inv_skip atoms_inv_joined atoms_inv_merge
      atoms_inv_0 atoms_inv_end dest: atoms_inv_lt)
  apply (simp add: atoms_inv_def rep_for_def sizes_ok_def rep_has_def)
  done

definition arg_moved_contract :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>arg_moved_contract p old rs i \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length old = length (Problem_terms p) \<and> length rs = length (Problem_terms p) \<and>
         unat i < length (Problem_terms p)\<rangle> in
     make_function_contract pre (\<lambda>_. can_alloc_reference)\<close>

lemma arg_moved_spec:
  shows \<open>\<Gamma>; arg_moved p old rs i \<Turnstile>\<^sub>F arg_moved_contract p old rs i\<close>
  apply (crush_boot f: arg_moved_def contract: arg_moved_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq sizes_ok_def)
  apply (meson nth_mem unat_idx_lt(1) wf_args_lt_length)+
  done

definition moved_rows_contract :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>moved_rows_contract p old rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length old = length (Problem_terms p) \<and> length rs = length (Problem_terms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>length r = length (Problem_terms p)\<rangle> in
     make_function_contract pre post\<close>

lemma moved_rows_spec:
  shows \<open>\<Gamma>; moved_rows p old rs \<Turnstile>\<^sub>F moved_rows_contract p old rs\<close>
  apply (crush_boot f: moved_rows_def contract: moved_rows_contract_def)
  apply (crush_base simp add: sizes_ok_def unat_of_nat_lt63)
  subgoal for rows_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' v. rows_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: arg_moved_spec contracts add: arg_moved_contract_def
        simp add: unat_of_nat_eq less_Suc_eq sizes_ok_def)
    done
  done

definition log_col_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>log_col_contract p rep g rs xs gx xv ys gy yv ls gl lv i E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>cc_inv p E rs \<and> unat i < length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_col_spec:
  shows \<open>\<Gamma>; log_col p perm st rep xs ys ls i \<Turnstile>\<^sub>F log_col_contract p rep g rs xs gx xv ys gy yv ls gl lv i E\<close>
  apply (crush_boot f: log_col_def contract: log_col_contract_def)
  apply (crush_base specs add: get_or_spec sat_add_ok_spec contracts add: get_or_contract_def sat_add_ok_contract_def
      simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec congruent_spec merge_spec
        contracts add: get_or_contract_def congruent_contract_def merge_contract_def
        inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (all \<open>(drule unat_lt_len[OF iffD1[OF word_less_nat_alt]])?\<close>)
    apply (auto simp add: cc_inv_length intro: cc_inv_merge args_len_lt dest: wf_args_lt_length)
    apply (auto simp add: cc_inv_def sizes_ok_def intro: args_len_lt)
    apply ((meson wf_args order.strict_trans)+)?
    done
  done

lemma rev_idx_lt:
  assumes \<open>i < n\<close> \<open>n < 9223372036854775808\<close>
  shows \<open>unat (word64_of_nat n - 1 - word64_of_nat i) = n - 1 - i\<close> \<open>word64_of_nat i \<le> (word64_of_nat n - 1 :: 64 word)\<close>
    \<open>1 \<le> (word64_of_nat n :: 64 word)\<close>
proof -
  have n: \<open>unat (word64_of_nat n :: 64 word) = n\<close> \<open>unat (word64_of_nat i :: 64 word) = i\<close>
    using assms by (simp_all add: unat_of_nat_eq)
  then show \<open>1 \<le> (word64_of_nat n :: 64 word)\<close> using assms(1) by (simp add: word_le_nat_alt)
  then have m: \<open>unat (word64_of_nat n - 1 :: 64 word) = n - 1\<close> using n by (simp add: unat_sub)
  then show \<open>word64_of_nat i \<le> (word64_of_nat n - 1 :: 64 word)\<close> using n assms(1) by (simp add: word_le_nat_alt)
  then show \<open>unat (word64_of_nat n - 1 - word64_of_nat i) = n - 1 - i\<close> using n m by (simp add: unat_sub)
qed

definition buckets_contract :: \<open>Problem \<Rightarrow> ('s, 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  \<open>buckets_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>_. can_alloc_reference in
     make_function_contract pre post\<close>

lemma buckets_spec:
  shows \<open>\<Gamma>; buckets p rs \<Turnstile>\<^sub>F buckets_contract p\<close>
  apply (crush_boot f: buckets_def contract: buckets_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for bh_ref bn_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' v. bh_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. bn_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec set_at_any_spec contracts add: get_or_contract_def set_at_any_contract_def
        simp add: unat_of_nat_eq less_Suc_eq sizes_ok_def)
    apply (auto simp add: rev_idx_lt)
    done
  done

definition log_bucket_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>log_bucket_contract p rep g rs xs gx xv ys gy yv ls gl lv i E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>cc_inv p E rs \<and> unat i < length (Problem_terms p) \<and> Term_args (Problem_terms p ! unat i) \<noteq> []\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_bucket_spec:
  shows \<open>\<Gamma>; log_bucket p bh bn rep xs ys ls i \<Turnstile>\<^sub>F log_bucket_contract p rep g rs xs gx xv ys gy yv ls gl lv i E\<close>
  apply (crush_boot f: log_bucket_def contract: log_bucket_contract_def)
  apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref jv j_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star> (\<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star> (\<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec congruent_spec merge_spec
        contracts add: get_or_contract_def congruent_contract_def merge_contract_def
        inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length not_le word_less_nat_alt unat_of_nat_lt63 intro: cc_inv_merge args_len_lt unat_lt_len
        dest: wf_args_lt_length)
    apply (auto simp add: cc_inv_def sizes_ok_def)
    done
  apply (auto simp add: rep_ok_def intro!: wf_args_lt_length)
  done

definition log_moved_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>log_moved_contract p rows rep g rs xs gx xv ys gy yv ls gl lv E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>cc_inv p E rs \<and> length rows = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_moved_spec:
  shows \<open>\<Gamma>; log_moved p perm st bh bn rows rep xs ys ls \<Turnstile>\<^sub>F log_moved_contract p rows rep g rs xs gx xv ys gy yv ls gl lv E\<close>
  apply (crush_boot f: log_moved_def contract: log_moved_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: log_col_spec log_bucket_spec contracts add: log_col_contract_def log_bucket_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_def sizes_ok_def)
    done
  done

definition copy_into_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow>
      ('s, unit, 'abort) function_contract\<close> where
  \<open>copy_into_contract old n rs \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g v. old \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>length v = n\<rangle>) in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g v. old \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>length v = n\<rangle>) in
     make_function_contract pre post\<close>

lemma copy_into_spec:
  shows \<open>\<Gamma>; copy_into old rs \<Turnstile>\<^sub>F copy_into_contract old n rs\<close>
  apply (crush_boot f: copy_into_def contract: copy_into_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. old \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>length v = n\<rangle>)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq word_less_nat_alt)
  apply (auto intro: unat_idx_lt(1) unat_lt_len)
  done

definition round_moved_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>round_moved_contract p old rep g rs xs ys ls E \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star>
        \<langle>cc_inv p E rs \<and> wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma round_moved_spec:
  shows \<open>\<Gamma>; round_moved p perm st old rep xs ys ls \<Turnstile>\<^sub>F round_moved_contract p old rep g rs xs ys ls E\<close>
  apply (crush_boot f: round_moved_def contract: round_moved_contract_def)
  apply (crush_base specs add: moved_rows_spec copy_into_spec[where n=\<open>length (Problem_terms p)\<close>] buckets_spec log_moved_spec
      contracts add: moved_rows_contract_def copy_into_contract_def buckets_contract_def log_moved_contract_def
      simp add: cc_inv_length)
  done

definition close_moved_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>close_moved_contract p old rep g rs xs ys ls E \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star>
        \<langle>cc_inv p E rs \<and> wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma close_moved_spec:
  shows \<open>\<Gamma>; close_moved p perm st old rep xs ys ls \<Turnstile>\<^sub>F close_moved_contract p old rep g rs xs ys ls E\<close>
  apply (crush_boot f: close_moved_def contract: close_moved_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v. old \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: round_moved_spec contracts add: round_moved_contract_def
      simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
  apply (auto simp add: cc_inv_def sizes_ok_def)
  done

text \<open>The partition that \<^const>\<open>cc_step\<close> returns is sound for the atoms set true.\<close>
definition cc_step_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow>
      ('s, 64 word \<times> bool list \<times> bool list \<times> 64 word list \<times> 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort)
        function_contract\<close> where
  \<open>cc_step_contract p t f rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> rep_for p t rs \<and> length t = length (Problem_atoms p) \<and>
         length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>conflict_result p t f (fst r) \<and> (\<exists>rs'. implied_ok p t f rs' (fst (snd r)) (fst (snd (snd r)))) \<and>
         rep_for p t (fst (snd (snd (snd r))))\<rangle> in
     make_function_contract pre post\<close>

lemma cc_step_spec:
  shows \<open>\<Gamma>; cc_step p perm st t f rs xs ys ls \<Turnstile>\<^sub>F cc_step_contract p t f rs\<close>
  apply (crush_boot f: cc_step_def contract: cc_step_contract_def)
  apply (crush_base specs add: log_atoms_inv_spec close_moved_spec false_joined_spec[where t=t] implied_spec
      contracts add: log_atoms_inv_contract_def close_moved_contract_def false_joined_contract_def
        implied_contract_def
      simp add: rep_for_length)
  apply (all \<open>(solves \<open>blast intro: rep_for_cc_inv\<close>)?\<close>)
  done

definition root_log_contract :: \<open>Problem \<Rightarrow>
      ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  \<open>root_log_contract p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>cc_inv p {} (fst r)\<rangle> in
     make_function_contract pre post\<close>

lemma root_log_spec:
  shows \<open>\<Gamma>; root_log p \<Turnstile>\<^sub>F root_log_contract p\<close>
  apply (crush_boot f: root_log_def contract: root_log_contract_def)
  apply (crush_base specs add: init_rep_spec close_spec merge_log_spec
      contracts add: init_rep_contract_def close_contract_def merge_log_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto simp add: sizes_ok_def unat_of_nat_lt63 intro: cc_inv_init64 cc_inv_init cc_inv_length)
  done

end

end
