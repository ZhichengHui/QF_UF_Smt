theory QFUF_Contracts
  imports QFUF_Pure
begin

section \<open>Contracts of the solver's functions\<close>

lemma map_prefix_nth:
  \<open>i < length xs \<Longrightarrow> (List.map f (take i xs) @ drop i xs) ! i = xs ! i\<close>
  by (simp add: nth_append min_def)

lemma map_prefix_Suc:
  \<open>i < length xs \<Longrightarrow>
   List.map f (take (Suc i) xs) @ drop (Suc i) xs = (List.map f (take i xs) @ drop i xs)[i := f (xs ! i)]\<close>
  by (simp add: take_Suc_conv_app_nth list_update_append Cons_nth_drop_Suc[symmetric])

lemma map_prefix_update_same:
  \<open>i < length xs \<Longrightarrow> (List.map f (take i xs) @ drop i xs)[i := xs ! i] = List.map f (take i xs) @ drop i xs\<close>
  by (metis list_update_id map_prefix_nth)

lemma word64_of_nat_eq_lengthD:
  assumes \<open>(word_of_nat x :: 64 word) = word_of_nat y\<close> \<open>x < 2^64\<close> \<open>y < 2^64\<close>
  shows \<open>x = y\<close>
proof -
  have \<open>unat (word_of_nat x :: 64 word) = x\<close> \<open>unat (word_of_nat y :: 64 word) = y\<close>
    using assms(2,3) by (simp_all add: unat_of_nat_eq)
  then show ?thesis using assms(1) by metis
qed

lemma unat_of_nat_le:
  \<open>unat (word_of_nat n :: 64 word) \<le> n\<close>
  by (simp add: unat_of_nat)

lemma unat_idx_lt:
  \<open>i < unat (word_of_nat n :: 64 word) \<Longrightarrow> unat (word_of_nat i :: 64 word) < n\<close>
  \<open>i < n \<Longrightarrow> unat (word_of_nat i :: 64 word) < n\<close>
  by (meson le_less_trans order_less_le_trans unat_of_nat_le)+

lemma unat_lt_len:
  \<open>x < unat (word_of_nat n :: 64 word) \<Longrightarrow> x < n\<close>
  using order_less_le_trans unat_of_nat_le by blast

lemma wf_args_lt_length:
  \<open>wf_problem p \<Longrightarrow> k < length (Problem_terms_l p) \<Longrightarrow> x \<in> set (Term_args_l (Problem_terms_l p ! k)) \<Longrightarrow>
   unat x < length (Problem_terms_l p)\<close>
  using wf_args by (meson order.strict_trans)

text \<open>Every representative is a term index.\<close>
definition reps_lt :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>reps_lt p rs \<equiv> \<forall>x \<in> set rs. unat x < length (Problem_terms_l p)\<close>

text \<open>The invariant of the representative list during the closure, for the asserted pairs \<open>E\<close>.\<close>
definition cc_inv :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>cc_inv p E rs \<equiv> wf_problem p \<and> sizes_ok p \<and> rep_ok p E rs \<and>
     (\<forall>(i, j) \<in> E. i < length (Problem_terms_l p) \<and> j < length (Problem_terms_l p)) \<and> reps_lt p rs\<close>

lemma cc_inv_merge:
  assumes \<open>cc_inv p E rs\<close> \<open>i < length rs\<close> \<open>j < length rs\<close> \<open>congruent_p p rs i j\<close>
  shows \<open>cc_inv p E (merge_list rs i j)\<close>
proof -
  have \<open>reps_lt p (merge_list rs i j)\<close>
    using assms(1,3) unfolding cc_inv_def reps_lt_def merge_list_def by (auto intro: nth_mem)
  then show ?thesis
    using assms rep_ok_merge_congruent unfolding cc_inv_def rep_ok_def by (metis length_merge_list)
qed

lemma cc_inv_length:
  \<open>cc_inv p E rs \<Longrightarrow> length rs = length (Problem_terms_l p)\<close>
  by (simp add: cc_inv_def rep_ok_def)

text \<open>The step of a row of the closure that merges nothing at \<open>k\<close> because \<open>k\<close> is not congruent to
  \<open>i\<close> under \<open>rs'\<close>; congruence under \<open>rs\<close> carries over to \<open>rs'\<close>, which keeps the classes of \<open>rs\<close>.\<close>
lemma row_joined_step_wf:
  assumes \<open>wf_problem p\<close> \<open>rep_ok p E rs\<close> \<open>refines rs rs'\<close>
      and \<open>i < length (Problem_terms_l p)\<close> \<open>k < length (Problem_terms_l p)\<close>
      and \<open>row_joined p rs rs' i k\<close> \<open>\<not> congruent_p p rs' i k\<close>
  shows \<open>row_joined p rs rs' i (Suc k)\<close>
proof -
  have \<open>\<not> congruent_p p rs i k\<close>
    using assms congruent_p_refines[OF assms(3)] unfolding rep_ok_def by (metis wf_args_lt_length)
  then show ?thesis using assms(6) row_joined_not_congruent by blast
qed

lemma closed_rowsI:
  \<open>\<forall>i < length rs. row_joined p rs rs i i \<Longrightarrow> closed p rs\<close>
  unfolding row_joined_def by (rule closed_lowerI) blast

lemma card_merge_lt:
  assumes \<open>cc_inv p E r\<close> \<open>i < length (Problem_terms_l p)\<close> \<open>j < length (Problem_terms_l p)\<close>
      and \<open>r ! i \<noteq> r ! j\<close> \<open>card (set r) \<le> C\<close>
  shows \<open>card (set (merge_list r i j)) < C\<close>
  using assms card_set_merge_list_less[of i r j] cc_inv_length[OF assms(1)] by simp

lemma args_len_lt:
  \<open>\<forall>t \<in> set ts. length (Term_args_l t) < 9223372036854775808 \<Longrightarrow> k < length ts \<Longrightarrow>
   length (Term_args_l (ts ! k)) < 18446744073709551616\<close>
  using nth_mem by fastforce

lemma unat_len_plus_one:
  \<open>n < 2^63 \<Longrightarrow> unat (word_of_nat n + 1 :: 64 word) = n + 1\<close>
  by (simp add: unat_word_ariths unat_of_nat_eq)

lemma length_map_prefix [simp]:
  \<open>length (List.map f (take i xs) @ drop i xs) = length xs\<close>
  by simp

text \<open>The row of a constant, which \<open>scan_apps\<close> skips.\<close>
lemma apps_below_Suc_const:
  assumes \<open>apps_below p rs k\<close> \<open>\<not> 0 < (word_of_nat (length (Term_args_l (Problem_terms_l p ! k))) :: 64 word)\<close>
      and \<open>\<forall>t \<in> set (Problem_terms_l p). length (Term_args_l t) < 9223372036854775808\<close>
      and \<open>k < length (Problem_terms_l p)\<close>
  shows \<open>apps_below p rs (Suc k)\<close>
proof -
  have \<open>(word_of_nat (length (Term_args_l (Problem_terms_l p ! k))) :: 64 word) = word_of_nat 0\<close>
    using assms(2) by (simp add: word_gt_0)
  then have \<open>Term_args_l (Problem_terms_l p ! k) = []\<close>
    using args_len_lt[OF assms(3,4)] word64_of_nat_eq_lengthD by fastforce
  then show ?thesis using assms(1) apps_below_Suc by blast
qed

context QFUF_ctx
begin

subsection \<open>Propositional evaluation\<close>

definition clause_holds_contract :: \<open>bool list \<Rightarrow> Clause \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>clause_holds_contract a c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length a) \<and> length (Clause_lits_l c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l \<in> set (Clause_lits_l c). a ! unat (Lit_atom l) = Lit_pos l)\<rangle> in
     make_function_contract pre post\<close>

lemma clause_holds_spec:
  shows \<open>\<Gamma>; clause_holds a c \<Turnstile>\<^sub>F clause_holds_contract a c\<close>
  apply (crush_boot f: clause_holds_def contract: clause_holds_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j<i. a ! unat (Lit_atom (Clause_lits_l c ! j)) \<noteq> Lit_pos (Clause_lits_l c ! j)\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l\<in>set (Clause_lits_l c). a ! unat (Lit_atom l) = Lit_pos l)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq in_set_conv_nth)
  apply (auto intro: nth_mem)
  done

definition prop_holds_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>prop_holds_contract p a \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>c \<in> set (Problem_clauses_l p). \<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length a) \<and>
         length (Problem_clauses_l p) < 2^64 \<and> (\<forall>c \<in> set (Problem_clauses_l p). length (Clause_lits_l c) < 2^64)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = prop_true p a\<rangle> in
     make_function_contract pre post\<close>

lemma prop_holds_spec:
  shows \<open>\<Gamma>; prop_holds p a \<Turnstile>\<^sub>F prop_holds_contract p a\<close>
  apply (crush_boot f: prop_holds_def contract: prop_holds_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star>
               \<langle>\<forall>j<i. \<exists>l \<in> set (Clause_lits_l (Problem_clauses_l p ! j)). a ! unat (Lit_atom l) = Lit_pos l\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = prop_true p a\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: clause_holds_spec contracts add: clause_holds_contract_def
      simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: prop_true_def less_Suc_eq intro: nth_mem)
  apply (metis in_set_conv_nth)
  done

definition some_lit_true_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>some_lit_true_contract t f c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length t) \<and> length f = length t \<and>
         length (Clause_lits_l c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l \<in> set (Clause_lits_l c). lit_set_true t f l)\<rangle> in
     make_function_contract pre post\<close>

lemma some_lit_true_spec:
  shows \<open>\<Gamma>; some_lit_true t f c \<Turnstile>\<^sub>F some_lit_true_contract t f c\<close>
  apply (crush_boot f: some_lit_true_def contract: some_lit_true_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j<i. \<not> lit_set_true t f (Clause_lits_l c ! j)\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l \<in> set (Clause_lits_l c). lit_set_true t f l)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: lit_set_true_def in_set_conv_nth)
  apply (metis nth_mem)+
  done

definition unset_lit_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>unset_lit_contract t f c s \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length t) \<and> length f = length t \<and>
         length (Clause_lits_l c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat r \<le> length (Clause_lits_l c) \<and>
         (unat r < length (Clause_lits_l c) \<longrightarrow> r \<noteq> s \<and> lit_unset t f (Clause_lits_l c ! unat r)) \<and>
         (unat r = length (Clause_lits_l c) \<longrightarrow>
            (\<forall>j < length (Clause_lits_l c). j \<noteq> unat s \<longrightarrow> \<not> lit_unset t f (Clause_lits_l c ! j)))\<rangle> in
     make_function_contract pre post\<close>

lemma unset_lit_spec:
  shows \<open>\<Gamma>; unset_lit t f c s \<Turnstile>\<^sub>F unset_lit_contract t f c s\<close>
  apply (crush_boot f: unset_lit_def contract: unset_lit_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j<i. j \<noteq> unat s \<longrightarrow> \<not> lit_unset t f (Clause_lits_l c ! j)\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>unat r < length (Clause_lits_l c) \<and> r \<noteq> s \<and> lit_unset t f (Clause_lits_l c ! unat r)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: lit_unset_def)
  done

text \<open>The result of \<^const>\<open>clause_unit\<close>: a literal whose atom is below \<open>length t\<close> is a literal of
  \<open>c\<close>, unset, and every other literal of \<open>c\<close> is false; otherwise the atom is \<open>length t\<close>, and
  if the literal is positive every literal of \<open>c\<close> is false.\<close>
definition unit_result :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>unit_result t f c r \<equiv>
     (unat (Lit_atom r) < length t \<longrightarrow>
        r \<in> set (Clause_lits_l c) \<and> lit_unset t f r \<and> (\<forall>l \<in> set (Clause_lits_l c). l = r \<or> lit_false t f l)) \<and>
     (unat (Lit_atom r) = length t \<and> Lit_pos r \<longrightarrow> (\<forall>l \<in> set (Clause_lits_l c). lit_false t f l)) \<and>
     unat (Lit_atom r) \<le> length t\<close>

lemma unit_result_none:
  \<open>length t < 2^63 \<Longrightarrow> unit_result t f c (make_Lit (word_of_nat (length t)) False)\<close>
  unfolding unit_result_def by (simp add: unat_of_nat_eq)

lemma unit_result_conflict:
  assumes \<open>length t < 2^63\<close> \<open>\<forall>l \<in> set (Clause_lits_l c). \<not> lit_set_true t f l\<close>
      and \<open>\<forall>j < length (Clause_lits_l c). \<not> lit_unset t f (Clause_lits_l c ! j)\<close>
  shows \<open>unit_result t f c (make_Lit (word_of_nat (length t)) True)\<close>
proof -
  have \<open>\<forall>l \<in> set (Clause_lits_l c). lit_false t f l\<close>
    using assms(2,3) by (metis in_set_conv_nth lit_falseI)
  then show ?thesis using assms(1) unfolding unit_result_def by (simp add: unat_of_nat_eq)
qed

lemma unit_result_unit:
  assumes at: \<open>\<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length t\<close>
      and nt: \<open>\<forall>l \<in> set (Clause_lits_l c). \<not> lit_set_true t f l\<close>
      and i: \<open>i < length (Clause_lits_l c)\<close> \<open>lit_unset t f (Clause_lits_l c ! i)\<close>
      and one: \<open>\<forall>j < length (Clause_lits_l c). j \<noteq> i \<longrightarrow> \<not> lit_unset t f (Clause_lits_l c ! j)\<close>
  shows \<open>unit_result t f c (Clause_lits_l c ! i)\<close>
proof -
  have all: \<open>\<forall>l \<in> set (Clause_lits_l c). l = Clause_lits_l c ! i \<or> lit_false t f l\<close>
  proof
    fix l assume \<open>l \<in> set (Clause_lits_l c)\<close>
    then obtain j where j: \<open>j < length (Clause_lits_l c)\<close> \<open>l = Clause_lits_l c ! j\<close>
      by (auto simp add: in_set_conv_nth)
    show \<open>l = Clause_lits_l c ! i \<or> lit_false t f l\<close>
    proof (cases \<open>j = i\<close>)
      case False
      then have \<open>lit_false t f l\<close> using j one nt nth_mem[OF j(1)] by (auto intro: lit_falseI)
      then show ?thesis ..
    qed (use j in simp)
  qed
  have \<open>Clause_lits_l c ! i \<in> set (Clause_lits_l c)\<close> using i(1) by simp
  then show ?thesis using all at i(2) unfolding unit_result_def by auto
qed

lemma unat_lt_of_ne:
  assumes \<open>unat (x :: 64 word) \<le> n\<close> \<open>n < 2^64\<close> \<open>x \<noteq> word_of_nat n\<close>
  shows \<open>unat x < n\<close>
proof (rule ccontr)
  assume \<open>\<not> unat x < n\<close>
  then have \<open>unat x = unat (word_of_nat n :: 64 word)\<close> using assms(1,2) by (simp add: unat_of_nat_eq)
  then show False using assms(3) unat_eq_iff_eq by blast
qed

lemma unat_eq_of_not_less:
  assumes \<open>unat (x :: 64 word) \<le> n\<close> \<open>n < 2^64\<close> \<open>\<not> x < word_of_nat n\<close>
  shows \<open>unat x = n\<close>
proof -
  have \<open>unat (word_of_nat n :: 64 word) = n\<close> using assms(2) by (simp add: unat_of_nat_eq)
  then show ?thesis using assms(1,3) by (simp add: word_less_nat_alt)
qed

definition clause_unit_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  \<open>clause_unit_contract t f c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_lits_l c). unat (Lit_atom l) < length t) \<and> length f = length t \<and>
         length t < 2^63 \<and> length (Clause_lits_l c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>unit_result t f c r\<rangle> in
     make_function_contract pre post\<close>

lemma clause_unit_spec:
  shows \<open>\<Gamma>; clause_unit t f c \<Turnstile>\<^sub>F clause_unit_contract t f c\<close>
  apply (crush_boot f: clause_unit_def contract: clause_unit_contract_def)
  apply (crush_base specs add: some_lit_true_spec unset_lit_spec
      contracts add: some_lit_true_contract_def unset_lit_contract_def simp add: unat_of_nat_eq)
  subgoal for x xa
    using unat_lt_of_ne[of x \<open>length (Clause_lits_l c)\<close>] unat_eq_of_not_less[of xa \<open>length (Clause_lits_l c)\<close>]
    by (intro unit_result_unit) auto
  subgoal for x xa using unat_lt_of_ne[of x \<open>length (Clause_lits_l c)\<close>] by simp
  subgoal for x xa using unat_lt_of_ne[of x \<open>length (Clause_lits_l c)\<close>] by simp
  subgoal by (rule unit_result_none) simp
  subgoal by (rule unit_result_conflict) simp_all
  subgoal by (rule unit_result_none) simp
  done

subsection \<open>Union-find\<close>

definition merge_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>merge_contract rep g rs a b \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>unat a < length rs \<and> unat b < length rs \<and> length rs < 2^64\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>(merge_list rs (unat a) (unat b))) in
     make_function_contract pre post\<close>

lemma merge_spec:
  shows \<open>\<Gamma>; merge rep a b \<Turnstile>\<^sub>F merge_contract rep g rs a b\<close>
  apply (crush_boot f: merge_def contract: merge_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>(List.map
                 (\<lambda>x. if x = rs ! unat a then rs ! unat b else x) (take i rs) @ drop i rs))\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq map_prefix_nth map_prefix_Suc merge_list_def map_prefix_update_same)
  done

definition congruent_contract :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>congruent_contract p rs i j \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>unat i < length (Problem_terms_l p) \<and> unat j < length (Problem_terms_l p) \<and>
         length (Term_args_l (Problem_terms_l p ! unat i)) < 2^64 \<and> length (Term_args_l (Problem_terms_l p ! unat j)) < 2^64 \<and>
         (\<forall>x \<in> set (Term_args_l (Problem_terms_l p ! unat i)). unat x < length rs) \<and>
         (\<forall>x \<in> set (Term_args_l (Problem_terms_l p ! unat j)). unat x < length rs)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = congruent_p p rs (unat i) (unat j)\<rangle> in
     make_function_contract pre post\<close>

lemma congruent_spec:
  shows \<open>\<Gamma>; congruent p rs i j \<Turnstile>\<^sub>F congruent_contract p rs i j\<close>
  apply (crush_boot f: congruent_def contract: congruent_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star>
               \<langle>\<forall>k'<k. rs ! unat (Term_args_l (Problem_terms_l p ! unat i) ! k') =
                        rs ! unat (Term_args_l (Problem_terms_l p ! unat j) ! k')\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = congruent_p p rs (unat i) (unat j)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: congruent_p_def less_Suc_eq dest!: word64_of_nat_eq_lengthD)
  done

subsection \<open>Congruence closure\<close>

definition scan_row_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_row_contract p rep g rs i E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p E rs \<and> unat i < length (Problem_terms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p E rs' \<and> refines rs rs' \<and> row_joined p rs rs' (unat i) (unat i) \<and>
         (if r then card (set rs') < card (set rs) else rs' = rs)\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_row_spec:
  shows \<open>\<Gamma>; scan_row p rep i \<Turnstile>\<^sub>F scan_row_contract p rep g rs i E\<close>
  apply (crush_boot f: scan_row_def contract: scan_row_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs' \<and> refines rs rs' \<and> row_joined p rs rs' (unat i) k \<and>
                  (if c then card (set rs') < card (set rs) else rs' = rs)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: congruent_spec merge_spec contracts add: congruent_contract_def merge_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length split: if_splits intro: cc_inv_merge card_merge_lt args_len_lt
        refines_refl refines_merge row_joined_0 row_joined_merge row_joined_eq row_joined_step_wf
        dest: wf_args_lt_length)
    apply (auto simp add: cc_inv_def sizes_ok_def intro: args_len_lt)
    apply (meson wf_args order.strict_trans)+
    done
  done

definition scan_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_contract p rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p E rs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p E rs' \<and> consts_joined p rs' \<and>
         (if r then card (set rs') < card (set rs) else rs' = rs \<and> closed p rs)\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_spec:
  shows \<open>\<Gamma>; scan p rep \<Turnstile>\<^sub>F scan_contract p rep g rs E\<close>
  apply (crush_boot f: scan_def contract: scan_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs' \<and> consts_below p rs' k \<and>
                  (if c then card (set rs') < card (set rs) else rs' = rs \<and> (\<forall>i < k. row_joined p rs rs i i))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: scan_row_spec contracts add: scan_row_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length consts_joined_def split: if_splits
        intro: closed_rowsI consts_below_0 consts_below_step)
    apply (auto simp add: cc_inv_def sizes_ok_def)
    done
  done

definition scan_apps_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_apps_contract p rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p E rs \<and> consts_joined p rs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p E rs' \<and> consts_joined p rs' \<and>
         (if r then card (set rs') < card (set rs) else rs' = rs \<and> closed p rs)\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_apps_spec:
  shows \<open>\<Gamma>; scan_apps p rep \<Turnstile>\<^sub>F scan_apps_contract p rep g rs E\<close>
  apply (crush_boot f: scan_apps_def contract: scan_apps_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs' \<and> consts_joined p rs' \<and>
                  (if c then card (set rs') < card (set rs) else rs' = rs \<and> apps_below p rs k)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: scan_row_spec contracts add: scan_row_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length split: if_splits
        intro: closed_appsI apps_below_0 apps_below_Suc apps_below_Suc_const consts_joined_refines)
    apply (auto simp add: cc_inv_def sizes_ok_def)
    done
  done

definition close_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>close_contract p rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p E rs\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs' \<and> closed p rs'\<rangle>) in
     make_function_contract pre post\<close>

lemma close_spec:
  shows \<open>\<Gamma>; close p rep \<Turnstile>\<^sub>F close_contract p rep g rs E\<close>
  apply (crush_boot f: close_def contract: close_contract_def)
  apply (crush_base specs add: scan_spec contracts add: scan_contract_def simp add: cc_inv_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
               \<langle>cc_inv p E rs' \<and> consts_joined p rs' \<and> card (set rs') + k \<le> length (Problem_terms_l p)\<rangle>)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs' \<and> closed p rs'\<rangle>)\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: scan_apps_spec contracts add: scan_apps_contract_def
      simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
  apply (auto simp add: cc_inv_def sizes_ok_def rep_ok_def unat_len_plus_one split: if_splits
      intro: order.trans[OF card_length])
  done

subsection \<open>Facts for the model, the theory check and the search\<close>

text \<open>Placed after the congruence-closure contracts, so that they are not in the context of
  the earlier crush calls, which pick facts by relevance.\<close>

definition entry_of :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> Entry\<close> where
  \<open>entry_of p rs i \<equiv> make_Entry (Term_fun (Problem_terms_l p ! i))
     (List.map (\<lambda>x. rs ! unat x) (Term_args_l (Problem_terms_l p ! i))) (rs ! i)\<close>

lemma model_of_eq:
  assumes \<open>length es = length (Problem_terms_l p)\<close> \<open>\<forall>j < length (Problem_terms_l p). es ! j = entry_of p rs j\<close>
  shows \<open>make_Model es = model_of p rs\<close>
proof -
  have \<open>es = List.map (entry_of p rs) [0..<length (Problem_terms_l p)]\<close>
    using assms by (intro nth_equalityI) simp_all
  then show ?thesis by (simp add: model_of_def entry_of_def)
qed

text \<open>The partition \<open>rs\<close> keeps apart the two sides of every atom below \<open>m\<close> set false.\<close>
definition diseqs_hold :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>diseqs_hold p a rs m \<equiv> \<forall>k < m. \<not> a ! k \<longrightarrow>
     rs ! unat (Atom_lhs (Problem_atoms_l p ! k)) \<noteq> rs ! unat (Atom_rhs (Problem_atoms_l p ! k))\<close>

lemma reps_lt_merge:
  \<open>reps_lt p rs \<Longrightarrow> b < length rs \<Longrightarrow> reps_lt p (merge_list rs a b)\<close>
  unfolding reps_lt_def merge_list_def by (auto intro: nth_mem)

lemma reps_lt_init:
  \<open>length (Problem_terms_l p) < 2^63 \<Longrightarrow> reps_lt p (List.map word_of_nat [0..<length (Problem_terms_l p)])\<close>
  unfolding reps_lt_def by (auto simp add: unat_of_nat_eq)

text \<open>Every value and every argument in the entries of the model \<open>m\<close> is a term index of \<open>p\<close>.\<close>
definition model_vals_ok :: \<open>Problem \<Rightarrow> Model \<Rightarrow> bool\<close> where
  \<open>model_vals_ok p m \<equiv> length (Model_entries_l m) \<le> length (Problem_terms_l p) \<and> (\<forall>e \<in> set (Model_entries_l m).
     unat (Entry_val e) < length (Problem_terms_l p) \<and> (\<forall>a \<in> set (Entry_args_l e). unat a < length (Problem_terms_l p)) \<and>
     (\<exists>t \<in> set (Problem_terms_l p). length (Entry_args_l e) \<le> length (Term_args_l t)))\<close>

lemma model_of_vals_ok:
  assumes \<open>cc_inv p E rs\<close>
  shows \<open>model_vals_ok p (model_of p rs)\<close>
proof -
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms_l p)\<close> and r: \<open>reps_lt p rs\<close>
    using assms by (simp_all add: cc_inv_def rep_ok_def)
  have rs: \<open>unat (rs ! k) < length (Problem_terms_l p)\<close> if \<open>k < length (Problem_terms_l p)\<close> for k
    using r n that unfolding reps_lt_def by (metis nth_mem)
  have l: \<open>length (Model_entries_l (model_of p rs)) \<le> length (Problem_terms_l p)\<close> by (simp add: model_of_def)
  have each: \<open>unat (Entry_val e) < length (Problem_terms_l p) \<and>
          (\<forall>a \<in> set (Entry_args_l e). unat a < length (Problem_terms_l p)) \<and>
          (\<exists>t \<in> set (Problem_terms_l p). length (Entry_args_l e) \<le> length (Term_args_l t))\<close>
    if ein: \<open>e \<in> set (Model_entries_l (model_of p rs))\<close> for e
  proof -
    obtain i where i: \<open>i < length (Problem_terms_l p)\<close> and e: \<open>e = make_Entry (Term_fun (Problem_terms_l p ! i))
        (List.map (\<lambda>x. rs ! unat x) (Term_args_l (Problem_terms_l p ! i))) (rs ! i)\<close>
      using ein by (auto simp add: model_of_def)
    have t: \<open>\<exists>t \<in> set (Problem_terms_l p). length (Entry_args_l e) \<le> length (Term_args_l t)\<close>
      using i by (auto simp add: e intro!: bexI[of _ \<open>Problem_terms_l p ! i\<close>])
    show ?thesis using rs[OF i] rs wf_args_lt_length[OF wf i] t by (auto simp add: e)
  qed
  show ?thesis using l each by (simp add: model_vals_ok_def)
qed

lemma cc_inv_init:
  \<open>wf_problem p \<Longrightarrow> sizes_ok p \<Longrightarrow> cc_inv p {} (List.map word_of_nat [0..<length (Problem_terms_l p)])\<close>
  using rep_ok_init[of p] reps_lt_init[of p] unfolding cc_inv_def sizes_ok_def by simp

lemma cc_inv_assert:
  assumes \<open>cc_inv p (asserted p a k) rs\<close> \<open>k < length (Problem_atoms_l p)\<close> \<open>a ! k\<close>
  shows \<open>cc_inv p (asserted p a (Suc k))
           (merge_list rs (unat (Atom_lhs (Problem_atoms_l p ! k))) (unat (Atom_rhs (Problem_atoms_l p ! k))))\<close>
proof -
  let ?l = \<open>unat (Atom_lhs (Problem_atoms_l p ! k))\<close> and ?r = \<open>unat (Atom_rhs (Problem_atoms_l p ! k))\<close>
  let ?E = \<open>asserted p a k\<close> and ?E' = \<open>asserted p a (Suc k)\<close>
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms_l p)\<close>
    using assms(1) by (simp_all add: cc_inv_def rep_ok_def)
  have lr: \<open>?l < length rs\<close> \<open>?r < length rs\<close> using wf_atom[OF wf assms(2)] n by simp_all
  have E': \<open>?E' = insert (?l, ?r) ?E\<close> using assms(3) by (simp add: asserted_Suc)
  have bnd: \<open>\<forall>(i, j) \<in> ?E'. i < length (Problem_terms_l p) \<and> j < length (Problem_terms_l p)\<close>
    using asserted_bounded[OF wf, of \<open>Suc k\<close> a] assms(2) by simp
  have sound: \<open>rep_sound p ?E' rs\<close>
    using assms(1) cc_mono[of _ _ p ?E ?E'] E' unfolding cc_inv_def rep_ok_def rep_sound_def by blast
  have \<open>(?l, ?r) \<in> cc p ?E'\<close> using E' by (simp add: cc.base)
  then have \<open>rep_sound p ?E' (merge_list rs ?l ?r)\<close>
    using rep_sound_merge[OF sound lr] by blast
  moreover have \<open>rep_has ?E' (merge_list rs ?l ?r)\<close>
  proof -
    have \<open>rep_has ?E (merge_list rs ?l ?r)\<close>
      using assms(1) rep_has_merge bnd E' n unfolding cc_inv_def rep_ok_def by auto
    then show ?thesis using merge_list_joins[OF lr] E' unfolding rep_has_def by auto
  qed
  moreover have \<open>reps_lt p (merge_list rs ?l ?r)\<close>
    using assms(1) lr(2) reps_lt_merge unfolding cc_inv_def by blast
  ultimately show ?thesis
    using assms(1) bnd n unfolding cc_inv_def rep_ok_def by simp
qed

lemma word64_eq_of_nat_iff:
  fixes x :: \<open>64 word\<close>
  assumes \<open>n < 2^64\<close>
  shows \<open>x = word_of_nat n \<longleftrightarrow> unat x = n\<close>
proof
  assume \<open>x = word_of_nat n\<close>
  then show \<open>unat x = n\<close> using assms by (simp add: unat_of_nat_eq)
next
  assume \<open>unat x = n\<close>
  then show \<open>x = word_of_nat n\<close> using assms by (simp add: word_unat_eq_iff unat_of_nat_eq)
qed

lemma unat_of_nat_lt63:
  \<open>n < 9223372036854775808 \<Longrightarrow> unat (word_of_nat n :: 64 word) = n\<close>
  by (simp add: unat_of_nat_eq)

lemma cc_inv_atom_lt:
  assumes \<open>cc_inv p E rs\<close> \<open>k < length (Problem_atoms_l p)\<close>
  shows \<open>unat (Atom_lhs (Problem_atoms_l p ! k)) < length rs\<close> \<open>unat (Atom_rhs (Problem_atoms_l p ! k)) < length rs\<close>
  using assms wf_atom[of p k] unfolding cc_inv_def rep_ok_def by simp_all

lemma cc_inv_len64:
  \<open>cc_inv p E rs \<Longrightarrow> length rs < 18446744073709551616\<close>
  unfolding cc_inv_def rep_ok_def sizes_ok_def by simp

text \<open>Facts for the leaves of the search.\<close>

lemma theory_none:
  assumes \<open>cc_inv p (asserted p a (length (Problem_atoms_l p))) rs\<close> \<open>length a = length (Problem_atoms_l p)\<close>
      and \<open>\<not> diseqs_hold p a rs (length (Problem_atoms_l p))\<close>
  shows \<open>atom_vals I p \<noteq> a\<close>
proof
  assume av: \<open>atom_vals I p = a\<close>
  obtain k where k: \<open>k < length (Problem_atoms_l p)\<close> \<open>\<not> a ! k\<close>
    \<open>rs ! unat (Atom_lhs (Problem_atoms_l p ! k)) = rs ! unat (Atom_rhs (Problem_atoms_l p ! k))\<close>
    using assms(3) unfolding diseqs_hold_def by blast
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms_l p)\<close>
    using assms(1) by (simp_all add: cc_inv_def rep_ok_def)
  have \<open>(unat (Atom_lhs (Problem_atoms_l p ! k)), unat (Atom_rhs (Problem_atoms_l p ! k)))
          \<in> cc p (asserted p a (length (Problem_atoms_l p)))\<close>
    using assms(1) k(3) wf_atom[OF wf k(1)] n unfolding cc_inv_def rep_ok_def rep_sound_def by simp
  then show False using unsat_by_cc[OF wf assms(2) av k(1,2)] by blast
qed

lemma theory_some:
  assumes \<open>cc_inv p (asserted p a (length (Problem_atoms_l p))) rs\<close> \<open>closed p rs\<close>
      \<open>length a = length (Problem_atoms_l p)\<close> \<open>diseqs_hold p a rs (length (Problem_atoms_l p))\<close>
  shows \<open>atom_vals (model_interp (model_of p rs)) p = a\<close>
  using assms model_of_atom_vals unfolding cc_inv_def diseqs_hold_def by blast

text \<open>The postcondition of \<^const>\<open>find_unit\<close>.\<close>
definition find_result :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>find_result p t f r \<equiv>
     unat (Lit_atom r) \<le> length t \<and>
     (unat (Lit_atom r) < length t \<longrightarrow> lit_unset t f r \<and>
        (pext p t f \<longrightarrow> (if Lit_pos r then pext p (t[unat (Lit_atom r) := True]) f
                         else pext p t (f[unat (Lit_atom r) := True])))) \<and>
     (unat (Lit_atom r) = length t \<and> Lit_pos r \<longrightarrow> \<not> pext p t f)\<close>

lemma find_result_none:
  \<open>unat (Lit_atom r) = length t \<Longrightarrow> \<not> Lit_pos r \<Longrightarrow> find_result p t f r\<close>
  unfolding find_result_def by simp

lemma find_result_clause:
  assumes c: \<open>clause_ok p c\<close> and u: \<open>unit_result t f c r\<close>
      and len: \<open>length t = length (Problem_atoms_l p)\<close> \<open>length f = length (Problem_atoms_l p)\<close>
  shows \<open>find_result p t f r\<close>
  using u pext_unit[OF c _ _ len, of r] pext_conflict[OF c, of t f]
  unfolding unit_result_def find_result_def by auto

text \<open>Clauses that \<^const>\<open>find_unit\<close> may scan: clauses of the problem or learned ones.\<close>
definition clauses_ok :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool\<close> where
  \<open>clauses_ok p cs \<equiv> \<forall>c \<in> set cs. clause_ok p c \<and> length (Clause_lits_l c) < 2^64\<close>

lemma clauses_ok_problem:
  \<open>wf_problem p \<Longrightarrow> sizes_ok p \<Longrightarrow> clauses_ok p (Problem_clauses_l p)\<close>
  unfolding clauses_ok_def sizes_ok_def using clause_ok_problem by fastforce

lemma clauses_ok_append:
  \<open>clauses_ok p cs \<Longrightarrow> clause_ok p c \<Longrightarrow> length (Clause_lits_l c) < 2^64 \<Longrightarrow> clauses_ok p (cs @ [c])\<close>
  unfolding clauses_ok_def by auto

text \<open>A pair of atom sides that a partition joins lies in the congruence closure.\<close>
lemma cc_inv_joined:
  assumes \<open>cc_inv p E rs\<close> \<open>k < length (Problem_atoms_l p)\<close>
      and \<open>rs ! unat (Atom_lhs (Problem_atoms_l p ! k)) = rs ! unat (Atom_rhs (Problem_atoms_l p ! k))\<close>
  shows \<open>(unat (Atom_lhs (Problem_atoms_l p ! k)), unat (Atom_rhs (Problem_atoms_l p ! k))) \<in> cc p E\<close>
proof -
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms_l p)\<close>
    using assms(1) by (simp_all add: cc_inv_def rep_ok_def)
  show ?thesis
    using assms wf_atom[OF wf assms(2)] n unfolding cc_inv_def rep_ok_def rep_sound_def by simp
qed

text \<open>The result of \<^const>\<open>false_joined\<close>: an atom index, and for an atom below the
  number of atoms, an atom set false whose sides the closure of the atoms set true joins.\<close>
definition conflict_result :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> bool\<close> where
  \<open>conflict_result p t f r \<equiv> unat r \<le> length (Problem_atoms_l p) \<and>
     (unat r < length (Problem_atoms_l p) \<longrightarrow> f ! unat r \<and>
        (unat (Atom_lhs (Problem_atoms_l p ! unat r)), unat (Atom_rhs (Problem_atoms_l p ! unat r)))
          \<in> cc p (asserted p t (length (Problem_atoms_l p))))\<close>

lemma conflict_result_none:
  \<open>conflict_result p t f r \<Longrightarrow> wf_problem p \<Longrightarrow> length t = length (Problem_atoms_l p) \<Longrightarrow>
   unat r < length (Problem_atoms_l p) \<Longrightarrow> \<not> pext p t f\<close>
  unfolding conflict_result_def using pext_cc_conflict by blast

text \<open>Facts for the steps of the search.\<close>

lemma search_unit_none:
  \<open>find_result p t f r \<Longrightarrow> unat (Lit_atom r) < length t \<Longrightarrow> Lit_pos r \<Longrightarrow>
   \<not> pext p (t[unat (Lit_atom r) := True]) f \<Longrightarrow> \<not> pext p t f\<close>
  \<open>find_result p t f r \<Longrightarrow> unat (Lit_atom r) < length t \<Longrightarrow> \<not> Lit_pos r \<Longrightarrow>
   \<not> pext p t (f[unat (Lit_atom r) := True]) \<Longrightarrow> \<not> pext p t f\<close>
  unfolding find_result_def by auto

lemma search_unit_fuel:
  assumes \<open>find_result p t f r\<close> \<open>unat (Lit_atom r) < length t\<close> \<open>length f = length t\<close>
      and \<open>unset_count t f < Suc k\<close>
  shows \<open>unset_count (t[unat (Lit_atom r) := True]) f < k\<close> \<open>unset_count t (f[unat (Lit_atom r) := True]) < k\<close>
  using assms unset_count_less[of \<open>unat (Lit_atom r)\<close> t f] unfolding find_result_def lit_unset_def by auto

lemma search_branch_fuel:
  assumes \<open>j < length t\<close> \<open>\<not> t ! j\<close> \<open>\<not> f ! j\<close> \<open>length f = length t\<close> \<open>unset_count t f < Suc k\<close>
  shows \<open>unset_count (t[j := True]) f < k\<close> \<open>unset_count t (f[j := True]) < k\<close>
  using assms unset_count_less[of j t f] by auto

lemma search_branch_none:
  \<open>\<not> pext p (t[j := True]) f \<Longrightarrow> \<not> pext p t (f[j := True]) \<Longrightarrow> \<not> pext p t f\<close>
  using pext_branch by blast

lemma search_leaf_none:
  \<open>wf_problem p \<Longrightarrow> length t = length (Problem_atoms_l p) \<Longrightarrow> \<forall>j < length t. t ! j \<or> f ! j \<Longrightarrow>
   \<not> prop_true p t \<Longrightarrow> \<not> pext p t f\<close>
  using pext_leaf problem_true_prop_true by metis

lemma search_leaf_theory_none:
  \<open>length t = length (Problem_atoms_l p) \<Longrightarrow> \<forall>j < length t. t ! j \<or> f ! j \<Longrightarrow>
   \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. atom_vals I p \<noteq> t \<Longrightarrow> \<not> pext p t f\<close>
  using pext_leaf by metis

lemma search_leaf_some:
  \<open>wf_problem p \<Longrightarrow> prop_true p a \<Longrightarrow> atom_vals I p = a \<Longrightarrow> problem_true I p\<close>
  using problem_true_prop_true by metis

definition rep_args_contract :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  \<open>rep_args_contract rs xs \<equiv>
     let pre = can_alloc_reference \<star> \<langle>(\<forall>x \<in> set xs. unat x < length rs) \<and> length xs < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = List.map (\<lambda>x. rs ! unat x) xs\<rangle> in
     make_function_contract pre post\<close>

lemma rep_args_spec:
  shows \<open>\<Gamma>; rep_args rs xs \<Turnstile>\<^sub>F rep_args_contract rs xs\<close>
  apply (crush_boot f: rep_args_def contract: rep_args_contract_def)
  apply crush_base
  subgoal for out_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' ys. out_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ys \<star>
                 \<langle>ys = List.map (\<lambda>x. rs ! unat x) (take k xs) @ drop k xs\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq map_prefix_nth map_prefix_Suc)
    apply (auto simp add: map_prefix_nth)?
    done
  done

definition build_model_contract :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> ('s, Model, 'abort) function_contract\<close> where
  \<open>build_model_contract p rs \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = model_of p rs\<rangle> in
     make_function_contract pre post\<close>

lemma build_model_spec:
  shows \<open>\<Gamma>; build_model p rs \<Turnstile>\<^sub>F build_model_contract p rs\<close>
  apply (crush_boot f: build_model_def contract: build_model_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for entries_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' es. entries_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>es \<star>
                 \<langle>length es = length (Problem_terms_l p) \<and> (\<forall>j < i. es ! j = entry_of p rs j)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: rep_args_spec contracts add: rep_args_contract_def
        simp add: unat_of_nat_eq less_Suc_eq)
    apply (auto simp add: entry_of_def intro: args_len_lt wf_args_lt_length model_of_eq)
    done
  done

subsection \<open>Facts used by the theory check\<close>

text \<open>Placed here, after the congruence-closure contracts, so that they are not in the
  context of the earlier crush calls, which pick facts by relevance.\<close>

text \<open>The index of a \<^verbatim>\<open>for\<close> loop over \<open>0..n\<close> appears as an element of
  \<^term>\<open>List.map word64_of_nat [0..<n]\<close>.\<close>
lemma unat_map_upt_nth63:
  \<open>i < n \<Longrightarrow> n < 9223372036854775808 \<Longrightarrow> unat (List.map word64_of_nat [0..<n] ! i) = i\<close>
  by (simp add: unat_of_nat_lt63)

text \<open>Used with \<open>xs\<close> fixed, so that both conditions are assumptions of the goal.\<close>
lemma unat_idx_lt63:
  \<open>i < length xs \<Longrightarrow> length xs < 9223372036854775808 \<Longrightarrow> unat (word_of_nat i :: 64 word) = i\<close>
  by (rule unat_of_nat_lt63) (erule (1) less_trans)

lemma cc_inv_init64:
  \<open>wf_problem p \<Longrightarrow> sizes_ok p \<Longrightarrow>
   cc_inv p {} (List.map word_of_nat [0..<unat (word_of_nat (length (Problem_terms_l p)) :: 64 word)])\<close>
  using cc_inv_init[of p] by (simp add: sizes_ok_def unat_of_nat_lt63)

lemma cc_inv_assert_insert:
  assumes \<open>cc_inv p (asserted p a k) rs\<close> \<open>k < length (Problem_atoms_l p)\<close> \<open>a ! k\<close>
  shows \<open>cc_inv p (insert (unat (Atom_lhs (Problem_atoms_l p ! k)), unat (Atom_rhs (Problem_atoms_l p ! k)))
                     (asserted p a k))
           (merge_list rs (unat (Atom_lhs (Problem_atoms_l p ! k))) (unat (Atom_rhs (Problem_atoms_l p ! k))))\<close>
  using cc_inv_assert[OF assms] assms(3) by (simp add: asserted_Suc)

subsection \<open>The theory check\<close>

definition init_rep_contract :: \<open>64 word \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  \<open>init_rep_contract n \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = List.map word_of_nat [0..<unat n]\<rangle> in
     make_function_contract pre post\<close>

lemma init_rep_spec:
  shows \<open>\<Gamma>; init_rep n \<Turnstile>\<^sub>F init_rep_contract n\<close>
  apply (crush_boot f: init_rep_def contract: init_rep_contract_def)
  apply (insert unat_lt2p[of n])
  apply crush_base
  subgoal for rep_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' xs. rep_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>xs \<star>
                 \<langle>length xs = unat n \<and> (\<forall>j < i. xs ! j = word_of_nat j)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq less_Suc_eq nth_list_update)
    apply (auto simp add: nth_list_update less_Suc_eq intro!: nth_equalityI)
    done
  done

definition assert_eqs_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      64 word list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>assert_eqs_contract p a m rep g rs \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p {} rs \<and> length a = length (Problem_atoms_l p) \<and> unat m \<le> length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p (asserted p a (unat m)) rs'\<rangle>) in
     make_function_contract pre post\<close>

text \<open>The loop body ends with a call whose postcondition is existential. With schematics
  allowed, crush would instantiate the invariant's existentials before opening the callee's,
  so the steps below run with schematics off and instantiate by hand.\<close>
lemma assert_eqs_spec:
  shows \<open>\<Gamma>; assert_eqs p a m rep \<Turnstile>\<^sub>F assert_eqs_contract p a m rep g rs\<close>
  apply (crush_boot f: assert_eqs_def contract: assert_eqs_contract_def)
  apply (crush_base simp add: unat_of_nat_lt63 cc_inv_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
               \<langle>cc_inv p (asserted p a k) rs'\<rangle>)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  supply [[crush_allow_schematics = false]]
  apply (crush_base specs add: merge_spec contracts add: merge_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms_l p\<close>]
        asserted_Suc unat_map_upt_nth63)
  subgoal for i g' rs'
    apply (rule aexists_entailsR[where x=g'], rule aexists_entailsR[where x=rs'])
    apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms_l p\<close>]
        asserted_Suc unat_map_upt_nth63)
    done
  subgoal for i g' rs'
    apply (crush_base specs add: merge_spec[where g=g' and rs=rs'] contracts add: merge_contract_def
        simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms_l p\<close>]
        asserted_Suc unat_map_upt_nth63)
    supply [[crush_allow_schematics = true]]
    apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms_l p\<close>]
        asserted_Suc unat_map_upt_nth63)
    apply (auto simp add: asserted_Suc intro: cc_inv_assert_insert cc_inv_assert cc_inv_atom_lt cc_inv_len64)
    done
  supply [[crush_allow_schematics = true]]
  apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms_l p\<close>]
        asserted_Suc unat_map_upt_nth63)?
  apply (auto simp add: cc_inv_def sizes_ok_def dest: wf_atom)?
  done

definition diseqs_ok_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> 64 word list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>diseqs_ok_contract p a m rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> length rs = length (Problem_terms_l p) \<and> length a = length (Problem_atoms_l p) \<and>
         unat m \<le> length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = diseqs_hold p a rs (unat m)\<rangle> in
     make_function_contract pre post\<close>

lemma diseqs_ok_spec:
  shows \<open>\<Gamma>; diseqs_ok p a m rs \<Turnstile>\<^sub>F diseqs_ok_contract p a m rs\<close>
  apply (crush_boot f: diseqs_ok_def contract: diseqs_ok_contract_def)
  apply (insert unat_lt2p[of m])
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> \<langle>\<forall>k' < k. \<not> a ! k' \<longrightarrow>
               rs ! unat (Atom_lhs (Problem_atoms_l p ! k')) \<noteq> rs ! unat (Atom_rhs (Problem_atoms_l p ! k'))\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = diseqs_hold p a rs (unat m)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq diseqs_hold_def)
  apply (meson wf_atom order_less_le_trans)+
  done

definition theory_check_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('s, Model option, 'abort) function_contract\<close> where
  \<open>theory_check_contract p a \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length a = length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           None \<Rightarrow> \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. atom_vals I p \<noteq> a
         | Some m \<Rightarrow> atom_vals (model_interp m) p = a \<and> model_vals_ok p m\<rangle> in
     make_function_contract pre post\<close>

text \<open>The state of \<open>rep\<close> is existentially quantified inside the contract: the caller gets it from
  the existential postcondition of \<^const>\<open>close\<close>, and a contract parameter would be instantiated
  before that existential is opened.\<close>
definition finish_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, Model option, 'abort) function_contract\<close> where
  \<open>finish_contract p a rep \<equiv>
     let pre = can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
          \<langle>cc_inv p (asserted p a (length (Problem_atoms_l p))) rs \<and> closed p rs \<and>
           length rs = length (Problem_terms_l p)\<rangle>) \<star>
        \<langle>length a = length (Problem_atoms_l p) \<and> wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs) \<star>
        \<langle>case r of
           None \<Rightarrow> \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. atom_vals I p \<noteq> a
         | Some m \<Rightarrow> atom_vals (model_interp m) p = a \<and> model_vals_ok p m\<rangle> in
     make_function_contract pre post\<close>

lemma finish_spec:
  shows \<open>\<Gamma>; finish p a rep \<Turnstile>\<^sub>F finish_contract p a rep\<close>
  apply (crush_boot f: finish_def contract: finish_contract_def)
  apply (crush_base specs add: diseqs_ok_spec build_model_spec
      contracts add: diseqs_ok_contract_def build_model_contract_def
      simp add: sizes_ok_def unat_of_nat_lt63)
  apply (auto intro: theory_none theory_some model_of_vals_ok simp add: sizes_ok_def)
  apply ((metis theory_none)+)?
  done

lemma theory_check_spec:
  shows \<open>\<Gamma>; theory_check p a \<Turnstile>\<^sub>F theory_check_contract p a\<close>
  apply (crush_boot f: theory_check_def contract: theory_check_contract_def)
  apply (crush_base specs add: init_rep_spec assert_eqs_spec close_spec finish_spec
      contracts add: init_rep_contract_def assert_eqs_contract_def close_contract_def finish_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto intro: cc_inv_init64 cc_inv_init cc_inv_length simp add: sizes_ok_def unat_of_nat_lt63)
  done

definition first_joined_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>first_joined_contract p f rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> length rs = length (Problem_terms_l p) \<and> length f = length (Problem_atoms_l p) \<and>
         length (Problem_atoms_l p) < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat r \<le> length (Problem_atoms_l p) \<and> (unat r < length (Problem_atoms_l p) \<longrightarrow> f ! unat r \<and>
           rs ! unat (Atom_lhs (Problem_atoms_l p ! unat r)) = rs ! unat (Atom_rhs (Problem_atoms_l p ! unat r)))\<rangle> in
     make_function_contract pre post\<close>

lemma first_joined_spec:
  shows \<open>\<Gamma>; first_joined p f rs \<Turnstile>\<^sub>F first_joined_contract p f rs\<close>
  apply (crush_boot f: first_joined_def contract: first_joined_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>unat r < length (Problem_atoms_l p) \<and> f ! unat r \<and>
           rs ! unat (Atom_lhs (Problem_atoms_l p ! unat r)) = rs ! unat (Atom_rhs (Problem_atoms_l p ! unat r))\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (metis wf_atom)+
  done

text \<open>The contract keeps the invariant of \<open>rep\<close>: theory propagation (\<^const>\<open>cc_propagate\<close>)
  reads \<open>rep\<close> again afterwards.\<close>
definition false_joined_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, 64 word, 'abort) function_contract\<close> where
  \<open>false_joined_contract p t f rep \<equiv>
     let pre = can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms_l p))) rs\<rangle>) \<star>
        \<langle>wf_problem p \<and> length t = length (Problem_atoms_l p) \<and> length f = length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms_l p))) rs\<rangle>) \<star>
        \<langle>conflict_result p t f r\<rangle> in
     make_function_contract pre post\<close>

lemma false_joined_spec:
  shows \<open>\<Gamma>; false_joined p f rep \<Turnstile>\<^sub>F false_joined_contract p t f rep\<close>
  apply (crush_boot f: false_joined_def contract: false_joined_contract_def)
  apply (crush_base specs add: first_joined_spec contracts add: first_joined_contract_def)
  apply (auto simp add: conflict_result_def cc_inv_def sizes_ok_def intro: cc_inv_joined)
  apply (simp add: rep_ok_def)
  done

subsection \<open>Unit propagation\<close>

definition find_unit_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  \<open>find_unit_contract p cs t f \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>clauses_ok p cs \<and> length (Problem_atoms_l p) < 2^63 \<and>
         length t = length (Problem_atoms_l p) \<and> length f = length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>find_result p t f r\<rangle> in
     make_function_contract pre post\<close>

lemma find_unit_spec:
  shows \<open>\<Gamma>; find_unit cs t f \<Turnstile>\<^sub>F find_unit_contract p cs t f\<close>
  apply (crush_boot f: find_unit_def contract: find_unit_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>find_result p t f r\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: clause_unit_spec contracts add: clause_unit_contract_def
      simp add: unat_of_nat_eq less_Suc_eq)
  subgoal for i x
    by (rule find_result_clause[where c=\<open>cs ! unat (word_of_nat i :: 64 word)\<close>])
      (auto simp add: clauses_ok_def unat_of_nat_lt63 dest: unat_idx_lt)
  subgoal for i x
    by (rule find_result_clause[where c=\<open>cs ! unat (word_of_nat i :: 64 word)\<close>])
      (auto simp add: clauses_ok_def unat_of_nat_lt63 dest: unat_idx_lt)
  apply (auto simp add: clauses_ok_def unat_of_nat_lt63 intro: find_result_none dest: unat_idx_lt)
  apply (meson clause_ok_def nth_mem unat_idx_lt)+
  done

definition next_unit_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  \<open>next_unit_contract p l t f \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and>
         length t = length (Problem_atoms_l p) \<and> length f = length (Problem_atoms_l p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>find_result p t f r\<rangle> in
     make_function_contract pre post\<close>

lemma next_unit_spec:
  shows \<open>\<Gamma>; next_unit p l t f \<Turnstile>\<^sub>F next_unit_contract p l t f\<close>
  apply (crush_boot f: next_unit_def contract: next_unit_contract_def)
  apply (crush_base specs add: find_unit_spec[where p=p] contracts add: find_unit_contract_def
      simp add: clauses_ok_problem)
  apply (auto simp add: sizes_ok_def clauses_ok_problem)
  done

definition first_unset_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>first_unset_contract t f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length f = length t \<and> length t < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat r \<le> length t \<and> (unat r < length t \<longrightarrow> \<not> t ! unat r \<and> \<not> f ! unat r) \<and>
         (unat r = length t \<longrightarrow> (\<forall>j < length t. t ! j \<or> f ! j))\<rangle> in
     make_function_contract pre post\<close>

lemma first_unset_spec:
  shows \<open>\<Gamma>; first_unset t f \<Turnstile>\<^sub>F first_unset_contract t f\<close>
  apply (crush_boot f: first_unset_def contract: first_unset_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j < i. t ! j \<or> f ! j\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>unat r < length t \<and> \<not> t ! unat r \<and> \<not> f ! unat r\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  done

end

end
