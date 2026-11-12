theory QFUF_Proof
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

lemma wf_args_lt_length:
  \<open>wf_problem p \<Longrightarrow> k < length (Problem_terms p) \<Longrightarrow> x \<in> set (Term_args (Problem_terms p ! k)) \<Longrightarrow>
   unat x < length (Problem_terms p)\<close>
  using wf_args by (meson order.strict_trans)

text \<open>Every representative is a term index.\<close>
definition reps_lt :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>reps_lt p rs \<equiv> \<forall>x \<in> set rs. unat x < length (Problem_terms p)\<close>

text \<open>The invariant of the representative list during the closure, for the asserted pairs \<open>E\<close>.\<close>
definition cc_inv :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>cc_inv p E rs \<equiv> wf_problem p \<and> sizes_ok p \<and> rep_ok p E rs \<and>
     (\<forall>(i, j) \<in> E. i < length (Problem_terms p) \<and> j < length (Problem_terms p)) \<and> reps_lt p rs\<close>

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
  \<open>cc_inv p E rs \<Longrightarrow> length rs = length (Problem_terms p)\<close>
  by (simp add: cc_inv_def rep_ok_def)

lemma card_merge_lt:
  assumes \<open>cc_inv p E r\<close> \<open>i < length (Problem_terms p)\<close> \<open>j < length (Problem_terms p)\<close>
      and \<open>r ! i \<noteq> r ! j\<close> \<open>card (set r) \<le> C\<close>
  shows \<open>card (set (merge_list r i j)) < C\<close>
  using assms card_set_merge_list_less[of i r j] cc_inv_length[OF assms(1)] by simp

lemma args_len_lt:
  \<open>\<forall>t \<in> set ts. length (Term_args t) < 9223372036854775808 \<Longrightarrow> k < length ts \<Longrightarrow>
   length (Term_args (ts ! k)) < 18446744073709551616\<close>
  using nth_mem by fastforce

lemma unat_len_plus_one:
  \<open>n < 2^63 \<Longrightarrow> unat (word_of_nat n + 1 :: 64 word) = n + 1\<close>
  by (simp add: unat_word_ariths unat_of_nat_eq)

lemma length_map_prefix [simp]:
  \<open>length (List.map f (take i xs) @ drop i xs) = length xs\<close>
  by simp

context QFUF_ctx
begin

subsection \<open>Propositional evaluation\<close>

definition clause_holds_contract :: \<open>bool list \<Rightarrow> Clause \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>clause_holds_contract a c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length a) \<and> length (Clause_lits c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l \<in> set (Clause_lits c). a ! unat (Lit_atom l) = Lit_pos l)\<rangle> in
     make_function_contract pre post\<close>

lemma clause_holds_spec:
  shows \<open>\<Gamma>; clause_holds a c \<Turnstile>\<^sub>F clause_holds_contract a c\<close>
  apply (crush_boot f: clause_holds_def contract: clause_holds_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j<i. a ! unat (Lit_atom (Clause_lits c ! j)) \<noteq> Lit_pos (Clause_lits c ! j)\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = (\<exists>l\<in>set (Clause_lits c). a ! unat (Lit_atom l) = Lit_pos l)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq in_set_conv_nth)
  apply (auto intro: nth_mem)
  done

definition prop_holds_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>prop_holds_contract p a \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>c \<in> set (Problem_clauses p). \<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length a) \<and>
         length (Problem_clauses p) < 2^64 \<and> (\<forall>c \<in> set (Problem_clauses p). length (Clause_lits c) < 2^64)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = prop_true p a\<rangle> in
     make_function_contract pre post\<close>

lemma prop_holds_spec:
  shows \<open>\<Gamma>; prop_holds p a \<Turnstile>\<^sub>F prop_holds_contract p a\<close>
  apply (crush_boot f: prop_holds_def contract: prop_holds_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star>
               \<langle>\<forall>j<i. \<exists>l \<in> set (Clause_lits (Problem_clauses p ! j)). a ! unat (Lit_atom l) = Lit_pos l\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = prop_true p a\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: clause_holds_spec contracts add: clause_holds_contract_def
      simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: prop_true_def less_Suc_eq intro: nth_mem)
  apply (metis in_set_conv_nth)
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
        \<langle>unat i < length (Problem_terms p) \<and> unat j < length (Problem_terms p) \<and>
         length (Term_args (Problem_terms p ! unat i)) < 2^64 \<and> length (Term_args (Problem_terms p ! unat j)) < 2^64 \<and>
         (\<forall>x \<in> set (Term_args (Problem_terms p ! unat i)). unat x < length rs) \<and>
         (\<forall>x \<in> set (Term_args (Problem_terms p ! unat j)). unat x < length rs)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = congruent_p p rs (unat i) (unat j)\<rangle> in
     make_function_contract pre post\<close>

lemma congruent_spec:
  shows \<open>\<Gamma>; congruent p rs i j \<Turnstile>\<^sub>F congruent_contract p rs i j\<close>
  apply (crush_boot f: congruent_def contract: congruent_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star>
               \<langle>\<forall>k'<k. rs ! unat (Term_args (Problem_terms p ! unat i) ! k') =
                        rs ! unat (Term_args (Problem_terms p ! unat j) ! k')\<rangle>\<close>
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
        \<langle>cc_inv p E rs \<and> unat i < length (Problem_terms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p E rs' \<and>
         (if r then card (set rs') < card (set rs)
          else rs' = rs \<and> (\<forall>j < length rs. congruent_p p rs (unat i) j \<longrightarrow> rs ! unat i = rs ! j))\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_row_spec:
  shows \<open>\<Gamma>; scan_row p rep i \<Turnstile>\<^sub>F scan_row_contract p rep g rs i E\<close>
  apply (crush_boot f: scan_row_def contract: scan_row_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs' \<and>
                  (if c then card (set rs') < card (set rs)
                   else rs' = rs \<and> (\<forall>j < k. congruent_p p rs (unat i) j \<longrightarrow> rs ! unat i = rs ! j))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: congruent_spec merge_spec contracts add: congruent_contract_def merge_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length split: if_splits intro: cc_inv_merge card_merge_lt args_len_lt
        dest: wf_args_lt_length)
    apply (auto simp add: cc_inv_def sizes_ok_def intro: args_len_lt)
    done
  done

definition scan_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_contract p rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p E rs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p E rs' \<and> (if r then card (set rs') < card (set rs) else rs' = rs \<and> closed p rs)\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_spec:
  shows \<open>\<Gamma>; scan p rep \<Turnstile>\<^sub>F scan_contract p rep g rs E\<close>
  apply (crush_boot f: scan_def contract: scan_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs' \<and>
                  (if c then card (set rs') < card (set rs)
                   else rs' = rs \<and> (\<forall>i < k. \<forall>j < length rs. congruent_p p rs i j \<longrightarrow> rs ! i = rs ! j))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: scan_row_spec contracts add: scan_row_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: closed_def cc_inv_length split: if_splits)
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
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
               \<langle>cc_inv p E rs' \<and> card (set rs') + k \<le> length (Problem_terms p)\<rangle>)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs' \<and> closed p rs'\<rangle>)\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: scan_spec contracts add: scan_contract_def
      simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
  apply (auto simp add: cc_inv_def sizes_ok_def rep_ok_def unat_len_plus_one split: if_splits
      intro: order.trans[OF card_length])
  done

subsection \<open>Facts for the model, the theory check and the search\<close>

text \<open>Placed after the congruence-closure contracts, so that they are not in the context of
  the earlier crush calls, which pick facts by relevance.\<close>

definition entry_of :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> Entry\<close> where
  \<open>entry_of p rs i \<equiv> make_Entry (Term_fun (Problem_terms p ! i))
     (List.map (\<lambda>x. rs ! unat x) (Term_args (Problem_terms p ! i))) (rs ! i)\<close>

lemma model_of_eq:
  assumes \<open>length es = length (Problem_terms p)\<close> \<open>\<forall>j < length (Problem_terms p). es ! j = entry_of p rs j\<close>
  shows \<open>make_Model es = model_of p rs\<close>
proof -
  have \<open>es = List.map (entry_of p rs) [0..<length (Problem_terms p)]\<close>
    using assms by (intro nth_equalityI) simp_all
  then show ?thesis by (simp add: model_of_def entry_of_def)
qed

definition diseqs_hold :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>diseqs_hold p a rs \<equiv> \<forall>k < length (Problem_atoms p). \<not> a ! k \<longrightarrow>
     rs ! unat (Atom_lhs (Problem_atoms p ! k)) \<noteq> rs ! unat (Atom_rhs (Problem_atoms p ! k))\<close>

lemma reps_lt_merge:
  \<open>reps_lt p rs \<Longrightarrow> b < length rs \<Longrightarrow> reps_lt p (merge_list rs a b)\<close>
  unfolding reps_lt_def merge_list_def by (auto intro: nth_mem)

lemma reps_lt_init:
  \<open>length (Problem_terms p) < 2^63 \<Longrightarrow> reps_lt p (List.map word_of_nat [0..<length (Problem_terms p)])\<close>
  unfolding reps_lt_def by (auto simp add: unat_of_nat_eq)

text \<open>Every value and every argument in the entries of the model \<open>m\<close> is a term index of \<open>p\<close>.\<close>
definition model_vals_ok :: \<open>Problem \<Rightarrow> Model \<Rightarrow> bool\<close> where
  \<open>model_vals_ok p m \<equiv> \<forall>e \<in> set (Model_entries m).
     unat (Entry_val e) < length (Problem_terms p) \<and> (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms p))\<close>

lemma model_of_vals_ok:
  assumes \<open>cc_inv p E rs\<close>
  shows \<open>model_vals_ok p (model_of p rs)\<close>
proof -
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms p)\<close> and r: \<open>reps_lt p rs\<close>
    using assms by (simp_all add: cc_inv_def rep_ok_def)
  have rs: \<open>unat (rs ! k) < length (Problem_terms p)\<close> if \<open>k < length (Problem_terms p)\<close> for k
    using r n that unfolding reps_lt_def by (metis nth_mem)
  show ?thesis
    unfolding model_vals_ok_def
  proof
    fix e
    assume \<open>e \<in> set (Model_entries (model_of p rs))\<close>
    then obtain i where i: \<open>i < length (Problem_terms p)\<close> and e: \<open>e = make_Entry (Term_fun (Problem_terms p ! i))
        (List.map (\<lambda>x. rs ! unat x) (Term_args (Problem_terms p ! i))) (rs ! i)\<close>
      by (auto simp add: model_of_def)
    show \<open>unat (Entry_val e) < length (Problem_terms p) \<and>
          (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms p))\<close>
      using rs[OF i] rs wf_args_lt_length[OF wf i] by (auto simp add: e)
  qed
qed

lemma cc_inv_init:
  \<open>wf_problem p \<Longrightarrow> sizes_ok p \<Longrightarrow> cc_inv p {} (List.map word_of_nat [0..<length (Problem_terms p)])\<close>
  using rep_ok_init[of p] reps_lt_init[of p] unfolding cc_inv_def sizes_ok_def by simp

lemma cc_inv_assert:
  assumes \<open>cc_inv p (asserted p a k) rs\<close> \<open>k < length (Problem_atoms p)\<close> \<open>a ! k\<close>
  shows \<open>cc_inv p (asserted p a (Suc k))
           (merge_list rs (unat (Atom_lhs (Problem_atoms p ! k))) (unat (Atom_rhs (Problem_atoms p ! k))))\<close>
proof -
  let ?l = \<open>unat (Atom_lhs (Problem_atoms p ! k))\<close> and ?r = \<open>unat (Atom_rhs (Problem_atoms p ! k))\<close>
  let ?E = \<open>asserted p a k\<close> and ?E' = \<open>asserted p a (Suc k)\<close>
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms p)\<close>
    using assms(1) by (simp_all add: cc_inv_def rep_ok_def)
  have lr: \<open>?l < length rs\<close> \<open>?r < length rs\<close> using wf_atom[OF wf assms(2)] n by simp_all
  have E': \<open>?E' = insert (?l, ?r) ?E\<close> using assms(3) by (simp add: asserted_Suc)
  have bnd: \<open>\<forall>(i, j) \<in> ?E'. i < length (Problem_terms p) \<and> j < length (Problem_terms p)\<close>
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

lemma unat_word_Suc63:
  \<open>unat (i :: 64 word) < 9223372036854775808 \<Longrightarrow> unat (i + 1) = Suc (unat i)\<close>
  by (simp add: unat_word_ariths)

lemma cc_inv_atom_lt:
  assumes \<open>cc_inv p E rs\<close> \<open>k < length (Problem_atoms p)\<close>
  shows \<open>unat (Atom_lhs (Problem_atoms p ! k)) < length rs\<close> \<open>unat (Atom_rhs (Problem_atoms p ! k)) < length rs\<close>
  using assms wf_atom[of p k] unfolding cc_inv_def rep_ok_def by simp_all

lemma cc_inv_len64:
  \<open>cc_inv p E rs \<Longrightarrow> length rs < 18446744073709551616\<close>
  unfolding cc_inv_def rep_ok_def sizes_ok_def by simp

text \<open>Facts for the leaves of the search.\<close>

lemma theory_none:
  assumes \<open>cc_inv p (asserted p a (length (Problem_atoms p))) rs\<close> \<open>length a = length (Problem_atoms p)\<close>
      and \<open>\<not> diseqs_hold p a rs\<close>
  shows \<open>atom_vals I p \<noteq> a\<close>
proof
  assume av: \<open>atom_vals I p = a\<close>
  obtain k where k: \<open>k < length (Problem_atoms p)\<close> \<open>\<not> a ! k\<close>
    \<open>rs ! unat (Atom_lhs (Problem_atoms p ! k)) = rs ! unat (Atom_rhs (Problem_atoms p ! k))\<close>
    using assms(3) unfolding diseqs_hold_def by blast
  have wf: \<open>wf_problem p\<close> and n: \<open>length rs = length (Problem_terms p)\<close>
    using assms(1) by (simp_all add: cc_inv_def rep_ok_def)
  have \<open>(unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k)))
          \<in> cc p (asserted p a (length (Problem_atoms p)))\<close>
    using assms(1) k(3) wf_atom[OF wf k(1)] n unfolding cc_inv_def rep_ok_def rep_sound_def by simp
  then show False using unsat_by_cc[OF wf assms(2) av k(1,2)] by blast
qed

lemma theory_some:
  assumes \<open>cc_inv p (asserted p a (length (Problem_atoms p))) rs\<close> \<open>closed p rs\<close>
      \<open>length a = length (Problem_atoms p)\<close> \<open>diseqs_hold p a rs\<close>
  shows \<open>atom_vals (model_interp (model_of p rs)) p = a\<close>
  using assms model_of_atom_vals unfolding cc_inv_def diseqs_hold_def by blast

lemma search_leaf_none:
  \<open>wf_problem p \<Longrightarrow> length a = length (Problem_atoms p) \<Longrightarrow> \<not> prop_true p a \<Longrightarrow> \<not> ext_ok p a (length a)\<close>
  using ext_ok_all problem_true_prop_true by metis

lemma search_leaf_theory_none:
  \<open>length a = length (Problem_atoms p) \<Longrightarrow> \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. atom_vals I p \<noteq> a \<Longrightarrow>
   \<not> ext_ok p a (length a)\<close>
  using ext_ok_all by metis

lemma search_leaf_some:
  \<open>wf_problem p \<Longrightarrow> prop_true p a \<Longrightarrow> atom_vals I p = a \<Longrightarrow> problem_true I p\<close>
  using problem_true_prop_true by metis

lemma search_step_none:
  \<open>\<not> ext_ok p (a[k := True]) (Suc k) \<Longrightarrow> \<not> ext_ok p (a[k := False]) (Suc k) \<Longrightarrow> k < length a \<Longrightarrow>
   length a = length (Problem_atoms p) \<Longrightarrow> \<not> ext_ok p a k\<close>
  using ext_ok_step by blast

subsection \<open>The model\<close>

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
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = model_of p rs\<rangle> in
     make_function_contract pre post\<close>

lemma build_model_spec:
  shows \<open>\<Gamma>; build_model p rs \<Turnstile>\<^sub>F build_model_contract p rs\<close>
  apply (crush_boot f: build_model_def contract: build_model_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for entries_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' es. entries_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>es \<star>
                 \<langle>length es = length (Problem_terms p) \<and> (\<forall>j < i. es ! j = entry_of p rs j)\<rangle>)\<close>
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
   cc_inv p {} (List.map word_of_nat [0..<unat (word_of_nat (length (Problem_terms p)) :: 64 word)])\<close>
  using cc_inv_init[of p] by (simp add: sizes_ok_def unat_of_nat_lt63)

lemma cc_inv_assert_insert:
  assumes \<open>cc_inv p (asserted p a k) rs\<close> \<open>k < length (Problem_atoms p)\<close> \<open>a ! k\<close>
  shows \<open>cc_inv p (insert (unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k)))
                     (asserted p a k))
           (merge_list rs (unat (Atom_lhs (Problem_atoms p ! k))) (unat (Atom_rhs (Problem_atoms p ! k))))\<close>
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

definition assert_eqs_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      64 word list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>assert_eqs_contract p a rep g rs \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p {} rs \<and> length a = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
        \<langle>cc_inv p (asserted p a (length (Problem_atoms p))) rs'\<rangle>) in
     make_function_contract pre post\<close>

text \<open>The loop body ends with a call whose postcondition is existential. With schematics
  allowed, crush would instantiate the invariant's existentials before opening the callee's,
  so the steps below run with schematics off and instantiate by hand.\<close>
lemma assert_eqs_spec:
  shows \<open>\<Gamma>; assert_eqs p a rep \<Turnstile>\<^sub>F assert_eqs_contract p a rep g rs\<close>
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
      simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms p\<close>]
        asserted_Suc unat_map_upt_nth63)
  subgoal for i g' rs'
    apply (rule aexists_entailsR[where x=g'], rule aexists_entailsR[where x=rs'])
    apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms p\<close>]
        asserted_Suc unat_map_upt_nth63)
    done
  subgoal for i g' rs'
    apply (crush_base specs add: merge_spec[where g=g' and rs=rs'] contracts add: merge_contract_def
        simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms p\<close>]
        asserted_Suc unat_map_upt_nth63)
    supply [[crush_allow_schematics = true]]
    apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms p\<close>]
        asserted_Suc unat_map_upt_nth63)
    apply (auto simp add: asserted_Suc intro: cc_inv_assert_insert cc_inv_assert cc_inv_atom_lt cc_inv_len64)
    done
  supply [[crush_allow_schematics = true]]
  apply (crush_base simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq unat_idx_lt63[of _ \<open>Problem_atoms p\<close>]
        asserted_Suc unat_map_upt_nth63)?
  apply (auto simp add: cc_inv_def sizes_ok_def dest: wf_atom)?
  done

definition diseqs_ok_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>diseqs_ok_contract p a rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> length rs = length (Problem_terms p) \<and> length a = length (Problem_atoms p) \<and>
         length (Problem_atoms p) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = diseqs_hold p a rs\<rangle> in
     make_function_contract pre post\<close>

lemma diseqs_ok_spec:
  shows \<open>\<Gamma>; diseqs_ok p a rs \<Turnstile>\<^sub>F diseqs_ok_contract p a rs\<close>
  apply (crush_boot f: diseqs_ok_def contract: diseqs_ok_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> \<langle>\<forall>k' < k. \<not> a ! k' \<longrightarrow>
               rs ! unat (Atom_lhs (Problem_atoms p ! k')) \<noteq> rs ! unat (Atom_rhs (Problem_atoms p ! k'))\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = diseqs_hold p a rs\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq diseqs_hold_def)
  apply (blast dest: wf_atom)+
  done

definition theory_check_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('s, Model option, 'abort) function_contract\<close> where
  \<open>theory_check_contract p a \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length a = length (Problem_atoms p)\<rangle> in
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
          \<langle>cc_inv p (asserted p a (length (Problem_atoms p))) rs \<and> closed p rs \<and>
           length rs = length (Problem_terms p)\<rangle>) \<star>
        \<langle>length a = length (Problem_atoms p) \<and> wf_problem p \<and> sizes_ok p\<rangle> in
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
      simp add: sizes_ok_def)
  apply (auto intro: theory_none theory_some model_of_vals_ok simp add: sizes_ok_def)
  apply ((metis theory_none)+)?
  done

lemma theory_check_spec:
  shows \<open>\<Gamma>; theory_check p a \<Turnstile>\<^sub>F theory_check_contract p a\<close>
  apply (crush_boot f: theory_check_def contract: theory_check_contract_def)
  apply (crush_base specs add: init_rep_spec assert_eqs_spec close_spec finish_spec
      contracts add: init_rep_contract_def assert_eqs_contract_def close_contract_def finish_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto intro: cc_inv_init64 cc_inv_init cc_inv_length)
  done

subsection \<open>Search\<close>

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>search\<close>. Its precondition requires fewer than \<open>k\<close> atoms
  to remain unassigned, so the innermost function is never called.\<close>
definition search_contract :: \<open>nat \<Rightarrow> Problem \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> ('s, Model option, 'abort) function_contract\<close> where
  \<open>search_contract k p a i \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length a = length (Problem_atoms p) \<and> unat i \<le> length a \<and>
         length a - unat i < k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           None \<Rightarrow> \<not> ext_ok p a (unat i)
         | Some m \<Rightarrow> problem_true (model_interp m) p \<and> model_vals_ok p m\<rangle> in
     make_function_contract pre post\<close>

lemma search_rec_step_spec:
  assumes \<open>\<And>a i. \<Gamma>; R p a i \<Turnstile>\<^sub>F search_contract k p a i\<close>
  shows \<open>\<Gamma>; search_rec_step R p a i \<Turnstile>\<^sub>F search_contract (Suc k) p a i\<close>
  apply (crush_boot f: search_rec_step_def contract: search_contract_def)
  apply (crush_base specs add: assms prop_holds_spec theory_check_spec
      contracts add: search_contract_def prop_holds_contract_def theory_check_contract_def
      simp add: unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq word64_eq_of_nat_iff)
  apply (auto simp add: unat_word_Suc63 unat_of_nat_eq Option.is_none_def split: option.splits
      intro: search_step_none)
  apply (auto dest: search_leaf_none search_leaf_theory_none search_leaf_some)
  apply (metis ext_ok_step le_neq_implies_less)
  apply (metis ext_ok_all)
  apply (blast dest: wf_lit)
  done

lemma search_rec_spec:
  shows \<open>\<Gamma>; (search_rec_step ^^ k) R p a i \<Turnstile>\<^sub>F search_contract k p a i\<close>
proof (induction k arbitrary: a i)
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
  shows \<open>\<Gamma>; search p a i \<Turnstile>\<^sub>F search_contract urust_fuel p a i\<close>
  unfolding search_def by (rule search_rec_spec)

subsection \<open>The top-level contract\<close>

lemma solve_spec:
  assumes fuel: \<open>length (Problem_atoms p) < urust_fuel\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
  apply (crush_boot f: solve_def contract: solve_contract_def)
  apply (crush_base specs add: search_spec contracts add: search_contract_def split!: option.splits
      simp add: fuel unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq ext_ok_start Answer_Sat_mk_def)
  done

text \<open>The contract of \<^verbatim>\<open>solve\<close> with, for a model, the bound on its values and arguments.\<close>
definition solve_contract_vals :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract_vals p \<equiv>
     let pre = can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> problem_true (model_interp m) p \<and>
             (\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms p) \<and>
                (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms p)))
         | Answer_Unsat \<Rightarrow> \<not> satisfiable p\<rangle> in
     make_function_contract pre post\<close>

lemma solve_vals_spec:
  assumes fuel: \<open>length (Problem_atoms p) < urust_fuel\<close>
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract_vals p\<close>
  apply (crush_boot f: solve_def contract: solve_contract_vals_def)
  apply (crush_base specs add: search_spec contracts add: search_contract_def split!: option.splits
      simp add: fuel unat_of_nat_lt63 sizes_ok_def unat_of_nat_eq ext_ok_start Answer_Sat_mk_def)
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

text \<open>The same statement for \<^const>\<open>QFUF_ctx.solve_contract_vals\<close>.\<close>
theorem solve_correct_vals:
  shows \<open>\<forall>p. wf_problem p \<and> sizes_ok p \<longrightarrow>
           (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F QFUF_ctx.solve_contract_vals can_alloc_reference p)\<close>
proof (intro allI impI)
  fix p
  have \<open>\<Gamma>; solve fuel p \<Turnstile>\<^sub>F QFUF_ctx.solve_contract_vals can_alloc_reference p\<close>
    if \<open>length (Problem_atoms p) < fuel\<close> for fuel
    by (rule QFUF_ctx.solve_vals_spec[OF QFUF_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solve fuel p \<Turnstile>\<^sub>F QFUF_ctx.solve_contract_vals can_alloc_reference p\<close>
    by (intro exI[of _ \<open>length (Problem_atoms p) + 1\<close>]) simp
qed

end

end
