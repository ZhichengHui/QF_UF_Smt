theory QFUF_Proof
  imports QFUF_Pure.QFUF_Pure
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

text \<open>The invariant of the representative list during the closure, for the asserted pairs \<open>E\<close>.\<close>
definition cc_inv :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>cc_inv p E rs \<equiv> wf_problem p \<and> sizes_ok p \<and> rep_ok p E rs \<and>
     (\<forall>(i, j) \<in> E. i < length (Problem_terms p) \<and> j < length (Problem_terms p))\<close>

lemma cc_inv_merge:
  assumes \<open>cc_inv p E rs\<close> \<open>i < length rs\<close> \<open>j < length rs\<close> \<open>congruent_p p rs i j\<close>
  shows \<open>cc_inv p E (merge_list rs i j)\<close>
  using assms rep_ok_merge_congruent unfolding cc_inv_def rep_ok_def by (metis length_merge_list)

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

end

end
