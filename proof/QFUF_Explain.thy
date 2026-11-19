theory QFUF_Explain
  imports QFUF_Contracts
begin

section \<open>Contracts of the explanation of a closure conflict\<close>

context QFUF_ctx
begin

text \<open>The explanation (\<^verbatim>\<open>explain\<close>) is a heuristic: it reads a small set of atoms off a
  logged closure, and then confirms it with \<^verbatim>\<open>rows_join\<close>, a closure restricted to some
  terms. Only the confirmation matters for soundness: a restricted closure still only joins terms
  that the congruence closure joins. The heuristic's functions are proved not to fail; their
  results only need the right lengths.\<close>

subsection \<open>The restricted closure\<close>

definition scan_row_in_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      64 word list \<Rightarrow> 64 word \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_row_in_contract p rows rep g rs i E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p E rs \<and> unat i < length (Problem_terms p) \<and> length rows = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_row_in_spec:
  shows \<open>\<Gamma>; scan_row_in p rows rep i \<Turnstile>\<^sub>F scan_row_in_contract p rows rep g rs i E\<close>
  apply (crush_boot f: scan_row_in_def contract: scan_row_in_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs'\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: congruent_spec merge_spec contracts add: congruent_contract_def merge_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_length intro: cc_inv_merge args_len_lt dest: wf_args_lt_length)
    apply (auto simp add: cc_inv_def sizes_ok_def intro: args_len_lt)
    apply (meson wf_args order.strict_trans)+
    done
  done

definition scan_rows_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      64 word list \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>scan_rows_contract p rows rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p E rs \<and> length rows = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) in
     make_function_contract pre post\<close>

lemma scan_rows_spec:
  shows \<open>\<Gamma>; scan_rows p rows rep \<Turnstile>\<^sub>F scan_rows_contract p rows rep g rs E\<close>
  apply (crush_boot f: scan_rows_def contract: scan_rows_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c g' rs'. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star>
                 \<langle>cc_inv p E rs'\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: scan_row_in_spec contracts add: scan_row_in_contract_def
        simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
    apply (auto simp add: cc_inv_def sizes_ok_def)
    done
  done

definition close_rows_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      64 word list \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>close_rows_contract p rows rep g rs E \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star>
        \<langle>cc_inv p E rs \<and> length rows = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>) in
     make_function_contract pre post\<close>

lemma close_rows_spec:
  shows \<open>\<Gamma>; close_rows p rows rep \<Turnstile>\<^sub>F close_rows_contract p rows rep g rs E\<close>
  apply (crush_boot f: close_rows_def contract: close_rows_contract_def)
  apply (crush_base simp add: cc_inv_def sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>cc_inv p E rs'\<rangle>)\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: scan_rows_spec contracts add: scan_rows_contract_def
      simp add: unat_of_nat_eq less_Suc_eq cc_inv_length)
  apply (auto simp add: cc_inv_def sizes_ok_def rep_ok_def unat_len_plus_one)
  done

definition same_class_contract :: \<open>64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>same_class_contract rs a b \<equiv>
     let pre = can_alloc_reference \<star> \<langle>unat a < length rs \<and> unat b < length rs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (rs ! unat a = rs ! unat b)\<rangle> in
     make_function_contract pre post\<close>

lemma same_class_spec:
  shows \<open>\<Gamma>; same_class rs a b \<Turnstile>\<^sub>F same_class_contract rs a b\<close>
  apply (crush_boot f: same_class_def contract: same_class_contract_def)
  apply crush_base
  done

text \<open>As for \<^const>\<open>finish\<close>, the state of \<open>rep\<close> is existentially quantified inside the
  contract.\<close>
definition joined_contract :: \<open>Problem \<Rightarrow> 64 word \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      (nat \<times> nat) set \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>joined_contract p k rep E \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p E rs\<rangle>) \<star>
        \<langle>unat k < length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs) \<star>
        \<langle>r \<longrightarrow> (unat (Atom_lhs (Problem_atoms p ! unat k)), unat (Atom_rhs (Problem_atoms p ! unat k))) \<in> cc p E\<rangle> in
     make_function_contract pre post\<close>

lemma joined_spec:
  shows \<open>\<Gamma>; joined p k rep \<Turnstile>\<^sub>F joined_contract p k rep E\<close>
  apply (crush_boot f: joined_def contract: joined_contract_def)
  apply (crush_base specs add: same_class_spec contracts add: same_class_contract_def)
  apply (auto intro: cc_inv_joined cc_inv_atom_lt)
  done

definition rows_join_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>rows_join_contract p e rows k \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length e = length (Problem_atoms p) \<and> length rows = length (Problem_terms p) \<and>
         unat k < length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r \<longrightarrow> (unat (Atom_lhs (Problem_atoms p ! unat k)), unat (Atom_rhs (Problem_atoms p ! unat k)))
                 \<in> cc p (asserted p e (length (Problem_atoms p)))\<rangle> in
     make_function_contract pre post\<close>

lemma rows_join_spec:
  shows \<open>\<Gamma>; rows_join p e rows k \<Turnstile>\<^sub>F rows_join_contract p e rows k\<close>
  apply (crush_boot f: rows_join_def contract: rows_join_contract_def)
  apply (crush_base specs add: init_rep_spec assert_eqs_spec close_rows_spec
      joined_spec[where E=\<open>asserted p e (length (Problem_atoms p))\<close>]
      contracts add: init_rep_contract_def assert_eqs_contract_def close_rows_contract_def joined_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto simp add: sizes_ok_def unat_of_nat_lt63 intro: cc_inv_init64 cc_inv_init cc_inv_length)
  done

end

end
