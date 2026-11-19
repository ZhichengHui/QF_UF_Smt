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

subsection \<open>Bounds-checked access\<close>

text \<open>The callers use these functions only where any value would do, so the contracts state
  only that they do not fail and keep the length.\<close>

definition get_or_contract :: \<open>64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>get_or_contract v i d \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>_. can_alloc_reference in
     make_function_contract pre post\<close>

lemma get_or_spec:
  shows \<open>\<Gamma>; get_or v i d \<Turnstile>\<^sub>F get_or_contract v i d\<close>
  apply (crush_boot f: get_or_def contract: get_or_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (meson order_less_le_trans unat_of_nat_le)
  done

text \<open>The state of the vector is existentially quantified inside the contracts below, as for
  \<^const>\<open>finish\<close>; only its length is a parameter.\<close>
definition set_at_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> nat \<Rightarrow>
      64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>set_at_contract v n i x \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>length vs = n\<rangle>) in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>length vs = n\<rangle>) in
     make_function_contract pre post\<close>

lemma set_at_spec:
  shows \<open>\<Gamma>; set_at v i x \<Turnstile>\<^sub>F set_at_contract v n i x\<close>
  apply (crush_boot f: set_at_def contract: set_at_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (auto intro: unat_lt_len)
  done

definition set_true_contract :: \<open>('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> nat \<Rightarrow>
      64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>set_true_contract v n i \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>length vs = n\<rangle>) in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>length vs = n\<rangle>) in
     make_function_contract pre post\<close>

lemma set_true_spec:
  shows \<open>\<Gamma>; set_true v i \<Turnstile>\<^sub>F set_true_contract v n i\<close>
  apply (crush_boot f: set_true_def contract: set_true_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (auto intro: unat_lt_len)
  done

subsection \<open>The merge log\<close>

text \<open>The functions that log a closure only keep the length of the representative list; the
  logged edges are not constrained.\<close>

definition log_atoms_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>log_atoms_contract p t rep g rs xs gx xv ys gy yv ls gl lv \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p) \<and> length rs = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_atoms_spec:
  shows \<open>\<Gamma>; log_atoms p t rep xs ys ls \<Turnstile>\<^sub>F log_atoms_contract p t rep g rs xs gx xv ys gy yv ls gl lv\<close>
  apply (crush_boot f: log_atoms_def contract: log_atoms_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: merge_spec contracts add: merge_contract_def inline: vec_push_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: unat_of_nat_lt63 dest: wf_atom)
  done

definition log_row_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>log_row_contract p rep g rs xs gx xv ys gy yv ls gl lv i \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p) \<and> unat i < length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_row_spec:
  shows \<open>\<Gamma>; log_row p rep xs ys ls i \<Turnstile>\<^sub>F log_row_contract p rep g rs xs gx xv ys gy yv ls gl lv i\<close>
  apply (crush_boot f: log_row_def contract: log_row_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: congruent_spec merge_spec contracts add: congruent_contract_def merge_contract_def
        inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq)
    apply (auto simp add: sizes_ok_def intro: args_len_lt dest: wf_args_lt_length)
    apply (meson wf_args order.strict_trans)+
    done
  done

definition log_scan_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>log_scan_contract p rep g rs xs gx xv ys gy yv ls gl lv  \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_scan_spec:
  shows \<open>\<Gamma>; log_scan p rep xs ys ls \<Turnstile>\<^sub>F log_scan_contract p rep g rs xs gx xv ys gy yv ls gl lv\<close>
  apply (crush_boot f: log_scan_def contract: log_scan_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: log_row_spec contracts add: log_row_contract_def
        simp add: unat_of_nat_eq less_Suc_eq)
    apply (auto simp add: sizes_ok_def)
    done
  done

definition log_close_contract :: \<open>Problem \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>log_close_contract p rep g rs xs gx xv ys gy yv ls gl lv  \<equiv>
     let pre = can_alloc_reference \<star> rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> xs \<mapsto>\<langle>\<top>\<rangle> gx\<down>xv \<star> ys \<mapsto>\<langle>\<top>\<rangle> gy\<down>yv \<star> ls \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) in
     make_function_contract pre post\<close>

lemma log_close_spec:
  shows \<open>\<Gamma>; log_close p rep xs ys ls \<Turnstile>\<^sub>F log_close_contract p rep g rs xs gx xv ys gy yv ls gl lv\<close>
  apply (crush_boot f: log_close_def contract: log_close_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' rs'. rep \<mapsto>\<langle>\<top>\<rangle> g'\<down>rs' \<star> \<langle>length rs' = length (Problem_terms p)\<rangle>) \<star>
        (\<Squnion>g' v. xs \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ys \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. ls \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: log_scan_spec contracts add: log_scan_contract_def
      simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto simp add: sizes_ok_def unat_len_plus_one)
  done

definition merge_log_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow>
      ('s, 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  \<open>merge_log_contract p t \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>_. can_alloc_reference in
     make_function_contract pre post\<close>

lemma merge_log_spec:
  shows \<open>\<Gamma>; merge_log p t \<Turnstile>\<^sub>F merge_log_contract p t\<close>
  apply (crush_boot f: merge_log_def contract: merge_log_contract_def)
  apply (crush_base specs add: init_rep_spec log_atoms_spec log_close_spec
      contracts add: init_rep_contract_def log_atoms_contract_def log_close_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto simp add: sizes_ok_def unat_of_nat_lt63)
  done

subsection \<open>The search for a path in the merge log\<close>

definition bfs_round_contract :: \<open>64 word \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>bfs_round_contract n xs ys pv pe \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     make_function_contract pre post\<close>

lemma bfs_round_spec:
  shows \<open>\<Gamma>; bfs_round n xs ys pv pe \<Turnstile>\<^sub>F bfs_round_contract n xs ys pv pe\<close>
  apply (crush_boot f: bfs_round_def contract: bfs_round_contract_def)
  apply crush_base
  subgoal for changed_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gc c. changed_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c) \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v')\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec set_at_spec contracts add: get_or_contract_def set_at_contract_def
        simp add: word_less_nat_alt)
    apply (auto intro: unat_lt_len unat_idx_lt)
    done
  done

definition bfs_rounds_contract :: \<open>64 word \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> W W
      ('s, unit, 'abort) function_contract\<close> where
  \<open>bfs_rounds_contract n xs ys b pv pe \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     make_function_contract pre post\<close>

lemma bfs_rounds_spec:
  shows \<open>\<Gamma>; bfs_rounds n xs ys b pv pe \<Turnstile>\<^sub>F bfs_rounds_contract n xs ys b pv pe\<close>
  apply (crush_boot f: bfs_rounds_def contract: bfs_rounds_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v')\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v'. pv \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. pe \<mapsto>\<langle>\<top>\<rangle> g'\<down>v')\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: get_or_spec bfs_round_spec contracts add: get_or_contract_def bfs_round_contract_def)
  done

definition bfs_contract :: \<open>64 word \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
      ('s, 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  \<open>bfs_contract n xs ys a b \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>_. can_alloc_reference in
     make_function_contract pre post\<close>

lemma bfs_spec:
  shows \<open>\<Gamma>; bfs n xs ys a b \<Turnstile>\<^sub>F bfs_contract n xs ys a b\<close>
  apply (crush_boot f: bfs_def contract: bfs_contract_def)
  apply (crush_base specs add: set_at_spec[where n=\<open>unat n\<close>] bfs_rounds_spec
      contracts add: set_at_contract_def bfs_rounds_contract_def)
  done

definition push_args_contract :: \<open>Problem \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>push_args_contract p u v qa qb \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> \<langle>sizes_ok p\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     make_function_contract pre post\<close>

lemma push_args_spec:
  shows \<open>\<Gamma>; push_args p u v qa qb \<Turnstile>\<^sub>F push_args_contract p u v qa qb\<close>
  apply (crush_boot f: push_args_def contract: push_args_contract_def)
  apply (crush_base simp add: sizes_ok_def word_less_nat_alt unat_of_nat_lt63)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v')\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base inline: vec_push_def simp add: sizes_ok_def word_less_nat_alt unat_of_nat_lt63 unat_of_nat_eq)
  apply (auto simp add: sizes_ok_def intro: unat_idx_lt)
  done

definition walk_contract :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> 64 word \<Rightarrow> ('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> nat \<Rightarrow> ('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> nat \<Rightarrow> B ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>walk_contract p xs ys ls pv pe a b e ne rows nr used qa qb \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g' v'. e \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = ne\<rangle>) \<star> (\<Squnion>g' v'. rows \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = nr\<rangle>) \<star>
        (\<Squnion>g' v'. used \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> \<langle>sizes_ok p\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' v'. e \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = ne\<rangle>) \<star> (\<Squnion>g' v'. rows \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = nr\<rangle>) \<star>
        (\<Squnion>g' v'. used \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') in
     make_function_contract pre post\<close>

lemma walk_spec:
  shows \<open>\<Gamma>; walk p xs ys ls pv pe a b e rows used qa qb \<Turnstile>\<^sub>F walk_contract p xs ys ls pv pe a b e ne rows nr used qa qb\<close>
  apply (crush_boot f: walk_def contract: walk_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for x_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gx x. x_ref \<mapsto>\<langle>\<top>\<rangle> gx\<down>x) \<star> (\<Squnion>g' v'. e \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = ne\<rangle>) \<star> (\<Squnion>g' v'. rows \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>length v' = nr\<rangle>) \<star>
        (\<Squnion>g' v'. used \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qa \<mapsto>\<langle>\<top>\<rangle> g'\<down>v') \<star> (\<Squnion>g' v'. qb \<mapsto>\<langle>\<top>\<rangle> g'\<down>v')\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec set_true_spec push_args_spec
        contracts add: get_or_contract_def set_true_contract_def push_args_contract_def
        simp add: word_less_nat_alt sizes_ok_def)
    apply (auto simp add: sizes_ok_def intro: unat_lt_len)
    done
  done

definition path_explain_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow>
      ('s, bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  \<open>path_explain_contract p t k \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p) \<and> unat k < length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>length (fst r) = length (Problem_atoms p) \<and> length (fst (snd r)) = length (Problem_terms p)\<rangle> in
     make_function_contract pre post\<close>

lemma path_explain_spec:
  shows \<open>\<Gamma>; path_explain p t k \<Turnstile>\<^sub>F path_explain_contract p t k\<close>
  apply (crush_boot f: path_explain_def contract: path_explain_contract_def)
  apply (crush_base specs add: merge_log_spec contracts add: merge_log_contract_def inline: vec_push_def
      simp add: sizes_ok_def unat_of_nat_lt63)
  subgoal for xs ys ls e_ref rows_ref used_ref qa_ref qb_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' v. e_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_atoms p)\<rangle>) \<star>
        (\<Squnion>g' v. rows_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v \<star> \<langle>length v = length (Problem_terms p)\<rangle>) \<star> (\<Squnion>g' v. used_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star>
        (\<Squnion>g' v. qa_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v) \<star> (\<Squnion>g' v. qb_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec bfs_spec
        walk_spec[where ne=\<open>length (Problem_atoms p)\<close> and nr=\<open>length (Problem_terms p)\<close>]
        contracts add: get_or_contract_def bfs_contract_def walk_contract_def
        simp add: sizes_ok_def unat_of_nat_lt63)
    apply (auto simp add: sizes_ok_def unat_of_nat_lt63)
    done
  done

definition explain_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>explain_contract p t k \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p) \<and> unat k < length (Problem_atoms p) \<and>
         (unat (Atom_lhs (Problem_atoms p ! unat k)), unat (Atom_rhs (Problem_atoms p ! unat k)))
           \<in> cc p (asserted p t (length (Problem_atoms p)))\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>length r = length (Problem_atoms p) \<and>
         (unat (Atom_lhs (Problem_atoms p ! unat k)), unat (Atom_rhs (Problem_atoms p ! unat k)))
           \<in> cc p (asserted p r (length (Problem_atoms p)))\<rangle> in
     make_function_contract pre post\<close>

lemma explain_spec:
  shows \<open>\<Gamma>; explain p t k \<Turnstile>\<^sub>F explain_contract p t k\<close>
  apply (crush_boot f: explain_def contract: explain_contract_def)
  apply (crush_base specs add: path_explain_spec rows_join_spec
      contracts add: path_explain_contract_def rows_join_contract_def)
  done

subsection \<open>Learned clauses\<close>

text \<open>The literals of the clause that \<^verbatim>\<open>conflict_clause\<close> builds from \<open>e\<close> and \<open>k\<close>.\<close>
definition conflict_lits :: \<open>bool list \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> Lit set\<close> where
  \<open>conflict_lits e k i \<equiv> insert (make_Lit k True) {make_Lit (word_of_nat j) False | j. j < i \<and> e ! j}\<close>

lemma conflict_lits_Suc:
  \<open>conflict_lits e k (Suc i) = conflict_lits e k i \<union> (if e ! i then {make_Lit (word_of_nat i) False} else {})\<close>
  unfolding conflict_lits_def by (auto simp add: less_Suc_eq)

definition conflict_clause_contract :: \<open>bool list \<Rightarrow> 64 word \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>conflict_clause_contract e k \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length e < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>set (Clause_lits r) = conflict_lits e k (length e) \<and> length (Clause_lits r) \<le> length e + 1\<rangle> in
     make_function_contract pre post\<close>

lemma conflict_clause_spec:
  shows \<open>\<Gamma>; conflict_clause e k \<Turnstile>\<^sub>F conflict_clause_contract e k\<close>
  apply (crush_boot f: conflict_clause_def contract: conflict_clause_contract_def)
  apply (crush_base inline: vec_push_def)
  subgoal for lits_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' ls. lits_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ls \<star>
                 \<langle>set ls = conflict_lits e k i \<and> length ls \<le> i + 1\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq conflict_lits_Suc)
    apply (auto simp add: conflict_lits_def unat_of_nat_eq)
    done
  done

lemma conflict_lits_clause_ok:
  assumes wf: \<open>wf_problem p\<close> and k: \<open>unat k < length (Problem_atoms p)\<close>
      and len: \<open>length e = length (Problem_atoms p)\<close> \<open>length e < 2^63\<close>
      and cc: \<open>(unat (Atom_lhs (Problem_atoms p ! unat k)), unat (Atom_rhs (Problem_atoms p ! unat k)))
                 \<in> cc p (asserted p e (length (Problem_atoms p)))\<close>
      and c: \<open>set (Clause_lits c) = conflict_lits e k (length e)\<close>
  shows \<open>clause_ok p c\<close>
proof (rule conflict_clause_ok[OF wf k cc])
  have j: \<open>unat (word_of_nat j :: 64 word) = j\<close> if \<open>j < length e\<close> for j
    using that len(2) by (simp add: unat_of_nat_eq)
  show \<open>\<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (Problem_atoms p)\<close>
    using c k len j by (auto simp add: conflict_lits_def)
  show \<open>\<exists>l \<in> set (Clause_lits c). unat (Lit_atom l) = unat k \<and> Lit_pos l\<close>
    using c by (auto simp add: conflict_lits_def)
  show \<open>\<forall>j < length (Problem_atoms p). e ! j \<longrightarrow>
          (\<exists>l \<in> set (Clause_lits c). unat (Lit_atom l) = j \<and> \<not> Lit_pos l)\<close>
    using c len j by (auto simp add: conflict_lits_def)
qed

definition learn_contract :: \<open>Clause list \<Rightarrow> Clause \<Rightarrow> ('s, Clause list, 'abort) function_contract\<close> where
  \<open>learn_contract l c \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = l @ [c]\<rangle> in
     make_function_contract pre post\<close>

lemma learn_spec:
  shows \<open>\<Gamma>; learn l c \<Turnstile>\<^sub>F learn_contract l c\<close>
  apply (crush_boot f: learn_def contract: learn_contract_def)
  apply (crush_base inline: vec_push_def)
  done

end

end
