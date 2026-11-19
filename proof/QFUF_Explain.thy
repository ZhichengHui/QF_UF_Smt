theory QFUF_Explain
  imports QFUF_Contracts
begin

section \<open>Contracts of the explanation of a closure conflict\<close>

lemma unat_of_nat_le:
  \<open>unat (word_of_nat n :: 64 word) \<le> n\<close>
  by (simp add: unat_of_nat)

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

definition set_at_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>set_at_contract v g vs i x \<equiv>
     let pre = can_alloc_reference \<star> v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' vs'. v \<mapsto>\<langle>\<top>\<rangle> g'\<down>vs' \<star> \<langle>length vs' = length vs\<rangle>) in
     make_function_contract pre post\<close>

lemma set_at_spec:
  shows \<open>\<Gamma>; set_at v i x \<Turnstile>\<^sub>F set_at_contract v g vs i x\<close>
  apply (crush_boot f: set_at_def contract: set_at_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (meson order_less_le_trans unat_of_nat_le)+
  done

definition set_true_contract :: \<open>('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> bool list \<Rightarrow>
      64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>set_true_contract v g vs i \<equiv>
     let pre = can_alloc_reference \<star> v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' vs'. v \<mapsto>\<langle>\<top>\<rangle> g'\<down>vs' \<star> \<langle>length vs' = length vs\<rangle>) in
     make_function_contract pre post\<close>

lemma set_true_spec:
  shows \<open>\<Gamma>; set_true v i \<Turnstile>\<^sub>F set_true_contract v g vs i\<close>
  apply (crush_boot f: set_true_def contract: set_true_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (meson order_less_le_trans unat_of_nat_le)+
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

end

end
