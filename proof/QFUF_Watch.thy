theory QFUF_Watch
  imports QFUF_Incremental
begin

section \<open>Unit propagation with watched literals, and the decision order\<close>

text \<open>\<^verbatim>\<open>watch_pass\<close> sets atoms only through \<^verbatim>\<open>clause_unit\<close> on a clause of the problem or a
  learned one, so each atom it sets is implied by the assignment before it, and a clause it finds
  false refutes the assignment. The watch lists only choose which clauses it checks: their
  contracts claim nothing about them. Likewise the symbol index of the closure and the activity of
  the decision order claim nothing.\<close>

subsection \<open>Pure facts\<close>

text \<open>\<open>t1\<close>, \<open>f1\<close> extend \<open>t\<close>, \<open>f\<close> by atoms unset in \<open>t\<close>, \<open>f\<close>, and every interpretation that
  extends \<open>t\<close>, \<open>f\<close> and makes the problem true extends \<open>t1\<close>, \<open>f1\<close>.\<close>
definition ext_ok :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>ext_ok p t f t1 f1 \<equiv>
     length t1 = length t \<and> length f1 = length f \<and>
     (\<forall>j < length t. (t ! j \<longrightarrow> t1 ! j) \<and> (f ! j \<longrightarrow> f1 ! j) \<and>
        (t1 ! j \<and> \<not> t ! j \<longrightarrow> \<not> f ! j) \<and> (f1 ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j)) \<and>
     (pext p t f \<longrightarrow> pext p t1 f1)\<close>

lemma ext_ok_refl:
  \<open>ext_ok p t f t f\<close>
  unfolding ext_ok_def by simp

lemma ext_ok_trans:
  assumes a: \<open>ext_ok p t f t1 f1\<close> and b: \<open>ext_ok p t1 f1 t2 f2\<close> and len: \<open>length f = length t\<close>
  shows \<open>ext_ok p t f t2 f2\<close>
proof -
  have la: \<open>length t1 = length t\<close> \<open>length f1 = length f\<close>
   and ja: \<open>\<forall>j < length t. (t ! j \<longrightarrow> t1 ! j) \<and> (f ! j \<longrightarrow> f1 ! j) \<and>
        (t1 ! j \<and> \<not> t ! j \<longrightarrow> \<not> f ! j) \<and> (f1 ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j)\<close>
   and pa: \<open>pext p t f \<longrightarrow> pext p t1 f1\<close>
    using a unfolding ext_ok_def by blast+
  have lb: \<open>length t2 = length t1\<close> \<open>length f2 = length f1\<close>
   and jb: \<open>\<forall>j < length t1. (t1 ! j \<longrightarrow> t2 ! j) \<and> (f1 ! j \<longrightarrow> f2 ! j) \<and>
        (t2 ! j \<and> \<not> t1 ! j \<longrightarrow> \<not> f1 ! j) \<and> (f2 ! j \<and> \<not> f1 ! j \<longrightarrow> \<not> t1 ! j)\<close>
   and pb: \<open>pext p t1 f1 \<longrightarrow> pext p t2 f2\<close>
    using b unfolding ext_ok_def by blast+
  have j: \<open>(t ! j \<longrightarrow> t2 ! j) \<and> (f ! j \<longrightarrow> f2 ! j) \<and>
        (t2 ! j \<and> \<not> t ! j \<longrightarrow> \<not> f ! j) \<and> (f2 ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j)\<close> if \<open>j < length t\<close> for j
  proof -
    have \<open>j < length t1\<close> using that la by simp
    then show ?thesis using ja jb that by blast
  qed
  have l: \<open>length t2 = length t\<close> \<open>length f2 = length f\<close> using la lb by simp_all
  show ?thesis
    unfolding ext_ok_def using l pa pb j by blast
qed

lemma ext_ok_fuel:
  assumes ok: \<open>ext_ok p t f t1 f1\<close> and len: \<open>length f = length t\<close>
      and d: \<open>t1 \<noteq> t \<or> f1 \<noteq> f\<close>
      and k: \<open>unset_count t f < Suc k\<close>
  shows \<open>unset_count t1 f1 < k\<close>
proof -
  let ?S = \<open>{j. j < length t \<and> \<not> t ! j \<and> \<not> f ! j}\<close> and ?S1 = \<open>{j. j < length t1 \<and> \<not> t1 ! j \<and> \<not> f1 ! j}\<close>
  have l1: \<open>length t1 = length t\<close> \<open>length f1 = length f\<close> using ok unfolding ext_ok_def by simp_all
  have sub: \<open>?S1 \<subseteq> ?S\<close> using ok l1 unfolding ext_ok_def by auto
  have \<open>\<exists>i < length t. t ! i \<noteq> t1 ! i \<or> f ! i \<noteq> f1 ! i\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>i < length t. t ! i \<noteq> t1 ! i \<or> f ! i \<noteq> f1 ! i)\<close>
    then have \<open>t1 = t\<close> \<open>f1 = f\<close> using len l1 by (auto intro!: nth_equalityI)
    then show False using d by simp
  qed
  then obtain i where i: \<open>i \<in> ?S\<close> \<open>i \<notin> ?S1\<close>
    using ok len l1 unfolding ext_ok_def by (metis (mono_tags, lifting) mem_Collect_eq)
  have \<open>card ?S1 < card ?S\<close>
    using sub i by (intro psubset_card_mono) auto
  then show ?thesis using k unfolding unset_count_def by simp
qed

lemma ext_ok_rep_for:
  assumes ok: \<open>ext_ok p t f t1 f1\<close> and len: \<open>length t = length (Problem_atoms p)\<close> and r: \<open>rep_for p t rs\<close>
  shows \<open>rep_for p t1 rs\<close>
proof (rule rep_for_mono[OF r])
  have \<open>\<forall>j < length t. t ! j \<longrightarrow> t1 ! j\<close>
    using ok unfolding ext_ok_def by blast
  then show \<open>\<forall>j < length (Problem_atoms p). t ! j \<longrightarrow> t1 ! j\<close>
    using len by simp
qed

lemma ext_ok_none:
  \<open>ext_ok p t f t1 f1 \<Longrightarrow> \<not> pext p t1 f1 \<Longrightarrow> \<not> pext p t f\<close>
  unfolding ext_ok_def by blast

lemma ext_ok_len:
  \<open>ext_ok p t f t1 f1 \<Longrightarrow> length t1 = length t\<close>
  \<open>ext_ok p t f t1 f1 \<Longrightarrow> length f1 = length f\<close>
  unfolding ext_ok_def by simp_all

context QFUF_ctx
begin

subsection \<open>Propagation steps\<close>

lemma idx_lt_len:
  assumes \<open>i < unat (word64_of_nat n :: 64 word)\<close> \<open>n < 2^63\<close> \<open>\<not> word64_of_nat m \<le> (word64_of_nat i :: 64 word)\<close>
  shows \<open>unat (word64_of_nat i :: 64 word) < m\<close>
proof -
  have \<open>i < n\<close> using assms(1) by (rule unat_lt_len)
  then have \<open>i < 2^63\<close> using assms(2) by simp
  then have i: \<open>unat (word64_of_nat i :: 64 word) = i\<close> by (simp add: unat_of_nat_eq)
  have \<open>unat (word64_of_nat i :: 64 word) < unat (word64_of_nat m :: 64 word)\<close>
    using assms(3) by (simp add: not_le word_less_nat_alt)
  then show ?thesis using unat_of_nat_le[of m] by simp
qed

lemma ext_ok_unit:
  assumes \<open>find_result p t f u\<close> \<open>unat (Lit_atom u) < length t\<close> \<open>length f = length t\<close>
  shows \<open>Lit_pos u \<Longrightarrow> ext_ok p t f (t[unat (Lit_atom u) := True]) f\<close>
    and \<open>\<not> Lit_pos u \<Longrightarrow> ext_ok p t f t (f[unat (Lit_atom u) := True])\<close>
  using assms unfolding ext_ok_def find_result_def lit_unset_def
  by (auto simp add: nth_list_update)

lemma ext_ok_step:
  assumes ok: \<open>ext_ok p t f t1 f1\<close> and len: \<open>length f = length t\<close>
      and u: \<open>find_result p t1 f1 u\<close> \<open>unat (Lit_atom u) < length t1\<close>
  shows \<open>Lit_pos u \<Longrightarrow> ext_ok p t f (t1[unat (Lit_atom u) := True]) f1\<close>
    and \<open>\<not> Lit_pos u \<Longrightarrow> ext_ok p t f t1 (f1[unat (Lit_atom u) := True])\<close>
proof -
  have l: \<open>length f1 = length t1\<close> using ok len unfolding ext_ok_def by simp
  show \<open>Lit_pos u \<Longrightarrow> ext_ok p t f (t1[unat (Lit_atom u) := True]) f1\<close>
    using ext_ok_trans[OF ok ext_ok_unit(1)[of p t1 f1 u, OF u l] len] by simp
  show \<open>\<not> Lit_pos u \<Longrightarrow> ext_ok p t f t1 (f1[unat (Lit_atom u) := True])\<close>
    using ext_ok_trans[OF ok ext_ok_unit(2)[of p t1 f1 u, OF u l] len] by simp
qed

lemma ext_ok_conflict:
  \<open>ext_ok p t f t1 f1 \<Longrightarrow> find_result p t1 f1 u \<Longrightarrow> unat (Lit_atom u) = length t1 \<Longrightarrow> Lit_pos u \<Longrightarrow>
   \<not> pext p t f\<close>
  unfolding find_result_def ext_ok_def by blast


lemma ext_ok_conflict':
  \<open>ext_ok p t f t1 f1 \<Longrightarrow> find_result p t1 f1 u \<Longrightarrow> \<not> unat (Lit_atom u) < length t1 \<Longrightarrow> Lit_pos u \<Longrightarrow>
   \<not> pext p t f\<close>
  unfolding find_result_def ext_ok_def by (meson le_neq_implies_less)

subsection \<open>Helpers\<close>

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


definition set_true_val_contract :: \<open>('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> bool list \<Rightarrow>
      64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>set_true_val_contract v g vs i \<equiv>
     let pre = can_alloc_reference \<star> v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>length vs < 2^64\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star>
        (\<Squnion>g'. v \<mapsto>\<langle>\<top>\<rangle> g'\<down>(if unat i < length vs then vs[unat i := True] else vs)) in
     make_function_contract pre post\<close>

lemma set_true_val_spec:
  shows \<open>\<Gamma>; set_true v i \<Turnstile>\<^sub>F set_true_val_contract v g vs i\<close>
  apply (crush_boot f: set_true_def contract: set_true_val_contract_def)
  apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq)
  done

definition trivial_contract :: \<open>('s, 'r, 'abort) function_contract\<close> where
  \<open>trivial_contract \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma lit_code_spec:
  shows \<open>\<Gamma>; lit_code l \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: lit_code_def contract: trivial_contract_def)
  apply (crush_base specs add: sat_add_ok_spec contracts add: sat_add_ok_contract_def)
  done

lemma lit_true_at_spec:
  shows \<open>\<Gamma>; lit_true_at t f l \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: lit_true_at_def contract: trivial_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (auto dest: unat_lt_len)
  done

lemma lit_false_at_spec:
  shows \<open>\<Gamma>; lit_false_at t f l \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: lit_false_at_def contract: trivial_contract_def)
  apply (crush_base simp add: word_less_nat_alt)
  apply (auto dest: unat_lt_len)
  done

lemma one_spec:
  shows \<open>\<Gamma>; one x \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: one_def contract: trivial_contract_def)
  apply (crush_base inline: vec_push_def)
  done

subsection \<open>Unit propagation\<close>

definition clause_unit_at_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('s, Lit, 'abort) function_contract\<close> where
  \<open>clause_unit_at_contract p l c t f \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and>
         length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>find_result p t f r\<rangle> in
     make_function_contract pre post\<close>

lemma clause_unit_at_spec:
  shows \<open>\<Gamma>; clause_unit_at p l c t f \<Turnstile>\<^sub>F clause_unit_at_contract p l c t f\<close>
  apply (crush_boot f: clause_unit_at_def contract: clause_unit_at_contract_def)
  apply (crush_base specs add: clause_unit_spec contracts add: clause_unit_contract_def)
  apply (all \<open>insert clauses_ok_problem[of p]\<close>)
  apply (all \<open>(drule unat_lt_len[OF iffD1[OF word_less_nat_alt]])?\<close>)
  apply (auto simp add: sizes_ok_def unat_of_nat_lt63 intro: find_result_none)
  apply (auto simp add: clauses_ok_def clause_ok_def intro!: find_result_clause)
  done

text \<open>\<^verbatim>\<open>units_at\<close> extends the assignment by atoms that it implies, and its result is the index
  of a clause that refutes it, or 0.\<close>
definition units_at_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> bool list \<Rightarrow>
      ('addr, 'gv, bool list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> bool list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 64 word list \<Rightarrow>
      ('s, 64 word, 'abort) function_contract\<close> where
  \<open>units_at_contract p l cs t gt tv f gf fv lv glv vlv rs grs vrs ts gts vts q gq vq \<equiv>
     let pre = can_alloc_reference \<star> t \<mapsto>\<langle>\<top>\<rangle> gt\<down>tv \<star> f \<mapsto>\<langle>\<top>\<rangle> gf\<down>fv \<star>
        lv \<mapsto>\<langle>\<top>\<rangle> glv\<down>vlv \<star> rs \<mapsto>\<langle>\<top>\<rangle> grs\<down>vrs \<star> ts \<mapsto>\<langle>\<top>\<rangle> gts\<down>vts \<star> q \<mapsto>\<langle>\<top>\<rangle> gq\<down>vq \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length tv = length (Problem_atoms p) \<and>
         length fv = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        (\<Squnion>g1 tv' g2 fv'. t \<mapsto>\<langle>\<top>\<rangle> g1\<down>tv' \<star> f \<mapsto>\<langle>\<top>\<rangle> g2\<down>fv' \<star>
           \<langle>ext_ok p tv fv tv' fv' \<and> (r \<noteq> 0 \<longrightarrow> \<not> pext p tv fv)\<rangle>) \<star>
        (\<Squnion>g v. lv \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. rs \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. ts \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. q \<mapsto>\<langle>\<top>\<rangle> g\<down>v) in
     make_function_contract pre post\<close>

lemma units_at_spec:
  shows \<open>\<Gamma>; units_at p l cs t f lv rs ts q d s \<Turnstile>\<^sub>F units_at_contract p l cs t gt tv f gf fv lv glv vlv rs grs vrs ts gts vts q gq vq\<close>
  apply (crush_boot f: units_at_def contract: units_at_contract_def)
  apply crush_base
  subgoal for c_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star>
        (\<Squnion>gc cv g1 tv' g2 fv'. c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cv \<star> t \<mapsto>\<langle>\<top>\<rangle> g1\<down>tv' \<star> f \<mapsto>\<langle>\<top>\<rangle> g2\<down>fv' \<star>
           \<langle>ext_ok p tv fv tv' fv' \<and> (cv \<noteq> 0 \<longrightarrow> \<not> pext p tv fv)\<rangle>) \<star>
        (\<Squnion>g v. lv \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. rs \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. ts \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. q \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: clause_unit_at_spec set_true_val_spec set_at_any_spec sat_add_ok_spec
        contracts add: clause_unit_at_contract_def set_true_val_contract_def set_at_any_contract_def
          sat_add_ok_contract_def
        inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq)
    apply (all \<open>(frule ext_ok_len(1), frule ext_ok_len(2))?\<close>)
    apply (auto simp add: word_less_nat_alt unat_of_nat_lt63 sizes_ok_def dest: unat_lt_len intro: ext_ok_refl)
    apply (auto intro: ext_ok_step unat_idx_lt dest: ext_ok_conflict')
    done
  done

lemma all_ids_spec:
  shows \<open>\<Gamma>; all_ids n \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: all_ids_def contract: trivial_contract_def)
  apply crush_base
  subgoal for v_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. v_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def)
    done
  done

lemma root_ids_spec:
  shows \<open>\<Gamma>; root_ids p l s \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: root_ids_def contract: trivial_contract_def)
  apply (crush_base specs add: all_ids_spec sat_add_ok_spec contracts add: trivial_contract_def sat_add_ok_contract_def)
  done

lemma false_code_spec:
  shows \<open>\<Gamma>; false_code t a \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: false_code_def contract: trivial_contract_def)
  apply (crush_base specs add: sat_add_ok_spec contracts add: sat_add_ok_contract_def simp add: word_less_nat_alt)
  apply (auto dest: unat_lt_len)
  done

lemma watch_move_spec:
  shows \<open>\<Gamma>; watch_move c t f a b \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: watch_move_def contract: trivial_contract_def)
  apply (crush_base specs add: lit_true_at_spec contracts add: trivial_contract_def inline: cap_def
      simp add: word_less_nat_alt)
  apply (all \<open>(ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)?\<close>)
  apply (crush_base specs add: lit_false_at_spec lit_code_spec contracts add: trivial_contract_def inline: cap_def
      simp add: unat_of_nat_eq word_less_nat_alt)
  apply (auto dest: unat_lt_len intro: unat_idx_lt(1))
  done

lemma watch_move_at_spec:
  shows \<open>\<Gamma>; watch_move_at p l c t f a b \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: watch_move_at_def contract: trivial_contract_def)
  apply (crush_base specs add: watch_move_spec contracts add: trivial_contract_def inline: cap_def
      simp add: word_less_nat_alt not_less)
  apply (auto dest: unat_lt_len simp add: word_le_nat_alt)
  done

definition watch_visit_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  \<open>watch_visit_contract head nxt wl \<equiv>
     make_function_contract
       (can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v))
       (\<lambda>_. can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v))\<close>

lemma watch_visit_spec:
  shows \<open>\<Gamma>; watch_visit p l lc t f head nxt wl \<Turnstile>\<^sub>F watch_visit_contract head nxt wl\<close>
  apply (crush_boot f: watch_visit_def contract: watch_visit_contract_def)
  apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def inline: cap_def)
  subgoal for x xb xd xe cands_ref prev_ref r xa w_ref ra
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. cands_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. prev_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. w_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. cands_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. prev_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. w_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec watch_move_at_spec set_at_any_spec
        contracts add: get_or_contract_def trivial_contract_def set_at_any_contract_def inline: vec_push_def cap_def)
    subgoal by (rule ccontr) (simp add: not_le word_less_1)
    subgoal for i g v ga va gb gc vc gd ge ve raa rb
      using unat_lt2p[of \<open>word64_of_nat (length ra) :: 64 word\<close>] by (simp add: not_le word_less_nat_alt)
    done
  done

text \<open>\<^verbatim>\<open>watch_pass\<close>: the extended assignment, and a refuted one when it reports a falsified
  clause.\<close>
definition watch_pass_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, 64 word \<times> bool list \<times> bool list \<times> 64 word list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort)
        function_contract\<close> where
  \<open>watch_pass_contract p l t f head nxt wl \<equiv>
     let pre = can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and>
         length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        \<langle>ext_ok p t f (fst (snd r)) (fst (snd (snd r))) \<and> (fst r \<noteq> 0 \<longrightarrow> \<not> pext p t f)\<rangle> in
     make_function_contract pre post\<close>

lemma watch_pass_spec:
  shows \<open>\<Gamma>; watch_pass p l t f q0 lv rs ts head nxt wl d s \<Turnstile>\<^sub>F watch_pass_contract p l t f head nxt wl\<close>
  apply (crush_boot f: watch_pass_def contract: watch_pass_contract_def)
  apply (crush_base specs add: root_ids_spec units_at_spec contracts add: trivial_contract_def units_at_contract_def)
  subgoal for x xa xb xc xd xe t1_ref f1_ref lv_ref rs_ref ts_ref q_ref c0 g g1 ga tv' gb g2 xm fv' gc xn xo xp c_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>gc cv g1 tv' g2 fv'. c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cv \<star> t1_ref \<mapsto>\<langle>\<top>\<rangle> g1\<down>tv' \<star>
           f1_ref \<mapsto>\<langle>\<top>\<rangle> g2\<down>fv' \<star> \<langle>ext_ok p t f tv' fv' \<and> (cv \<noteq> 0 \<longrightarrow> \<not> pext p t f)\<rangle>) \<star>
        (\<Squnion>g v. lv_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. rs_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. ts_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. q_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>gc cv g1 tv' g2 fv'. c_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cv \<star> t1_ref \<mapsto>\<langle>\<top>\<rangle> g1\<down>tv' \<star>
           f1_ref \<mapsto>\<langle>\<top>\<rangle> g2\<down>fv' \<star> \<langle>ext_ok p t f tv' fv' \<and> (cv \<noteq> 0 \<longrightarrow> \<not> pext p t f)\<rangle>) \<star>
        (\<Squnion>g v. lv_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. rs_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. ts_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. q_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: false_code_spec watch_visit_spec units_at_spec
        contracts add: trivial_contract_def watch_visit_contract_def units_at_contract_def)
    apply (all \<open>solves \<open>(rule ext_ok_trans; assumption?), simp_all\<close> | solves \<open>drule ext_ok_len(1), simp\<close> |
        solves \<open>drule ext_ok_len(2), simp\<close> | solves \<open>erule idx_lt_len; simp add: sizes_ok_def\<close> |
        solves \<open>meson ext_ok_none\<close>\<close>)
    done
  done

subsection \<open>Watching new clauses\<close>

lemma top_level_spec:
  shows \<open>\<Gamma>; top_level c lv k \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: top_level_def contract: trivial_contract_def)
  apply crush_base
  subgoal for x_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star>
          \<langle>v = word64_of_nat (length (Clause_lits c)) \<or> unat v < length (Clause_lits c)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def simp add: unat_of_nat_eq word_less_nat_alt)
    apply (auto intro: unat_idx_lt(1))
    done
  done

definition refs3_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>refs3_contract head nxt wl \<equiv>
     make_function_contract
       (can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v))
       (\<lambda>_. can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v))\<close>

definition refs2_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort) function_contract\<close> where
  \<open>refs2_contract head nxt \<equiv>
     make_function_contract
       (can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v))
       (\<lambda>_. can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v))\<close>

definition ref1_contract :: \<open>('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>ref1_contract v \<equiv>
     make_function_contract (can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs))
       (\<lambda>_. can_alloc_reference \<star> (\<Squnion>g vs. v \<mapsto>\<langle>\<top>\<rangle> g\<down>vs))\<close>

lemma link_spec:
  shows \<open>\<Gamma>; link head nxt code w \<Turnstile>\<^sub>F refs2_contract head nxt\<close>
  apply (crush_boot f: link_def contract: refs2_contract_def)
  apply (crush_base specs add: get_or_spec set_at_any_spec contracts add: get_or_contract_def set_at_any_contract_def
      inline: cap_def)
  done

lemma watch_clause_spec:
  shows \<open>\<Gamma>; watch_clause c lv head nxt wl \<Turnstile>\<^sub>F refs3_contract head nxt wl\<close>
  apply (crush_boot f: watch_clause_def contract: refs3_contract_def)
  apply (crush_base specs add: top_level_spec link_spec lit_code_spec sat_add_ok_spec
      contracts add: trivial_contract_def refs2_contract_def sat_add_ok_contract_def
      inline: vec_push_def cap_def simp add: word_less_nat_alt)
  apply (auto dest: unat_lt_len)
  done

lemma watch_new_spec:
  shows \<open>\<Gamma>; watch_new p l lv head nxt wl \<Turnstile>\<^sub>F refs3_contract head nxt wl\<close>
  apply (crush_boot f: watch_new_def contract: refs3_contract_def)
  apply (crush_base specs add: sat_add_ok_spec contracts add: sat_add_ok_contract_def)
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. head \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
        (\<Squnion>g v. nxt \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. wl \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: watch_clause_spec contracts add: refs3_contract_def
      simp add: word_less_nat_alt not_less)
  apply (auto simp add: word_le_nat_alt dest: unat_lt_len)
  done

subsection \<open>The decision order\<close>

lemma bump_spec:
  shows \<open>\<Gamma>; bump c act m \<Turnstile>\<^sub>F ref1_contract act\<close>
  apply (crush_boot f: bump_def contract: ref1_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g vs. act \<mapsto>\<langle>\<top>\<rangle> g\<down>vs)\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: set_at_any_spec contracts add: set_at_any_contract_def simp add: unat_of_nat_eq)
  apply (auto intro: unat_idx_lt(1))
  done

lemma bump_last_spec:
  shows \<open>\<Gamma>; bump_last l act \<Turnstile>\<^sub>F ref1_contract act\<close>
  apply (crush_boot f: bump_last_def contract: ref1_contract_def)
  apply (crush_base specs add: bump_spec contracts add: ref1_contract_def simp add: word_less_nat_alt)
  apply (auto intro: last_idx_lt last_idx_one)
  done

definition pick_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>pick_contract t f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length f = length t \<and> length t < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat r \<le> length t \<and> (unat r < length t \<longrightarrow> \<not> t ! unat r \<and> \<not> f ! unat r) \<and>
         (unat r = length t \<longrightarrow> (\<forall>j < length t. t ! j \<or> f ! j))\<rangle> in
     make_function_contract pre post\<close>

lemma pick_spec:
  shows \<open>\<Gamma>; pick t f act \<Turnstile>\<^sub>F pick_contract t f\<close>
  apply (crush_boot f: pick_def contract: pick_contract_def)
  apply crush_base
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g k. k_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>k \<star>
         \<langle>unat k \<le> length t \<and> (unat k < length t \<longrightarrow> \<not> t ! unat k \<and> \<not> f ! unat k) \<and>
          (unat k = length t \<longrightarrow> (\<forall>j < i. t ! j \<or> f ! j))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def simp add: unat_of_nat_eq less_Suc_eq)
    apply (auto simp add: word_less_nat_alt unat_of_nat_eq)
    apply (metis word_unat.Rep_inverse)+
    done
  done

lemma new_atoms_spec:
  shows \<open>\<Gamma>; new_atoms t f qt qf \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: new_atoms_def contract: trivial_contract_def)
  apply crush_base
  subgoal for q_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. q_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq word_less_nat_alt)
    apply (auto dest: unat_lt_len intro: unat_idx_lt(1))
    done
  done

subsection \<open>The symbol index\<close>

lemma sym_index_spec:
  shows \<open>\<Gamma>; sym_index p \<Turnstile>\<^sub>F trivial_contract\<close>
  apply (crush_boot f: sym_index_def contract: trivial_contract_def)
  apply crush_base
  subgoal for m_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. m_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: sat_add_ok_spec contracts add: sat_add_ok_contract_def simp add: unat_of_nat_eq)
    subgoal by (auto intro: unat_idx_lt(1))
    subgoal by (auto intro: unat_idx_lt(1))
    subgoal for g r x start_ref
      apply (ucincl_discharge\<open>
        rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. m_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
          (\<Squnion>g v. start_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
          and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
      apply (crush_base specs add: sat_add_ok_spec get_or_spec set_at_any_spec
          contracts add: sat_add_ok_contract_def get_or_contract_def set_at_any_contract_def simp add: unat_of_nat_eq)
      subgoal by (auto intro: unat_idx_lt(1))
      subgoal
        apply (ucincl_discharge\<open>
          rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. m_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
            (\<Squnion>g v. start_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
            and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
            and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_raw_for_loop_framedI'\<close>)
        apply (crush_base specs add: sat_add_ok_spec get_or_spec set_at_any_spec
            contracts add: sat_add_ok_contract_def get_or_contract_def set_at_any_contract_def simp add: unat_of_nat_eq)
        subgoal for gb gab xaa rb pos_ref perm_ref
          apply (ucincl_discharge\<open>
            rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g v. m_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
              (\<Squnion>g v. start_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star> (\<Squnion>g v. pos_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<star>
              (\<Squnion>g v. perm_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
              and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
              and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
              and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_raw_for_loop_framedI'\<close>)
          apply (crush_base specs add: sat_add_ok_spec get_or_spec set_at_any_spec
              contracts add: sat_add_ok_contract_def get_or_contract_def set_at_any_contract_def
              simp add: unat_of_nat_eq)
          apply (auto intro: unat_idx_lt(1))
          done
        done
      done
    done
  done

end

end
