theory QFUF_Propagate
  imports QFUF_Explain
begin

section \<open>Theory propagation\<close>

text \<open>After a closure without conflict, the search sets the unset atoms that the closure decides:
  an atom whose two sides it joins becomes true, and an atom whose two sides lie in the two classes
  of the sides of an atom set false becomes false. Every interpretation that extends the partial
  assignment and makes the problem true agrees with these values (\<open>pext_implied\<close>).\<close>

subsection \<open>Pure facts\<close>

text \<open>The two sides of atom \<open>j\<close> lie in the classes of \<open>rs\<close> of the two sides of an atom set false.\<close>
definition sep_by :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sep_by p f rs j \<equiv> \<exists>b < length (Problem_atoms p). f ! b \<and>
     (rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_lhs (Problem_atoms p ! b)) \<and>
      rs ! unat (Atom_rhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! b)) \<or>
      rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! b)) \<and>
      rs ! unat (Atom_rhs (Problem_atoms p ! j)) = rs ! unat (Atom_lhs (Problem_atoms p ! b)))\<close>

text \<open>\<open>t1\<close>, \<open>f1\<close> extend \<open>t\<close>, \<open>f\<close> by unset atoms that the closure \<open>rs\<close> of the atoms set true
  decides.\<close>
definition implied_ok :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>implied_ok p t f rs t1 f1 \<equiv>
     rep_sound p (asserted p t (length (Problem_atoms p))) rs \<and> length rs = length (Problem_terms p) \<and>
     length t1 = length t \<and> length f1 = length f \<and>
     (\<forall>j < length t. (t ! j \<longrightarrow> t1 ! j) \<and> (f ! j \<longrightarrow> f1 ! j) \<and>
        (t1 ! j \<and> \<not> t ! j \<longrightarrow> \<not> f ! j \<and>
           rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! j))) \<and>
        (f1 ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j \<and> sep_by p f rs j))\<close>

lemma rep_sound_val:
  assumes wf: \<open>wf_problem p\<close> and rs: \<open>rep_sound p (asserted p t (length (Problem_atoms p))) rs\<close>
      and n: \<open>length rs = length (Problem_terms p)\<close>
      and I: \<open>\<forall>j < length (Problem_atoms p). t ! j \<longrightarrow> atom_vals I p ! j\<close>
      and ij: \<open>i < length (Problem_terms p)\<close> \<open>i' < length (Problem_terms p)\<close> \<open>rs ! i = rs ! i'\<close>
  shows \<open>term_val I (Problem_terms p) i = term_val I (Problem_terms p) i'\<close>
proof -
  have \<open>\<forall>(a, b) \<in> asserted p t (length (Problem_atoms p)).
          term_val I (Problem_terms p) a = term_val I (Problem_terms p) b\<close>
    using I unfolding asserted_def atom_vals_def atom_true_def by auto
  moreover have \<open>(i, i') \<in> cc p (asserted p t (length (Problem_atoms p)))\<close>
    using rs n ij unfolding rep_sound_def by simp
  ultimately show ?thesis using cc_sound[OF wf] by blast
qed

lemma pext_implied:
  assumes wf: \<open>wf_problem p\<close> and len: \<open>length t = length (Problem_atoms p)\<close>
      and ok: \<open>implied_ok p t f rs t1 f1\<close> and e: \<open>pext p t f\<close>
  shows \<open>pext p t1 f1\<close>
proof -
  obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where I: \<open>problem_true I p\<close>
    \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    using e unfolding pext_def by blast
  have rs: \<open>rep_sound p (asserted p t (length (Problem_atoms p))) rs\<close> \<open>length rs = length (Problem_terms p)\<close>
    using ok unfolding implied_ok_def by simp_all
  let ?v = \<open>term_val I (Problem_terms p)\<close>
  let ?L = \<open>\<lambda>j. unat (Atom_lhs (Problem_atoms p ! j))\<close> and ?R = \<open>\<lambda>j. unat (Atom_rhs (Problem_atoms p ! j))\<close>
  have okT: \<open>\<forall>j < length t. t1 ! j \<and> \<not> t ! j \<longrightarrow> rs ! ?L j = rs ! ?R j\<close>
   and okF: \<open>\<forall>j < length t. f1 ! j \<and> \<not> f ! j \<longrightarrow> sep_by p f rs j\<close>
    using ok unfolding implied_ok_def by blast+
  have eq: \<open>?v i = ?v i'\<close> if \<open>i < length (Problem_terms p)\<close> \<open>i' < length (Problem_terms p)\<close> \<open>rs ! i = rs ! i'\<close> for i i'
    using rep_sound_val[OF wf rs] I(2) that by blast
  have av: \<open>atom_vals I p ! j = (?v (?L j) = ?v (?R j))\<close> if \<open>j < length (Problem_atoms p)\<close> for j
    using that by (simp add: atom_vals_def atom_true_def)
  have T: \<open>atom_vals I p ! j\<close> if j: \<open>j < length (Problem_atoms p)\<close> \<open>t1 ! j\<close> for j
  proof (cases \<open>t ! j\<close>)
    case False
    then have \<open>rs ! ?L j = rs ! ?R j\<close> using okT j len by simp
    then show ?thesis using eq wf_atom[OF wf j(1)] av[OF j(1)] by simp
  qed (use I(2) j in blast)
  have F: \<open>\<not> atom_vals I p ! j\<close> if j: \<open>j < length (Problem_atoms p)\<close> \<open>f1 ! j\<close> for j
  proof (cases \<open>f ! j\<close>)
    case False
    then have \<open>sep_by p f rs j\<close> using okF j len by simp
    then obtain b where b: \<open>b < length (Problem_atoms p)\<close> \<open>f ! b\<close>
      \<open>rs ! ?L j = rs ! ?L b \<and> rs ! ?R j = rs ! ?R b \<or> rs ! ?L j = rs ! ?R b \<and> rs ! ?R j = rs ! ?L b\<close>
      unfolding sep_by_def by blast
    have \<open>?v (?L b) \<noteq> ?v (?R b)\<close> using I(2) b(1,2) av[OF b(1)] by blast
    moreover have \<open>?L j < length (Problem_terms p)\<close> \<open>?R j < length (Problem_terms p)\<close>
      \<open>?L b < length (Problem_terms p)\<close> \<open>?R b < length (Problem_terms p)\<close>
      using wf_atom[OF wf j(1)] wf_atom[OF wf b(1)] by simp_all
    ultimately have \<open>?v (?L j) \<noteq> ?v (?R j)\<close> using b(3) eq by metis
    then show ?thesis using av[OF j(1)] by simp
  qed (use I(2) j in blast)
  show ?thesis
    unfolding pext_def using I(1) T F by blast
qed

lemma implied_fuel:
  assumes ok: \<open>implied_ok p t f rs t1 f1\<close> and len: \<open>length f = length t\<close>
      and d: \<open>t1 \<noteq> t \<or> f1 \<noteq> f\<close>
      and k: \<open>unset_count t f < Suc k\<close>
  shows \<open>unset_count t1 f1 < k\<close>
proof -
  let ?S = \<open>{j. j < length t \<and> \<not> t ! j \<and> \<not> f ! j}\<close> and ?S1 = \<open>{j. j < length t1 \<and> \<not> t1 ! j \<and> \<not> f1 ! j}\<close>
  have l1: \<open>length t1 = length t\<close> using ok unfolding implied_ok_def by simp
  have sub: \<open>?S1 \<subseteq> ?S\<close> using ok l1 unfolding implied_ok_def by auto
  have l2: \<open>length f1 = length f\<close> using ok unfolding implied_ok_def by simp
  have \<open>\<exists>i < length t. t ! i \<noteq> t1 ! i \<or> f ! i \<noteq> f1 ! i\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>i < length t. t ! i \<noteq> t1 ! i \<or> f ! i \<noteq> f1 ! i)\<close>
    then have \<open>t1 = t\<close> \<open>f1 = f\<close> using len l1 l2 by (auto intro!: nth_equalityI)
    then show False using d by simp
  qed
  then obtain i where i: \<open>i \<in> ?S\<close> \<open>i \<notin> ?S1\<close>
    using ok len l1 unfolding implied_ok_def by (metis (mono_tags, lifting) mem_Collect_eq)
  have \<open>card ?S1 < card ?S\<close>
    using sub i by (intro psubset_card_mono) auto
  then show ?thesis using k unfolding unset_count_def by simp
qed

lemma sep_byI:
  assumes \<open>\<forall>i < length us. \<exists>b < length (Problem_atoms p). f ! b \<and>
             us ! i = rs ! unat (Atom_lhs (Problem_atoms p ! b)) \<and> vs ! i = rs ! unat (Atom_rhs (Problem_atoms p ! b))\<close>
      and \<open>\<exists>i < length us. us ! i = rs ! unat (Atom_lhs (Problem_atoms p ! j)) \<and> vs ! i = rs ! unat (Atom_rhs (Problem_atoms p ! j)) \<or>
             us ! i = rs ! unat (Atom_rhs (Problem_atoms p ! j)) \<and> vs ! i = rs ! unat (Atom_lhs (Problem_atoms p ! j))\<close>
  shows \<open>sep_by p f rs j\<close>
  using assms unfolding sep_by_def by metis

lemma implied_okI:
  assumes \<open>cc_inv p (asserted p t (length (Problem_atoms p))) rs\<close>
      and \<open>length t = length (Problem_atoms p)\<close> \<open>length f = length (Problem_atoms p)\<close>
      and \<open>length t1 = length (Problem_atoms p)\<close>
      and \<open>\<forall>j < length (Problem_atoms p). t1 ! j = (t ! j \<or>
             \<not> f ! j \<and> rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! j)))\<close>
      and \<open>length f1 = length (Problem_atoms p)\<close>
      and \<open>\<forall>j < length (Problem_atoms p). (f ! j \<longrightarrow> f1 ! j) \<and> (f1 ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j \<and> sep_by p f rs j)\<close>
  shows \<open>implied_ok p t f rs t1 f1\<close>
  using assms unfolding implied_ok_def cc_inv_def rep_ok_def by auto

context QFUF_ctx
begin

subsection \<open>Contracts\<close>

definition joined_unset_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow>
      ('s, bool list, 'abort) function_contract\<close> where
  \<open>joined_unset_contract p t f rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p) \<and>
         length t = length (Problem_atoms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>length r = length (Problem_atoms p) \<and> (\<forall>j < length (Problem_atoms p). r ! j = (t ! j \<or>
           \<not> f ! j \<and> rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! j))))\<rangle> in
     make_function_contract pre post\<close>

lemma joined_unset_spec:
  shows \<open>\<Gamma>; joined_unset p t f rs \<Turnstile>\<^sub>F joined_unset_contract p t f rs\<close>
  apply (crush_boot f: joined_unset_def contract: joined_unset_contract_def)
  apply (crush_base simp add: sizes_ok_def)
  subgoal for t1_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' xs. t1_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>xs \<star>
                 \<langle>length xs = length (Problem_atoms p) \<and> (\<forall>j < length (Problem_atoms p). xs ! j = (t ! j \<or>
                    j < i \<and> \<not> f ! j \<and> rs ! unat (Atom_lhs (Problem_atoms p ! j)) = rs ! unat (Atom_rhs (Problem_atoms p ! j))))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq less_Suc_eq nth_list_update sizes_ok_def)
    apply (auto simp add: less_Suc_eq)
    apply (metis wf_atom)+
    done
  done

definition false_pairs_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow>
      ('s, 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  \<open>false_pairs_contract p f rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>length (fst (snd r)) = length (fst r) \<and> length (fst r) \<le> length (Problem_atoms p) \<and>
         (\<forall>i < length (fst r). \<exists>b < length (Problem_atoms p). f ! b \<and>
            fst r ! i = rs ! unat (Atom_lhs (Problem_atoms p ! b)) \<and>
            fst (snd r) ! i = rs ! unat (Atom_rhs (Problem_atoms p ! b)))\<rangle> in
     make_function_contract pre post\<close>

lemma false_pairs_spec:
  shows \<open>\<Gamma>; false_pairs p f rs \<Turnstile>\<^sub>F false_pairs_contract p f rs\<close>
  apply (crush_boot f: false_pairs_def contract: false_pairs_contract_def)
  apply (crush_base inline: vec_push_def simp add: sizes_ok_def)
  subgoal for us_ref vs_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' us. us_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>us \<star>
                 (\<Squnion>g'' vs. vs_ref \<mapsto>\<langle>\<top>\<rangle> g''\<down>vs \<star>
                 \<langle>length vs = length us \<and> length us \<le> i \<and> (\<forall>k < length us. \<exists>b < length (Problem_atoms p). f ! b \<and>
                    us ! k = rs ! unat (Atom_lhs (Problem_atoms p ! b)) \<and>
                    vs ! k = rs ! unat (Atom_rhs (Problem_atoms p ! b)))\<rangle>))\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq nth_append sizes_ok_def)
    apply blast
    apply (metis wf_atom)+
    done
  done

definition has_pair_contract :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
      ('s, bool, 'abort) function_contract\<close> where
  \<open>has_pair_contract us vs x y \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length us \<le> length vs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r \<longrightarrow> (\<exists>i < length us. us ! i = x \<and> vs ! i = y \<or> us ! i = y \<and> vs ! i = x)\<rangle> in
     make_function_contract pre post\<close>

lemma has_pair_spec:
  shows \<open>\<Gamma>; has_pair us vs x y \<Turnstile>\<^sub>F has_pair_contract us vs x y\<close>
  apply (crush_boot f: has_pair_def contract: has_pair_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
         \<langle>r \<longrightarrow> (\<exists>i < length us. us ! i = x \<and> vs ! i = y \<or> us ! i = y \<and> vs ! i = x)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto dest: unat_idx_lt(1) intro: order_less_le_trans)
  done

definition separated_unset_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow>
      ('s, bool list, 'abort) function_contract\<close> where
  \<open>separated_unset_contract p t f rs \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length rs = length (Problem_terms p) \<and>
         length t = length (Problem_atoms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>length r = length (Problem_atoms p) \<and> (\<forall>j < length (Problem_atoms p).
           (f ! j \<longrightarrow> r ! j) \<and> (r ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j \<and> sep_by p f rs j))\<rangle> in
     make_function_contract pre post\<close>

lemma separated_unset_spec:
  shows \<open>\<Gamma>; separated_unset p t f rs \<Turnstile>\<^sub>F separated_unset_contract p t f rs\<close>
  apply (crush_boot f: separated_unset_def contract: separated_unset_contract_def)
  apply (crush_base specs add: false_pairs_spec contracts add: false_pairs_contract_def simp add: sizes_ok_def)
  subgoal for us vs f1_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' xs. f1_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>xs \<star>
                 \<langle>length xs = length (Problem_atoms p) \<and> (\<forall>j < length (Problem_atoms p).
                    (f ! j \<longrightarrow> xs ! j) \<and> (xs ! j \<and> \<not> f ! j \<longrightarrow> \<not> t ! j \<and> sep_by p f rs j))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: has_pair_spec contracts add: has_pair_contract_def
        simp add: unat_of_nat_eq nth_list_update sizes_ok_def)
    subgoal for i g' xs x ia j
      by (cases \<open>i = j\<close>) (auto intro!: sep_byI[where us=us and vs=vs])
    subgoal for i g' xs x ia j by (cases \<open>i = j\<close>) auto
    subgoal for i g' xs x ia j
      by (cases \<open>i = j\<close>) (auto intro!: sep_byI[where us=us and vs=vs])
    subgoal for i g' xs x ia j by (cases \<open>i = j\<close>) auto
    apply (metis wf_atom)+
    done
  done

definition differs_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>differs_contract t t1 \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length t1 = length t \<and> length t < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (t1 \<noteq> t)\<rangle> in
     make_function_contract pre post\<close>

lemma differs_spec:
  shows \<open>\<Gamma>; differs t t1 \<Turnstile>\<^sub>F differs_contract t t1\<close>
  apply (crush_boot f: differs_def contract: differs_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j < i. t ! j = t1 ! j\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r \<and> (\<exists>i < length t. t ! i \<noteq> t1 ! i)\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq)
  apply (auto intro: nth_equalityI)
  done

text \<open>The contract of \<^const>\<open>false_joined\<close> that also keeps the invariant of \<open>rep\<close>.\<close>
definition false_joined_keep_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, 64 word, 'abort) function_contract\<close> where
  \<open>false_joined_keep_contract p t f rep \<equiv>
     let pre = can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms p))) rs\<rangle>) \<star>
        \<langle>wf_problem p \<and> length t = length (Problem_atoms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms p))) rs\<rangle>) \<star>
        \<langle>conflict_result p t f r\<rangle> in
     make_function_contract pre post\<close>

lemma false_joined_keep_spec:
  shows \<open>\<Gamma>; false_joined p f rep \<Turnstile>\<^sub>F false_joined_keep_contract p t f rep\<close>
  apply (crush_boot f: false_joined_def contract: false_joined_keep_contract_def)
  apply (crush_base specs add: first_joined_spec contracts add: first_joined_contract_def)
  apply (auto simp add: conflict_result_def cc_inv_def sizes_ok_def intro: cc_inv_joined)
  apply (simp add: rep_ok_def)
  done

definition implied_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> ('addr, 'gv, 64 word list) Global_Store.ref \<Rightarrow>
      ('s, bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  \<open>implied_contract p t f rep \<equiv>
     let pre = can_alloc_reference \<star>
        (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs \<star> \<langle>cc_inv p (asserted p t (length (Problem_atoms p))) rs\<rangle>) \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> (\<Squnion>g rs. rep \<mapsto>\<langle>\<top>\<rangle> g\<down>rs) \<star>
        \<langle>\<exists>rs. implied_ok p t f rs (fst r) (fst (snd r))\<rangle> in
     make_function_contract pre post\<close>

lemma implied_spec:
  shows \<open>\<Gamma>; implied p t f rep \<Turnstile>\<^sub>F implied_contract p t f rep\<close>
  apply (crush_boot f: implied_def contract: implied_contract_def)
  apply (crush_base specs add: joined_unset_spec separated_unset_spec
      contracts add: joined_unset_contract_def separated_unset_contract_def)
  apply (blast intro: implied_okI)
  apply (auto intro: cc_inv_length)
  done

definition cc_propagate_contract :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('s, 64 word \<times> bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  \<open>cc_propagate_contract p t f \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length t = length (Problem_atoms p) \<and> length f = length (Problem_atoms p)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>conflict_result p t f (fst r) \<and> (\<exists>rs. implied_ok p t f rs (fst (snd r)) (fst (snd (snd r))))\<rangle> in
     make_function_contract pre post\<close>

lemma cc_propagate_spec:
  shows \<open>\<Gamma>; cc_propagate p t f \<Turnstile>\<^sub>F cc_propagate_contract p t f\<close>
  apply (crush_boot f: cc_propagate_def contract: cc_propagate_contract_def)
  apply (crush_base specs add: init_rep_spec assert_eqs_spec close_spec false_joined_keep_spec[where t=t]
        implied_spec
      contracts add: init_rep_contract_def assert_eqs_contract_def close_contract_def
        false_joined_keep_contract_def implied_contract_def
      simp add: unat_of_nat_lt63 unat_of_nat_eq)
  apply blast
  apply (auto simp add: sizes_ok_def unat_of_nat_lt63 intro: cc_inv_init64 cc_inv_init cc_inv_length)
  done

end

end
