theory QFUF_Pure
  imports "QFUF_CoreSpec.QFUF_CoreSpec"
begin

section \<open>Pure facts behind the solver\<close>

text \<open>This theory has no uRust: it states and proves the mathematics of congruence closure, the
  model construction and the search, over HOL values that mirror the solver's data.\<close>

subsection \<open>Term values\<close>

lemma term_val_wf:
  assumes \<open>\<forall>x \<in> set (Term_args (ts ! i)). unat x < i\<close>
  shows \<open>term_val I ts i =
           I (unat (Term_fun (ts ! i))) (List.map (\<lambda>x. term_val I ts (unat x)) (Term_args (ts ! i)))\<close>
  using assms by (subst term_val.simps) (auto intro!: arg_cong[where f=\<open>I _\<close>])

lemma wf_problemD:
  assumes \<open>wf_problem p\<close>
  shows wf_args: \<open>\<And>i x. i < length (Problem_terms p) \<Longrightarrow> x \<in> set (Term_args (Problem_terms p ! i)) \<Longrightarrow>
                        unat x < i\<close>
    and wf_args_nth: \<open>\<And>i k. i < length (Problem_terms p) \<Longrightarrow> k < length (Term_args (Problem_terms p ! i)) \<Longrightarrow>
                        unat (Term_args (Problem_terms p ! i) ! k) < i\<close>
    and wf_atom: \<open>\<And>k. k < length (Problem_atoms p) \<Longrightarrow>
                    unat (Atom_lhs (Problem_atoms p ! k)) < length (Problem_terms p) \<and>
                    unat (Atom_rhs (Problem_atoms p ! k)) < length (Problem_terms p)\<close>
    and wf_lit: \<open>\<And>c l. c \<in> set (Problem_clauses p) \<Longrightarrow> l \<in> set (Clause_lits c) \<Longrightarrow>
                   unat (Lit_atom l) < length (Problem_atoms p)\<close>
  using assms unfolding wf_problem_def by (auto dest: nth_mem)

subsection \<open>Congruence closure\<close>

text \<open>The congruence closure of a set \<open>E\<close> of pairs of term indices.\<close>
inductive_set cc :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set\<close> for p E where
  base: \<open>(i, j) \<in> E \<Longrightarrow> (i, j) \<in> cc p E\<close>
| refl: \<open>(i, i) \<in> cc p E\<close>
| sym: \<open>(i, j) \<in> cc p E \<Longrightarrow> (j, i) \<in> cc p E\<close>
| trans: \<open>(i, j) \<in> cc p E \<Longrightarrow> (j, k) \<in> cc p E \<Longrightarrow> (i, k) \<in> cc p E\<close>
| cong: \<open>i < length (Problem_terms p) \<Longrightarrow> j < length (Problem_terms p) \<Longrightarrow>
         Term_fun (Problem_terms p ! i) = Term_fun (Problem_terms p ! j) \<Longrightarrow>
         length (Term_args (Problem_terms p ! i)) = length (Term_args (Problem_terms p ! j)) \<Longrightarrow>
         (\<forall>k < length (Term_args (Problem_terms p ! i)).
            (unat (Term_args (Problem_terms p ! i) ! k), unat (Term_args (Problem_terms p ! j) ! k)) \<in> cc p E) \<Longrightarrow>
         (i, j) \<in> cc p E\<close>

lemma cc_mono:
  assumes \<open>(i, j) \<in> cc p E\<close> \<open>E \<subseteq> E'\<close>
  shows \<open>(i, j) \<in> cc p E'\<close>
  using assms(1)
proof induction
  case (cong i j)
  then show ?case by (intro cc.cong) auto
qed (use assms(2) in \<open>auto intro: cc.intros\<close>)

text \<open>Every pair in the congruence closure of \<open>E\<close> has equal values under every interpretation
  that gives the pairs of \<open>E\<close> equal values, over any domain.\<close>
lemma cc_sound:
  assumes wf: \<open>wf_problem p\<close>
      and E: \<open>\<forall>(i, j) \<in> E. term_val I (Problem_terms p) i = term_val I (Problem_terms p) j\<close>
      and \<open>(i, j) \<in> cc p E\<close>
  shows \<open>term_val I (Problem_terms p) i = term_val I (Problem_terms p) j\<close>
  using assms(3)
proof induction
  case (base i j)
  then show ?case using E by auto
next
  case (cong i j)
  let ?ts = \<open>Problem_terms p\<close>
  have \<open>List.map (\<lambda>x. term_val I ?ts (unat x)) (Term_args (?ts ! i)) =
        List.map (\<lambda>x. term_val I ?ts (unat x)) (Term_args (?ts ! j))\<close>
    using cong by (auto intro!: nth_equalityI)
  then show ?case
    using cong.hyps(1-3) wf_args[OF wf] by (simp add: term_val_wf)
qed auto

subsection \<open>Partitions as representative lists\<close>

text \<open>\<open>rs ! i\<close> is the representative of term \<open>i\<close>'s class.\<close>

definition congruent_p :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>congruent_p p rs i j \<equiv>
     Term_fun (Problem_terms p ! i) = Term_fun (Problem_terms p ! j) \<and>
     length (Term_args (Problem_terms p ! i)) = length (Term_args (Problem_terms p ! j)) \<and>
     (\<forall>k < length (Term_args (Problem_terms p ! i)).
        rs ! unat (Term_args (Problem_terms p ! i) ! k) = rs ! unat (Term_args (Problem_terms p ! j) ! k))\<close>

text \<open>Every class lies in the congruence closure of \<open>E\<close>.\<close>
definition rep_sound :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>rep_sound p E rs \<equiv> \<forall>i < length rs. \<forall>j < length rs. rs ! i = rs ! j \<longrightarrow> (i, j) \<in> cc p E\<close>

text \<open>Every pair of \<open>E\<close> lies in a class.\<close>
definition rep_has :: \<open>(nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>rep_has E rs \<equiv> \<forall>(i, j) \<in> E. rs ! i = rs ! j\<close>

text \<open>Congruent terms lie in the same class.\<close>
definition closed :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>closed p rs \<equiv> \<forall>i < length rs. \<forall>j < length rs. congruent_p p rs i j \<longrightarrow> rs ! i = rs ! j\<close>

lemma congruent_p_sym:
  \<open>congruent_p p rs i j \<Longrightarrow> congruent_p p rs j i\<close>
  unfolding congruent_p_def by metis

text \<open>Congruence is symmetric, so it suffices to check every pair \<open>(i, j)\<close> with \<open>j < i\<close>.\<close>
lemma closed_lowerI:
  assumes \<open>\<forall>i < length rs. \<forall>j < i. congruent_p p rs i j \<longrightarrow> rs ! i = rs ! j\<close>
  shows \<open>closed p rs\<close>
  unfolding closed_def
proof (intro allI impI)
  fix i j assume ij: \<open>i < length rs\<close> \<open>j < length rs\<close> \<open>congruent_p p rs i j\<close>
  consider \<open>j < i\<close> | \<open>i = j\<close> | \<open>i < j\<close> by linarith
  then show \<open>rs ! i = rs ! j\<close>
    using assms ij congruent_p_sym by cases metis+
qed

text \<open>All invariants of the representative list during the closure, for the asserted pairs \<open>E\<close>.\<close>
definition rep_ok :: \<open>Problem \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 64 word list \<Rightarrow> bool\<close> where
  \<open>rep_ok p E rs \<equiv> length rs = length (Problem_terms p) \<and> rep_sound p E rs \<and> rep_has E rs\<close>

definition merge_list :: \<open>64 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 64 word list\<close> where
  \<open>merge_list rs a b \<equiv> List.map (\<lambda>x. if x = rs ! a then rs ! b else x) rs\<close>

lemma length_merge_list [simp]:
  \<open>length (merge_list rs a b) = length rs\<close>
  by (simp add: merge_list_def)

lemma nth_merge_list:
  \<open>i < length rs \<Longrightarrow> merge_list rs a b ! i = (if rs ! i = rs ! a then rs ! b else rs ! i)\<close>
  by (simp add: merge_list_def)

lemma merge_list_keeps:
  \<open>i < length rs \<Longrightarrow> j < length rs \<Longrightarrow> rs ! i = rs ! j \<Longrightarrow> merge_list rs a b ! i = merge_list rs a b ! j\<close>
  by (simp add: nth_merge_list)

lemma merge_list_joins:
  \<open>a < length rs \<Longrightarrow> b < length rs \<Longrightarrow> merge_list rs a b ! a = merge_list rs a b ! b\<close>
  by (simp add: nth_merge_list)

lemma rep_has_merge:
  \<open>rep_has E rs \<Longrightarrow> \<forall>(i, j) \<in> E. i < length rs \<and> j < length rs \<Longrightarrow> rep_has E (merge_list rs a b)\<close>
  unfolding rep_has_def using merge_list_keeps by fast

lemma rep_sound_merge:
  assumes \<open>rep_sound p E rs\<close> \<open>a < length rs\<close> \<open>b < length rs\<close> \<open>(a, b) \<in> cc p E\<close>
  shows \<open>rep_sound p E (merge_list rs a b)\<close>
  unfolding rep_sound_def
proof (intro allI impI)
  fix i j
  assume ij: \<open>i < length (merge_list rs a b)\<close> \<open>j < length (merge_list rs a b)\<close>
     and eq: \<open>merge_list rs a b ! i = merge_list rs a b ! j\<close>
  have s: \<open>\<And>i j. i < length rs \<Longrightarrow> j < length rs \<Longrightarrow> rs ! i = rs ! j \<Longrightarrow> (i, j) \<in> cc p E\<close>
    using assms(1) unfolding rep_sound_def by blast
  have ia: \<open>(i, a) \<in> cc p E\<close> if \<open>rs ! i = rs ! a\<close> using s ij assms(2) that by simp
  have ja: \<open>(j, a) \<in> cc p E\<close> if \<open>rs ! j = rs ! a\<close> using s ij assms(2) that by simp
  have ib: \<open>(i, b) \<in> cc p E\<close> if \<open>rs ! i = rs ! b\<close> using s ij assms(3) that by simp
  have jb: \<open>(j, b) \<in> cc p E\<close> if \<open>rs ! j = rs ! b\<close> using s ij assms(3) that by simp
  have ab: \<open>(a, b) \<in> cc p E\<close> \<open>(b, a) \<in> cc p E\<close> using assms(4) by (auto intro: cc.sym)
  show \<open>(i, j) \<in> cc p E\<close>
    using eq ij
    apply (simp add: nth_merge_list split: if_splits)
    using ia ja ib jb ab s cc.sym cc.trans by metis+
qed

lemma card_set_merge_list_less:
  assumes \<open>a < length rs\<close> \<open>b < length rs\<close> \<open>rs ! a \<noteq> rs ! b\<close>
  shows \<open>card (set (merge_list rs a b)) < card (set rs)\<close>
proof -
  have \<open>set (merge_list rs a b) = set rs - {rs ! a}\<close>
    using assms unfolding merge_list_def by (auto simp add: image_iff in_set_conv_nth)
  moreover have \<open>rs ! a \<in> set rs\<close> using assms by simp
  ultimately show ?thesis by (metis card_Diff1_less finite_set)
qed

lemma congruent_cc:
  assumes \<open>wf_problem p\<close> \<open>rep_ok p E rs\<close> \<open>i < length rs\<close> \<open>j < length rs\<close> \<open>congruent_p p rs i j\<close>
  shows \<open>(i, j) \<in> cc p E\<close>
proof -
  have n: \<open>length rs = length (Problem_terms p)\<close> using assms(2) by (simp add: rep_ok_def)
  show ?thesis
  proof (rule cc.cong)
    show \<open>\<forall>k < length (Term_args (Problem_terms p ! i)).
            (unat (Term_args (Problem_terms p ! i) ! k), unat (Term_args (Problem_terms p ! j) ! k)) \<in> cc p E\<close>
    proof (intro allI impI)
      fix k assume k: \<open>k < length (Term_args (Problem_terms p ! i))\<close>
      then have \<open>k < length (Term_args (Problem_terms p ! j))\<close> using assms(5) by (simp add: congruent_p_def)
      then have \<open>unat (Term_args (Problem_terms p ! i) ! k) < length rs\<close>
                \<open>unat (Term_args (Problem_terms p ! j) ! k) < length rs\<close>
        using k wf_args_nth[OF assms(1)] assms(3,4) n by (metis order.strict_trans)+
      then show \<open>(unat (Term_args (Problem_terms p ! i) ! k), unat (Term_args (Problem_terms p ! j) ! k)) \<in> cc p E\<close>
        using assms(2,5) k unfolding rep_ok_def rep_sound_def congruent_p_def by blast
    qed
  qed (use assms n in \<open>auto simp add: congruent_p_def\<close>)
qed

lemma rep_ok_merge:
  assumes \<open>rep_ok p E rs\<close> \<open>a < length rs\<close> \<open>b < length rs\<close> \<open>(a, b) \<in> cc p E\<close>
      and \<open>\<forall>(i, j) \<in> E. i < length rs \<and> j < length rs\<close>
  shows \<open>rep_ok p E (merge_list rs a b)\<close>
  using assms rep_sound_merge rep_has_merge unfolding rep_ok_def by simp

lemma rep_ok_merge_congruent:
  assumes \<open>wf_problem p\<close> \<open>rep_ok p E rs\<close> \<open>i < length rs\<close> \<open>j < length rs\<close> \<open>congruent_p p rs i j\<close>
      and \<open>\<forall>(i, j) \<in> E. i < length rs \<and> j < length rs\<close>
  shows \<open>rep_ok p E (merge_list rs i j)\<close>
  using assms congruent_cc rep_ok_merge by blast

text \<open>The initial partition: every term alone.\<close>
lemma rep_ok_init:
  assumes \<open>length (Problem_terms p) < 2^64\<close>
  shows \<open>rep_ok p {} (List.map word_of_nat [0..<length (Problem_terms p)])\<close>
proof -
  have \<open>(word_of_nat i :: 64 word) = word_of_nat j \<Longrightarrow> i < length (Problem_terms p) \<Longrightarrow>
        j < length (Problem_terms p) \<Longrightarrow> i = j\<close> for i j
  proof -
    assume \<open>(word_of_nat i :: 64 word) = word_of_nat j\<close> \<open>i < length (Problem_terms p)\<close>
      \<open>j < length (Problem_terms p)\<close>
    moreover have \<open>unat (word_of_nat k :: 64 word) = k\<close> if \<open>k < length (Problem_terms p)\<close> for k
      using that assms by (simp add: unat_of_nat_eq)
    ultimately show \<open>i = j\<close> by metis
  qed
  then show ?thesis
    unfolding rep_ok_def rep_sound_def rep_has_def by (auto intro: cc.refl)
qed

subsection \<open>The model of a closed partition\<close>

definition model_of :: \<open>Problem \<Rightarrow> 64 word list \<Rightarrow> Model\<close> where
  \<open>model_of p rs \<equiv> make_Model (List.map (\<lambda>i.
     make_Entry (Term_fun (Problem_terms p ! i))
                (List.map (\<lambda>x. rs ! unat x) (Term_args (Problem_terms p ! i))) (rs ! i))
     [0..<length (Problem_terms p)])\<close>

lemma unat_eq_iff_eq:
  \<open>unat x = unat (y :: 'a::len word) \<longleftrightarrow> x = y\<close>
  by (metis word_unat_eq_iff)

lemma map_unat_inj:
  \<open>List.map unat xs = List.map unat (ys :: 'a::len word list) \<longleftrightarrow> xs = ys\<close>
proof -
  have \<open>inj (unat :: 'a word \<Rightarrow> nat)\<close> by (rule injI) (simp add: unat_eq_iff_eq)
  then show ?thesis by (rule inj_map_eq_map)
qed

lemma model_of_term_val:
  assumes wf: \<open>wf_problem p\<close> and ok: \<open>rep_ok p E rs\<close> and cl: \<open>closed p rs\<close>
      and i: \<open>i < length (Problem_terms p)\<close>
  shows \<open>term_val (model_interp (model_of p rs)) (Problem_terms p) i = unat (rs ! i)\<close>
  using i
proof (induction i rule: less_induct)
  case (less i)
  let ?ts = \<open>Problem_terms p\<close> and ?M = \<open>model_interp (model_of p rs)\<close>
  let ?es = \<open>Model_entries (model_of p rs)\<close>
  let ?vs = \<open>List.map (\<lambda>x. unat (rs ! unat x)) (Term_args (?ts ! i))\<close>
  let ?P = \<open>\<lambda>e. unat (Entry_fun e) = unat (Term_fun (?ts ! i)) \<and> List.map unat (Entry_args e) = ?vs\<close>
  have n: \<open>length rs = length ?ts\<close> using ok by (simp add: rep_ok_def)
  have es: \<open>?es = List.map (\<lambda>i. make_Entry (Term_fun (?ts ! i))
                (List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! i))) (rs ! i)) [0..<length ?ts]\<close>
    by (simp add: model_of_def)
  have args: \<open>List.map (\<lambda>x. term_val ?M ?ts (unat x)) (Term_args (?ts ! i)) = ?vs\<close>
    using less.IH less.prems wf_args[OF wf] by (auto intro!: List.map_cong)
  have \<open>?P (?es ! i)\<close> using less.prems by (simp add: es comp_def)
  moreover have \<open>i < length ?es\<close> using less.prems by (simp add: es)
  ultimately have \<open>\<exists>x \<in> set ?es. ?P x\<close> by (meson nth_mem)
  then have \<open>List.find ?P ?es \<noteq> None\<close>
    unfolding find_None_iff by blast
  then obtain e where e: \<open>List.find ?P ?es = Some e\<close>
    by (cases \<open>List.find ?P ?es\<close>) auto
  then obtain j where j0: \<open>j < length ?es\<close> \<open>e = ?es ! j\<close> \<open>?P e\<close>
    unfolding find_Some_iff by blast
  have j: \<open>j < length ?ts\<close> \<open>e = ?es ! j\<close> \<open>?P e\<close>
    using j0 by (simp_all add: es)
  have ej: \<open>e = make_Entry (Term_fun (?ts ! j)) (List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! j))) (rs ! j)\<close>
    using j(1,2) by (simp add: es)
  have fj: \<open>Term_fun (?ts ! j) = Term_fun (?ts ! i)\<close>
    using j(3) ej by (simp add: unat_eq_iff_eq)
  have \<open>List.map unat (List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! j))) =
        List.map unat (List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! i)))\<close>
    using j(3) ej by (simp add: comp_def)
  then have aj: \<open>List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! j)) = List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! i))\<close>
    by (simp only: map_unat_inj)
  have lj: \<open>length (Term_args (?ts ! j)) = length (Term_args (?ts ! i))\<close>
    using arg_cong[OF aj, of length] by simp
  have \<open>rs ! unat (Term_args (?ts ! j) ! k) = rs ! unat (Term_args (?ts ! i) ! k)\<close>
    if \<open>k < length (Term_args (?ts ! j))\<close> for k
  proof -
    have \<open>List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! j)) ! k = List.map (\<lambda>x. rs ! unat x) (Term_args (?ts ! i)) ! k\<close>
      using aj by simp
    then show ?thesis using that lj by simp
  qed
  then have \<open>congruent_p p rs j i\<close>
    unfolding congruent_p_def using fj lj by blast
  then have \<open>rs ! j = rs ! i\<close>
    using cl j(1) less.prems n unfolding closed_def by simp
  then have vsval: \<open>?M (unat (Term_fun (?ts ! i))) ?vs = unat (rs ! i)\<close>
    using e ej unfolding model_interp_def by simp
  have \<open>term_val ?M ?ts i = ?M (unat (Term_fun (?ts ! i))) (List.map (\<lambda>x. term_val ?M ?ts (unat x)) (Term_args (?ts ! i)))\<close>
    by (rule term_val_wf) (use less.prems wf_args[OF wf] in blast)
  then show ?case
    using args vsval by simp
qed

subsection \<open>Atom assignments\<close>

definition asserted :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>asserted p a m \<equiv> {(unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k))) | k. k < m \<and> a ! k}\<close>

lemma asserted_Suc:
  \<open>asserted p a (Suc k) = asserted p a k \<union>
     (if a ! k then {(unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k)))} else {})\<close>
  unfolding asserted_def by (auto simp add: less_Suc_eq)

lemma asserted_0 [simp]:
  \<open>asserted p a 0 = {}\<close>
  by (simp add: asserted_def)

lemma asserted_bounded:
  \<open>wf_problem p \<Longrightarrow> m \<le> length (Problem_atoms p) \<Longrightarrow>
   \<forall>(i, j) \<in> asserted p a m. i < length (Problem_terms p) \<and> j < length (Problem_terms p)\<close>
  unfolding asserted_def using wf_atom by fastforce

text \<open>The truth values of the atoms under an interpretation.\<close>
definition atom_vals :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> bool list\<close> where
  \<open>atom_vals I p \<equiv> List.map (atom_true I p) (Problem_atoms p)\<close>

definition prop_true :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>prop_true p a \<equiv> \<forall>c \<in> set (Problem_clauses p). \<exists>l \<in> set (Clause_lits c). a ! unat (Lit_atom l) = Lit_pos l\<close>

lemma problem_true_prop_true:
  \<open>wf_problem p \<Longrightarrow> problem_true I p \<longleftrightarrow> prop_true p (atom_vals I p)\<close>
  unfolding problem_true_def prop_true_def clause_true_def lit_true_def atom_vals_def
  using wf_lit by fastforce

text \<open>If exactly the atoms set in \<open>a\<close> hold under some \<open>I\<close>, the closure of the asserted pairs
  never joins the two sides of an atom unset in \<open>a\<close>.\<close>
lemma unsat_by_cc:
  assumes wf: \<open>wf_problem p\<close> and len: \<open>length a = length (Problem_atoms p)\<close>
      and av: \<open>atom_vals I p = a\<close>
      and k: \<open>k < length (Problem_atoms p)\<close> \<open>\<not> a ! k\<close>
      and cc: \<open>(unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k)))
                 \<in> cc p (asserted p a (length (Problem_atoms p)))\<close>
  shows False
proof -
  have \<open>\<forall>(i, j) \<in> asserted p a (length (Problem_atoms p)).
          term_val I (Problem_terms p) i = term_val I (Problem_terms p) j\<close>
    using av unfolding asserted_def atom_vals_def atom_true_def by auto
  from cc_sound[OF wf this cc] have \<open>atom_true I p (Problem_atoms p ! k)\<close>
    by (simp add: atom_true_def)
  then show False
    using av k unfolding atom_vals_def by auto
qed

text \<open>The model of the closure of the asserted pairs makes exactly the atoms set in \<open>a\<close> true,
  if no unset atom has both sides in one class.\<close>
lemma model_of_atom_vals:
  assumes wf: \<open>wf_problem p\<close> and len: \<open>length a = length (Problem_atoms p)\<close>
      and ok: \<open>rep_ok p (asserted p a (length (Problem_atoms p))) rs\<close> and cl: \<open>closed p rs\<close>
      and neg: \<open>\<forall>k < length (Problem_atoms p). \<not> a ! k \<longrightarrow>
                  rs ! unat (Atom_lhs (Problem_atoms p ! k)) \<noteq> rs ! unat (Atom_rhs (Problem_atoms p ! k))\<close>
  shows \<open>atom_vals (model_interp (model_of p rs)) p = a\<close>
proof (rule nth_equalityI)
  fix k assume \<open>k < length (atom_vals (model_interp (model_of p rs)) p)\<close>
  then have k: \<open>k < length (Problem_atoms p)\<close> by (simp add: atom_vals_def)
  then have pos: \<open>rs ! unat (Atom_lhs (Problem_atoms p ! k)) = rs ! unat (Atom_rhs (Problem_atoms p ! k))\<close>
    if \<open>a ! k\<close>
    using ok that unfolding rep_ok_def rep_has_def asserted_def by blast
  let ?M = \<open>model_interp (model_of p rs)\<close> and ?at = \<open>Problem_atoms p ! k\<close>
  have \<open>term_val ?M (Problem_terms p) (unat (Atom_lhs ?at)) = unat (rs ! unat (Atom_lhs ?at))\<close>
       \<open>term_val ?M (Problem_terms p) (unat (Atom_rhs ?at)) = unat (rs ! unat (Atom_rhs ?at))\<close>
    using wf_atom[OF wf k] model_of_term_val[OF wf ok cl] by blast+
  then have \<open>atom_vals ?M p ! k = (rs ! unat (Atom_lhs ?at) = rs ! unat (Atom_rhs ?at))\<close>
    using k by (simp add: atom_vals_def atom_true_def unat_eq_iff_eq)
  then show \<open>atom_vals ?M p ! k = a ! k\<close>
    using k neg pos by (cases \<open>a ! k\<close>) auto
qed (simp add: atom_vals_def len)

subsection \<open>Partial assignments and the search\<close>

text \<open>A partial assignment of the atoms is a pair of lists \<open>t\<close>, \<open>f\<close>: atom \<open>j\<close> is set true if
  \<open>t ! j\<close>, set false if \<open>f ! j\<close>, and unset if neither.\<close>

text \<open>Some interpretation makes the problem true and agrees with the partial assignment.\<close>
definition pext :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>pext p t f \<equiv> \<exists>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p \<and>
     (\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j))\<close>

text \<open>The literal \<open>l\<close> is false under the partial assignment.\<close>
definition lit_false :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_false t f l \<equiv> if Lit_pos l then f ! unat (Lit_atom l) else t ! unat (Lit_atom l)\<close>

text \<open>The literal \<open>l\<close> is true under the partial assignment.\<close>
definition lit_set_true :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_set_true t f l \<equiv> if Lit_pos l then t ! unat (Lit_atom l) else f ! unat (Lit_atom l)\<close>

text \<open>The atom of the literal \<open>l\<close> is unset.\<close>
definition lit_unset :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_unset t f l \<equiv> \<not> t ! unat (Lit_atom l) \<and> \<not> f ! unat (Lit_atom l)\<close>

lemma lit_falseI:
  \<open>\<not> lit_set_true t f l \<Longrightarrow> \<not> lit_unset t f l \<Longrightarrow> lit_false t f l\<close>
  unfolding lit_set_true_def lit_unset_def lit_false_def by (simp split: if_splits)

text \<open>The number of unset atoms: the measure of the search.\<close>
definition unset_count :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> nat\<close> where
  \<open>unset_count t f \<equiv> card {j. j < length t \<and> \<not> t ! j \<and> \<not> f ! j}\<close>

lemma pext_start:
  \<open>pext p (replicate (length (Problem_atoms p)) False) (replicate (length (Problem_atoms p)) False) \<longleftrightarrow>
   satisfiable p\<close>
  unfolding pext_def satisfiable_def by simp

text \<open>A clause over the atoms of \<open>p\<close> that every interpretation making \<open>p\<close> true satisfies: a
  clause of \<open>p\<close>, or a clause the search has learned.\<close>
definition clause_ok :: \<open>Problem \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_ok p c \<equiv> (\<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (Problem_atoms p)) \<and>
     (\<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p \<longrightarrow> clause_true I p c)\<close>

lemma clause_ok_problem:
  \<open>wf_problem p \<Longrightarrow> c \<in> set (Problem_clauses p) \<Longrightarrow> clause_ok p c\<close>
  unfolding clause_ok_def problem_true_def using wf_lit by blast

lemma pext_lit_false:
  assumes l: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close>
      and I: \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
      and lf: \<open>lit_false t f l\<close>
  shows \<open>\<not> lit_true I p l\<close>
  using l I lf unfolding lit_false_def lit_true_def atom_vals_def by (cases \<open>Lit_pos l\<close>) auto

text \<open>A clause whose literals are all false cuts the branch.\<close>
lemma pext_conflict:
  assumes c: \<open>clause_ok p c\<close>
      and f: \<open>\<forall>l \<in> set (Clause_lits c). lit_false t f l\<close>
  shows \<open>\<not> pext p t f\<close>
proof
  assume \<open>pext p t f\<close>
  then obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where I: \<open>problem_true I p\<close>
    \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    unfolding pext_def by blast
  obtain l where \<open>l \<in> set (Clause_lits c)\<close> \<open>lit_true I p l\<close>
    using I(1) c unfolding clause_ok_def clause_true_def by blast
  then show False using pext_lit_false[OF _ I(2)] f c unfolding clause_ok_def by blast
qed

text \<open>The literal \<open>u\<close> of a clause whose other literals are all false holds in every
  interpretation that extends the partial assignment and makes the problem true.\<close>
lemma pext_unit:
  assumes c: \<open>clause_ok p c\<close>
      and u: \<open>\<forall>l \<in> set (Clause_lits c). l = u \<or> lit_false t f l\<close>
      and e: \<open>pext p t f\<close> and len: \<open>length t = length (Problem_atoms p)\<close> \<open>length f = length (Problem_atoms p)\<close>
  shows \<open>if Lit_pos u then pext p (t[unat (Lit_atom u) := True]) f else pext p t (f[unat (Lit_atom u) := True])\<close>
proof -
  obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where I: \<open>problem_true I p\<close>
    \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    using e unfolding pext_def by blast
  obtain l where l: \<open>l \<in> set (Clause_lits c)\<close> \<open>lit_true I p l\<close>
    using I(1) c unfolding clause_ok_def clause_true_def by blast
  have r: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close> using c l(1) unfolding clause_ok_def by blast
  have lu: \<open>l = u\<close> using u l pext_lit_false[OF r I(2)] by blast
  have x: \<open>unat (Lit_atom u) < length (Problem_atoms p)\<close> using r lu by simp
  have v: \<open>atom_vals I p ! unat (Lit_atom u) = Lit_pos u\<close>
    using l(2) lu x unfolding lit_true_def atom_vals_def by simp
  show ?thesis
    using I v x len unfolding pext_def by (auto simp add: nth_list_update)
qed

text \<open>A learned clause: if the closure of the atoms set in \<open>e\<close> joins the two sides of atom
  \<open>k\<close>, the clause whose literals are \<open>k\<close> and the negations of the atoms set in \<open>e\<close> holds in every
  interpretation.\<close>
lemma conflict_clause_ok:
  assumes wf: \<open>wf_problem p\<close> and k: \<open>k < length (Problem_atoms p)\<close>
      and cc: \<open>(unat (Atom_lhs (Problem_atoms p ! k)), unat (Atom_rhs (Problem_atoms p ! k)))
                 \<in> cc p (asserted p e (length (Problem_atoms p)))\<close>
      and lits: \<open>\<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (Problem_atoms p)\<close>
      and kin: \<open>\<exists>l \<in> set (Clause_lits c). unat (Lit_atom l) = k \<and> Lit_pos l\<close>
      and ein: \<open>\<forall>j < length (Problem_atoms p). e ! j \<longrightarrow>
                  (\<exists>l \<in> set (Clause_lits c). unat (Lit_atom l) = j \<and> \<not> Lit_pos l)\<close>
  shows \<open>clause_ok p c\<close>
  unfolding clause_ok_def
proof (intro conjI allI impI)
  fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close>
  show \<open>clause_true I p c\<close>
  proof (cases \<open>\<exists>j < length (Problem_atoms p). e ! j \<and> \<not> atom_true I p (Problem_atoms p ! j)\<close>)
    case True
    then obtain j where j: \<open>j < length (Problem_atoms p)\<close> \<open>e ! j\<close> \<open>\<not> atom_true I p (Problem_atoms p ! j)\<close>
      by blast
    then obtain l where \<open>l \<in> set (Clause_lits c)\<close> \<open>unat (Lit_atom l) = j\<close> \<open>\<not> Lit_pos l\<close>
      using ein by blast
    then show ?thesis using j(3) unfolding clause_true_def lit_true_def by auto
  next
    case False
    then have \<open>\<forall>(i, i') \<in> asserted p e (length (Problem_atoms p)).
                 term_val I (Problem_terms p) i = term_val I (Problem_terms p) i'\<close>
      unfolding asserted_def atom_true_def by auto
    from cc_sound[OF wf this cc] have \<open>atom_true I p (Problem_atoms p ! k)\<close>
      by (simp add: atom_true_def)
    then show ?thesis using kin unfolding clause_true_def lit_true_def by auto
  qed
qed (use lits in blast)

lemma pext_branch:
  assumes \<open>pext p t f\<close>
  shows \<open>pext p (t[k := True]) f \<or> pext p t (f[k := True])\<close>
proof -
  obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where I: \<open>problem_true I p\<close>
    \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    using assms unfolding pext_def by blast
  show ?thesis
  proof (cases \<open>k < length (Problem_atoms p) \<and> atom_vals I p ! k\<close>)
    case True
    then have \<open>pext p (t[k := True]) f\<close>
      using I unfolding pext_def by (metis length_list_update nth_list_update nth_list_update_neq)
    then show ?thesis ..
  next
    case False
    then have \<open>pext p t (f[k := True])\<close>
      using I unfolding pext_def by (metis nth_list_update nth_list_update_neq)
    then show ?thesis ..
  qed
qed

text \<open>When every atom is set, the extensions of the partial assignment are exactly the
  interpretations whose atom values are \<open>t\<close>.\<close>
lemma pext_leaf:
  assumes len: \<open>length t = length (Problem_atoms p)\<close>
      and all: \<open>\<forall>j < length t. t ! j \<or> f ! j\<close> and e: \<open>pext p t f\<close>
  shows \<open>\<exists>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p \<and> atom_vals I p = t\<close>
proof -
  obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where I: \<open>problem_true I p\<close>
    \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    using e unfolding pext_def by blast
  have \<open>atom_vals I p = t\<close>
    using I(2) all len by (intro nth_equalityI) (auto simp add: atom_vals_def)
  then show ?thesis using I(1) by blast
qed

text \<open>If the closure of the equalities set true joins the two sides of an atom set false, the
  branch is cut.\<close>
lemma pext_cc_conflict:
  assumes wf: \<open>wf_problem p\<close> and len: \<open>length t = length (Problem_atoms p)\<close>
      and j: \<open>j < length (Problem_atoms p)\<close> \<open>f ! j\<close>
      and cc: \<open>(unat (Atom_lhs (Problem_atoms p ! j)), unat (Atom_rhs (Problem_atoms p ! j)))
                 \<in> cc p (asserted p t (length (Problem_atoms p)))\<close>
  shows \<open>\<not> pext p t f\<close>
proof
  assume \<open>pext p t f\<close>
  then obtain I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where
    I: \<open>\<forall>j < length (Problem_atoms p). (t ! j \<longrightarrow> atom_vals I p ! j) \<and> (f ! j \<longrightarrow> \<not> atom_vals I p ! j)\<close>
    unfolding pext_def by blast
  have \<open>\<forall>(i, i') \<in> asserted p t (length (Problem_atoms p)).
          term_val I (Problem_terms p) i = term_val I (Problem_terms p) i'\<close>
    using I unfolding asserted_def atom_vals_def atom_true_def by auto
  from cc_sound[OF wf this cc] have \<open>atom_true I p (Problem_atoms p ! j)\<close>
    by (simp add: atom_true_def)
  then show False
    using I j unfolding atom_vals_def by auto
qed

lemma unset_count_less:
  assumes \<open>j < length t\<close> \<open>\<not> t ! j\<close> \<open>\<not> f ! j\<close> \<open>length f = length t\<close>
  shows \<open>unset_count (t[j := True]) f < unset_count t f\<close> \<open>unset_count t (f[j := True]) < unset_count t f\<close>
proof -
  let ?S = \<open>{j. j < length t \<and> \<not> t ! j \<and> \<not> f ! j}\<close>
  have \<open>{i. i < length (t[j := True]) \<and> \<not> t[j := True] ! i \<and> \<not> f ! i} = ?S - {j}\<close>
    using assms by (auto simp add: nth_list_update)
  moreover have \<open>{i. i < length t \<and> \<not> t ! i \<and> \<not> f[j := True] ! i} = ?S - {j}\<close>
    using assms by (auto simp add: nth_list_update)
  moreover have \<open>card (?S - {j}) < card ?S\<close>
    using assms by (intro card_Diff1_less) auto
  ultimately show \<open>unset_count (t[j := True]) f < unset_count t f\<close> \<open>unset_count t (f[j := True]) < unset_count t f\<close>
    unfolding unset_count_def by simp_all
qed

end
