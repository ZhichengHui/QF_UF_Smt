theory QFUF_ElimSem
  imports QFUF_SmtBound
begin

section \<open>Equality elimination: the functions and their meaning\<close>

text \<open>The functions of the equality elimination in \<^verbatim>\<open>core/src/lib.rs\<close> (\<^verbatim>\<open>occ\<close> to \<^verbatim>\<open>restore\<close>)
  as HOL functions, and the two facts the top-level proof needs: the problem after elimination is
  satisfiable if the problem before is, and \<^verbatim>\<open>restore\<close> turns a model of the problem after into a
  model of the problem before.\<close>

subsection \<open>The functions\<close>

fun occ_m :: \<open>64 word \<Rightarrow> SmtTerm \<Rightarrow> nat\<close> and occs_m :: \<open>64 word \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close> where
  \<open>occ_m c (SmtTerm_Fun f args) = (if f = c then 1 else 0) + occs_m c args\<close>
| \<open>occ_m c (SmtTerm_Def d args) = occs_m c args\<close>
| \<open>occ_m c (SmtTerm_App op args) = occs_m c args\<close>
| \<open>occ_m c _ = 0\<close>
| \<open>occs_m c [] = 0\<close>
| \<open>occs_m c (a # r) = occ_m c a + occs_m c r\<close>

definition occ_all_m :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> nat\<close> where
  \<open>occ_all_m p a c \<equiv> occs_m c a + sum_list (map (\<lambda>d. occ_m c (SmtDef_body d)) (SmtProblem_defs_l p))\<close>

definition const_sym_m :: \<open>64 word \<Rightarrow> SmtTerm \<Rightarrow> 64 word\<close> where
  \<open>const_sym_m n t \<equiv> (case t of SmtTerm_Fun f args \<Rightarrow> if args = [] then f else n | _ \<Rightarrow> n)\<close>

definition eq_partner_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm \<Rightarrow> 64 word\<close> where
  \<open>eq_partner_m c n t \<equiv>
     (case t of
        SmtTerm_App op args \<Rightarrow>
          if op = SmtOp_Eq \<and> length args = 2 then
            (let x = const_sym_m n (args ! 0); y = const_sym_m n (args ! 1) in
             if x = c \<and> y < n \<and> y \<noteq> c then y else if y = c \<and> x < n \<and> x \<noteq> c then x else n)
          else n
      | _ \<Rightarrow> n)\<close>

definition eq_count_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close> where
  \<open>eq_count_m c n ts \<equiv> length (filter (\<lambda>t. eq_partner_m c n t < n) ts)\<close>

definition first_partner_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm list \<Rightarrow> 64 word\<close> where
  \<open>first_partner_m c n ts \<equiv>
     (case List.find (\<lambda>t. eq_partner_m c n t < n) ts of Some t \<Rightarrow> eq_partner_m c n t | None \<Rightarrow> n)\<close>

fun find_conj_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm \<Rightarrow> 64 word\<close>
  and find_conjs_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm list \<Rightarrow> 64 word\<close> where
  \<open>find_conj_m c tot n (SmtTerm_App op args) =
     (if op = SmtOp_And then
        (if word_of_nat (eq_count_m c n args) = tot then first_partner_m c n args
         else find_conjs_m c tot n args)
      else if op = SmtOp_Or then find_conjs_m c tot n args else n)\<close>
| \<open>find_conj_m c tot n _ = n\<close>
| \<open>find_conjs_m c tot n [] = n\<close>
| \<open>find_conjs_m c tot n (a # r) =
     (if find_conj_m c tot n a < n then find_conj_m c tot n a else find_conjs_m c tot n r)\<close>

definition elim_partner_m :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> 64 word\<close> where
  \<open>elim_partner_m p a c \<equiv>
     let fs = SmtProblem_funs_l p; n = word_of_nat (length fs) in
     if SmtFun_args_l (fs ! unat c) \<noteq> [] then n else
     let tot = sat (occ_all_m p a c) in
     if tot = 0 \<or> 2 ^ 63 \<le> tot then n else
     let g = find_conjs_m c (word_of_nat tot) n a in
     if g < n \<and> SmtFun_args_l (fs ! unat g) = [] \<and> SmtFun_ret (fs ! unat g) = SmtFun_ret (fs ! unat c) then g else n\<close>

fun rename_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm \<Rightarrow> SmtTerm\<close>
  and renames_m :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> SmtTerm list \<Rightarrow> SmtTerm list\<close> where
  \<open>rename_m c g (SmtTerm_Fun f args) = SmtTerm_Fun (if f = c then g else f) (renames_m c g args)\<close>
| \<open>rename_m c g (SmtTerm_Def d args) = SmtTerm_Def d (renames_m c g args)\<close>
| \<open>rename_m c g (SmtTerm_App op args) = SmtTerm_App op (renames_m c g args)\<close>
| \<open>rename_m c g t = t\<close>
| \<open>renames_m c g [] = []\<close>
| \<open>renames_m c g (a # r) = rename_m c g a # renames_m c g r\<close>

text \<open>The problem \<open>p\<close> with the assertions \<open>a\<close>.\<close>
definition wa :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> SmtProblem\<close> where
  \<open>wa p a \<equiv> make_SmtProblem (SmtProblem_num_sorts p) (SmtProblem_funs_l p) (SmtProblem_defs_l p) a\<close>

definition elim_step_m :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<times> 64 word list \<times> 64 word list \<Rightarrow> nat \<Rightarrow>
    SmtTerm list \<times> 64 word list \<times> 64 word list\<close> where
  \<open>elim_step_m p s c \<equiv>
     (case s of (a, cs, gs) \<Rightarrow>
        let g = elim_partner_m p a (word_of_nat c) in
        if g < word_of_nat (length (SmtProblem_funs_l p))
        then (renames_m (word_of_nat c) g a, cs @ [word_of_nat c], gs @ [g]) else (a, cs, gs))\<close>

definition eliminate_m :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<times> 64 word list \<times> 64 word list\<close> where
  \<open>eliminate_m p \<equiv> foldl (elim_step_m p) (SmtProblem_asserts_l p, [], []) [0..<length (SmtProblem_funs_l p)]\<close>

text \<open>Step \<open>k\<close> of \<^verbatim>\<open>restore\<close>: the table of \<open>cs ! i\<close> becomes that of \<open>gs ! i\<close>, for
  \<open>i = length cs - 1 - k\<close>.\<close>
definition fix_m :: \<open>64 word list \<Rightarrow> 64 word list \<Rightarrow> SmtInterp list \<Rightarrow> nat \<Rightarrow> SmtInterp list\<close> where
  \<open>fix_m cs gs fs k \<equiv>
     (let i = length cs - 1 - k in
      if unat (cs ! i) < length fs \<and> i < length gs \<and> unat (gs ! i) < length fs
      then fs[unat (cs ! i) := fs ! unat (gs ! i)] else fs)\<close>

definition restore_m :: \<open>SmtModel \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> SmtModel\<close> where
  \<open>restore_m m cs gs \<equiv>
     make_SmtModel (SmtModel_domains_l m) (foldl (fix_m cs gs) (SmtModel_funs_l m) [0..<length cs])\<close>

subsection \<open>Basic facts\<close>

lemma unat_eq_w: \<open>(unat (x :: 64 word) = unat y) = (x = y)\<close>
  by (auto intro: word_eq_unatI)

lemma renames_map: \<open>renames_m c g ts = map (rename_m c g) ts\<close>
  by (induction ts) auto

lemma length_renames: \<open>length (renames_m c g ts) = length ts\<close>
  by (simp add: renames_map)

lemma occs_sum: \<open>occs_m c ts = sum_list (map (occ_m c) ts)\<close>
  by (induction ts) auto

lemma wa_sel [simp]:
  \<open>SmtProblem_num_sorts (wa p a) = SmtProblem_num_sorts p\<close>
  \<open>SmtProblem_funs_l (wa p a) = SmtProblem_funs_l p\<close>
  \<open>SmtProblem_defs_l (wa p a) = SmtProblem_defs_l p\<close>
  \<open>SmtProblem_asserts_l (wa p a) = a\<close>
  by (simp_all add: wa_def)

lemma wa_self: \<open>wa p (SmtProblem_asserts_l p) = p\<close>
  by (cases p) (simp add: wa_def)

lemma wa_wa [simp]: \<open>wa (wa p a) b = wa p b\<close>
  by (simp add: wa_def)

lemma size_rename: \<open>size (rename_m c g t) = size t\<close> and size_renames: \<open>size_list size (renames_m c g ts) = size_list size ts\<close>
  by (induction c g t and c g ts rule: rename_m_renames_m.induct) auto

lemma repr_rename: \<open>smt_term_repr (rename_m c g t) = smt_term_repr t\<close>
  and repr_renames: \<open>(\<forall>a \<in> set (renames_m c g ts). smt_term_repr a) = (\<forall>a \<in> set ts. smt_term_repr a)\<close>
  by (induction c g t and c g ts rule: rename_m_renames_m.induct) (auto simp: renames_map)

lemma no_bv_rename: \<open>smt_term_no_bv (rename_m c g t) = smt_term_no_bv t\<close>
  and no_bv_renames: \<open>(\<forall>a \<in> set (renames_m c g ts). smt_term_no_bv a) = (\<forall>a \<in> set ts. smt_term_no_bv a)\<close>
  by (induction c g t and c g ts rule: rename_m_renames_m.induct) (auto simp: renames_map)

text \<open>Renaming \<open>c\<close> into a symbol of the same signature keeps the sort of a term.\<close>
lemma tsort_rename:
  shows \<open>unat c < length fs \<Longrightarrow> unat g < length fs \<Longrightarrow> fs ! unat g = fs ! unat c \<Longrightarrow>
           smt_tsort fs ds ps (rename_m c g t) = smt_tsort fs ds ps t\<close>
    and \<open>unat c < length fs \<Longrightarrow> unat g < length fs \<Longrightarrow> fs ! unat g = fs ! unat c \<Longrightarrow>
           map (smt_tsort fs ds ps) (renames_m c g ts) = map (smt_tsort fs ds ps) ts\<close>
  by (induction c g t and c g ts rule: rename_m_renames_m.induct) (auto simp: renames_map comp_def cong: map_cong image_cong)

subsection \<open>Evaluation\<close>

text \<open>Evaluating the renamed term is evaluating the term with \<open>c\<close> interpreted as \<open>g\<close>.\<close>
lemma eval_rename:
  \<open>smt_eval I dv vs (rename_m c g t) = smt_eval (I(unat c := I (unat g))) dv vs t\<close>
  \<open>map (smt_eval I dv vs) (renames_m c g ts) = map (smt_eval (I(unat c := I (unat g))) dv vs) ts\<close>
proof (induction c g t and c g ts rule: rename_m_renames_m.induct)
  case (1 c g f args)
  then show ?case by (auto simp: unat_eq_w)
qed auto

text \<open>A term without \<open>c\<close> has the same value under interpretations that differ only at \<open>c\<close>.\<close>
lemma eval_occ0:
  shows \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> J f = I f \<Longrightarrow> occ_m c t = 0 \<Longrightarrow> smt_eval J dv vs t = smt_eval I dv vs t\<close>
    and \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> J f = I f \<Longrightarrow> occs_m c ts = 0 \<Longrightarrow>
           map (smt_eval J dv vs) ts = map (smt_eval I dv vs) ts\<close>
proof (induction c t and c ts rule: occ_m_occs_m.induct)
  case (1 c f args)
  then show ?case by (auto simp: unat_eq_w split: if_splits cong: map_cong)
qed (auto cong: map_cong)

lemma def_sems_occ0:
  assumes \<open>\<And>f. f \<noteq> unat c \<Longrightarrow> J f = I f\<close> \<open>\<forall>d \<in> set ds. occ_m c (SmtDef_body d) = 0\<close>
  shows \<open>smt_def_sems J ds = smt_def_sems I ds\<close>
proof -
  have \<open>foldl (\<lambda>dv d. dv @ [\<lambda>vs. smt_eval J dv vs (SmtDef_body d)]) acc ds =
        foldl (\<lambda>dv d. dv @ [\<lambda>vs. smt_eval I dv vs (SmtDef_body d)]) acc ds\<close> for acc
    using assms(2)
  proof (induction ds arbitrary: acc)
    case Nil
    then show ?case by simp
  next
    case (Cons d ds)
    have \<open>(\<lambda>vs. smt_eval J acc vs (SmtDef_body d)) = (\<lambda>vs. smt_eval I acc vs (SmtDef_body d))\<close>
      using eval_occ0(1)[of c J I] assms(1) Cons.prems by auto
    then show ?case using Cons by simp
  qed
  then show ?thesis by (simp add: smt_def_sems_def)
qed

text \<open>Terms in which \<open>c\<close> is applied to no arguments only.\<close>
fun nullary_only :: \<open>64 word \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> and nullary_onlys :: \<open>64 word \<Rightarrow> SmtTerm list \<Rightarrow> bool\<close> where
  \<open>nullary_only c (SmtTerm_Fun f args) = ((f = c \<longrightarrow> args = []) \<and> nullary_onlys c args)\<close>
| \<open>nullary_only c (SmtTerm_Def d args) = nullary_onlys c args\<close>
| \<open>nullary_only c (SmtTerm_App op args) = nullary_onlys c args\<close>
| \<open>nullary_only c _ = True\<close>
| \<open>nullary_onlys c [] = True\<close>
| \<open>nullary_onlys c (a # r) = (nullary_only c a \<and> nullary_onlys c r)\<close>

lemma nullary_onlys_iff: \<open>nullary_onlys c ts = (\<forall>a \<in> set ts. nullary_only c a)\<close>
  by (induction ts) auto

lemma occ0_nullary: \<open>occ_m c t = 0 \<Longrightarrow> nullary_only c t\<close> \<open>occs_m c ts = 0 \<Longrightarrow> nullary_onlys c ts\<close>
  by (induction c t and c ts rule: occ_m_occs_m.induct) auto

lemma eval_nullary:
  shows \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> J f = I f \<Longrightarrow> J (unat c) [] = I (unat c) [] \<Longrightarrow>
           nullary_only c t \<Longrightarrow> smt_eval J dv vs t = smt_eval I dv vs t\<close>
    and \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> J f = I f \<Longrightarrow> J (unat c) [] = I (unat c) [] \<Longrightarrow>
           nullary_onlys c ts \<Longrightarrow> map (smt_eval J dv vs) ts = map (smt_eval I dv vs) ts\<close>
proof (induction c t and c ts rule: nullary_only_nullary_onlys.induct)
  case (1 c f args)
  then show ?case by (cases \<open>f = c\<close>) (auto simp: unat_eq_w cong: map_cong)
qed (auto cong: map_cong)

subsection \<open>The conjunction\<close>

lemma const_sym_eq: \<open>const_sym_m n t = x \<Longrightarrow> x \<noteq> n \<Longrightarrow> t = SmtTerm_Fun x []\<close>
  by (auto simp: const_sym_m_def split: SmtTerm.splits if_splits)

text \<open>A conjunct with a partner is \<open>(= c g)\<close> or \<open>(= g c)\<close>.\<close>
lemma eq_partner_shape:
  assumes \<open>eq_partner_m c n t = g\<close> \<open>g < n\<close> \<open>c < n\<close>
  shows \<open>g \<noteq> c \<and> (t = SmtTerm_App SmtOp_Eq [SmtTerm_Fun c [], SmtTerm_Fun g []] \<or>
                   t = SmtTerm_App SmtOp_Eq [SmtTerm_Fun g [], SmtTerm_Fun c []])\<close>
proof -
  obtain args where t: \<open>t = SmtTerm_App SmtOp_Eq args\<close> \<open>length args = 2\<close>
    using assms by (auto simp: eq_partner_m_def split: SmtTerm.splits if_splits)
  then obtain x y where args: \<open>args = [x, y]\<close>
    by (metis (no_types, lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
  show ?thesis
    using assms const_sym_eq[of n x] const_sym_eq[of n y]
    by (auto simp: eq_partner_m_def t args Let_def split: if_splits)
qed

lemma eq_partner_occ:
  assumes \<open>eq_partner_m c n t < n\<close> \<open>c < n\<close>
  shows \<open>occ_m c t = 1\<close> \<open>nullary_only c t\<close>
proof -
  obtain g where g: \<open>eq_partner_m c n t = g\<close> by simp
  show \<open>occ_m c t = 1\<close> \<open>nullary_only c t\<close>
    using eq_partner_shape[OF g assms(1)[unfolded g] assms(2)] by auto
qed

lemma eq_count_le_occs:
  \<open>c < n \<Longrightarrow> eq_count_m c n ts \<le> occs_m c ts\<close>
proof (induction ts)
  case Nil
  then show ?case by (simp add: eq_count_m_def)
next
  case (Cons a ts)
  then show ?case
    using eq_partner_occ(1)[of c n a] by (auto simp: eq_count_m_def)
qed

text \<open>If the conjuncts with a partner account for all occurrences of \<open>c\<close>, the other conjuncts
  have none.\<close>
lemma eq_count_tight:
  assumes \<open>c < n\<close> \<open>occs_m c ts \<le> eq_count_m c n ts\<close> \<open>t \<in> set ts\<close> \<open>\<not> eq_partner_m c n t < n\<close>
  shows \<open>occ_m c t = 0\<close>
  using assms(2-)
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  have le: \<open>eq_count_m c n ts \<le> occs_m c ts\<close> using eq_count_le_occs[OF assms(1)] .
  show ?case
  proof (cases \<open>eq_partner_m c n a < n\<close>)
    case True
    then have \<open>occ_m c a = 1\<close> using eq_partner_occ(1) assms(1) by blast
    then have \<open>occs_m c ts \<le> eq_count_m c n ts\<close> using Cons.prems(1) True by (simp add: eq_count_m_def)
    then show ?thesis using Cons True by auto
  next
    case False
    then have \<open>occ_m c a + occs_m c ts \<le> eq_count_m c n ts\<close>
      using Cons.prems(1) by (simp add: eq_count_m_def)
    then show ?thesis using Cons False le by auto
  qed
qed

lemma first_partner_find:
  assumes \<open>first_partner_m c n ts = g\<close> \<open>g < n\<close>
  shows \<open>\<exists>t \<in> set ts. eq_partner_m c n t = g\<close>
  using assms by (auto simp: first_partner_m_def split: option.splits dest!: find_Some_iff[THEN iffD1]
      intro: nth_mem)

lemma eq_count_word:
  assumes \<open>word_of_nat (eq_count_m c n ts) = (tot :: 64 word)\<close> \<open>length ts < 2 ^ 64\<close>
  shows \<open>eq_count_m c n ts = unat tot\<close>
proof -
  have \<open>eq_count_m c n ts < 2 ^ 64\<close>
    using assms(2) length_filter_le[of _ ts] unfolding eq_count_m_def by (meson le_less_trans)
  then show ?thesis using assms(1) unat_of_nat_eq[of \<open>eq_count_m c n ts\<close>, where 'a=64] by auto
qed

fun args_ok :: \<open>SmtTerm \<Rightarrow> bool\<close> and argss_ok :: \<open>SmtTerm list \<Rightarrow> bool\<close> where
  \<open>args_ok (SmtTerm_Fun f args) = (length args < 2 ^ 64 \<and> argss_ok args)\<close>
| \<open>args_ok (SmtTerm_Def d args) = (length args < 2 ^ 64 \<and> argss_ok args)\<close>
| \<open>args_ok (SmtTerm_App op args) = (length args < 2 ^ 64 \<and> argss_ok args)\<close>
| \<open>args_ok _ = True\<close>
| \<open>argss_ok [] = True\<close>
| \<open>argss_ok (a # r) = (args_ok a \<and> argss_ok r)\<close>

lemma argss_ok_iff: \<open>argss_ok ts = (\<forall>a \<in> set ts. args_ok a)\<close>
  by (induction ts) auto

lemma repr_args_ok: \<open>smt_term_repr t \<Longrightarrow> args_ok t\<close>
  and reprs_argss_ok: \<open>\<forall>a \<in> set ts. smt_term_repr a \<Longrightarrow> argss_ok ts\<close>
  by (induction t and ts rule: args_ok_argss_ok.induct) (auto simp: argss_ok_iff)

lemma occs_nth_le: \<open>k < length ts \<Longrightarrow> occ_m c (ts ! k) \<le> occs_m c ts\<close>
  using elem_le_sum_list[of k \<open>map (occ_m c) ts\<close>] by (simp add: occs_sum)

text \<open>Where \<^const>\<open>find_conj_m\<close> finds a partner, the term has at least \<open>tot\<close> occurrences of
  \<open>c\<close>.\<close>
lemma find_conj_occ:
  shows \<open>c < n \<Longrightarrow> find_conj_m c tot n t < n \<Longrightarrow> args_ok t \<Longrightarrow> unat tot \<le> occ_m c t\<close>
    and \<open>c < n \<Longrightarrow> find_conjs_m c tot n ts < n \<Longrightarrow> argss_ok ts \<Longrightarrow> unat tot \<le> occs_m c ts\<close>
proof (induction c tot n t and c tot n ts rule: find_conj_m_find_conjs_m.induct)
  case (1 c tot n op args)
  show ?case
  proof (cases \<open>op = SmtOp_And \<and> word_of_nat (eq_count_m c n args) = tot\<close>)
    case True
    then show ?thesis using 1 eq_count_word[of c n args tot] eq_count_le_occs[of c n args] by auto
  next
    case False
    then show ?thesis using 1 by (auto split: if_splits)
  qed
qed (auto split: if_splits)

text \<open>\<^const>\<open>find_conjs_m\<close> finds its partner in one term of the list, and the others have no
  occurrence of \<open>c\<close>.\<close>
lemma find_conjs_split:
  assumes \<open>c < n\<close> \<open>find_conjs_m c tot n ts = g\<close> \<open>g < n\<close> \<open>argss_ok ts\<close> \<open>occs_m c ts \<le> unat tot\<close>
  shows \<open>\<exists>k < length ts. find_conj_m c tot n (ts ! k) = g \<and> (\<forall>j < length ts. j \<noteq> k \<longrightarrow> occ_m c (ts ! j) = 0)\<close>
  using assms(2-)
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  show ?case
  proof (cases \<open>find_conj_m c tot n a < n\<close>)
    case True
    then have \<open>unat tot \<le> occ_m c a\<close> using find_conj_occ(1)[OF assms(1)] Cons.prems(3) by simp
    then have \<open>occs_m c ts = 0\<close> using Cons.prems(4) by simp
    then have \<open>\<forall>j < length ts. occ_m c (ts ! j) = 0\<close> using occs_nth_le[of _ ts c] by fastforce
    then show ?thesis using True Cons.prems(1) by (intro exI[of _ 0]) (auto simp: nth_Cons split: nat.splits)
  next
    case False
    then have f: \<open>find_conjs_m c tot n ts = g\<close> using Cons.prems(1) by simp
    have \<open>unat tot \<le> occs_m c ts\<close> using find_conj_occ(2)[OF assms(1)] f Cons.prems(2,3) by simp
    then have a0: \<open>occ_m c a = 0\<close> using Cons.prems(4) by simp
    obtain k where \<open>k < length ts\<close> \<open>find_conj_m c tot n (ts ! k) = g\<close> \<open>\<forall>j < length ts. j \<noteq> k \<longrightarrow> occ_m c (ts ! j) = 0\<close>
      using Cons f by auto
    then show ?thesis using a0 by (intro exI[of _ \<open>Suc k\<close>]) (auto simp: nth_Cons split: nat.splits)
  qed
qed

lemma smt_true_iff: \<open>smt_true v = (v = VBool True)\<close>
  by (cases v) auto

text \<open>The key step: with \<open>c\<close> interpreted as \<open>g\<close>, a term in which \<^const>\<open>find_conj_m\<close> finds the
  partner \<open>g\<close> stays true. In the conjunction, if it holds, \<open>c\<close> already has the value of \<open>g\<close>;
  above it there are only \<open>and\<close> and \<open>or\<close>, which are monotone.\<close>
lemma find_conj_true:
  assumes C: \<open>c < n\<close> and G: \<open>g < n\<close> and J: \<open>J = I(unat c := I (unat g))\<close>
  shows \<open>find_conj_m c tot n t = g \<Longrightarrow> args_ok t \<Longrightarrow> occ_m c t \<le> unat tot \<Longrightarrow>
           smt_true (smt_eval I dv vs t) \<Longrightarrow> smt_true (smt_eval J dv vs t)\<close>
proof (induction t)
  case (SmtTerm_App op args)
  have JI: \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> J f = I f\<close> using J by simp
  have ok: \<open>length args < 2 ^ 64\<close> \<open>argss_ok args\<close> using SmtTerm_App.prems(2) by auto
  have occ: \<open>occs_m c args \<le> unat tot\<close> using SmtTerm_App.prems(3) by simp
  show ?case
  proof (cases \<open>op = SmtOp_And \<and> word_of_nat (eq_count_m c n args) = tot\<close>)
    case True
    \<comment> \<open>The conjunction itself.\<close>
    then have op: \<open>op = SmtOp_And\<close> and fp: \<open>first_partner_m c n args = g\<close> using SmtTerm_App.prems(1) by auto
    have cnt: \<open>eq_count_m c n args = unat tot\<close> by (rule eq_count_word) (use True ok(1) in auto)
    obtain t0 where t0: \<open>t0 \<in> set args\<close> \<open>eq_partner_m c n t0 = g\<close> using first_partner_find[OF fp G] by blast
    have all: \<open>\<forall>x \<in> set args. smt_true (smt_eval I dv vs x)\<close> using SmtTerm_App.prems(4) op by auto
    have \<open>smt_true (smt_eval I dv vs t0)\<close> using all t0(1) by blast
    then have Icg: \<open>I (unat c) [] = I (unat g) []\<close>
      using eq_partner_shape[OF t0(2) G C] by auto
    have JIc: \<open>J (unat c) [] = I (unat c) []\<close> using J Icg by simp
    have \<open>nullary_only c x\<close> if \<open>x \<in> set args\<close> for x
    proof (cases \<open>eq_partner_m c n x < n\<close>)
      case True
      then show ?thesis using eq_partner_occ(2) C by blast
    next
      case False
      then show ?thesis using eq_count_tight[OF C _ that False] occ cnt occ0_nullary(1) by simp
    qed
    then have \<open>smt_eval J dv vs x = smt_eval I dv vs x\<close> if \<open>x \<in> set args\<close> for x
      using eval_nullary(1)[OF JI JIc] that by blast
    then show ?thesis using SmtTerm_App.prems(4) op by simp
  next
    case False
    have fc: \<open>find_conjs_m c tot n args = g\<close> \<open>op = SmtOp_And \<or> op = SmtOp_Or\<close>
      using False SmtTerm_App.prems(1) G by (auto split: if_splits)
    obtain k where k: \<open>k < length args\<close> \<open>find_conj_m c tot n (args ! k) = g\<close>
      \<open>\<forall>j < length args. j \<noteq> k \<longrightarrow> occ_m c (args ! j) = 0\<close>
      using find_conjs_split[OF C fc(1) G ok(2) occ] by blast
    have same: \<open>smt_eval J dv vs (args ! j) = smt_eval I dv vs (args ! j)\<close> if \<open>j < length args\<close> \<open>j \<noteq> k\<close> for j
      using eval_occ0(1)[OF JI] k(3) that by blast
    have IH: \<open>smt_true (smt_eval I dv vs (args ! k)) \<Longrightarrow> smt_true (smt_eval J dv vs (args ! k))\<close>
      using SmtTerm_App.IH[OF nth_mem[OF k(1)] k(2)] ok(2) k(1) occs_nth_le[OF k(1), of c] occ
      by (auto simp: argss_ok_iff)
    have \<open>smt_true (smt_eval J dv vs (args ! j))\<close> if \<open>smt_true (smt_eval I dv vs (args ! j))\<close> \<open>j < length args\<close> for j
      using IH same that by (cases \<open>j = k\<close>) auto
    then have mono: \<open>\<And>x. x \<in> set args \<Longrightarrow> smt_true (smt_eval I dv vs x) \<Longrightarrow> smt_true (smt_eval J dv vs x)\<close>
      by (metis in_set_conv_nth)
    show ?thesis using fc(2) SmtTerm_App.prems(4) mono by (auto, blast)
  qed
qed (use G in auto)

subsection \<open>One elimination\<close>

lemma ucnt_wa: \<open>ucnt (wa p a) n t = ucnt p n t\<close> \<open>ucnt_args (wa p a) n ts = ucnt_args p n ts\<close>
  by (induction p n t and p n ts rule: ucnt_ucnt_args.induct) auto

lemma ucnt_rename: \<open>ucnt p n (rename_m c g t) = ucnt p n t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  then show ?case by (auto simp: renames_map ucnt_args_sum comp_def cong: map_cong)
next
  case (SmtTerm_Def d args)
  then show ?case by (auto simp: renames_map ucnt_args_sum comp_def cong: map_cong)
next
  case (SmtTerm_App op args)
  then show ?case by (auto simp: renames_map ucnt_args_sum comp_def cong: map_cong)
qed auto

lemma dsum_wa: \<open>dsum (wa p a) d = dsum p d\<close>
  by (simp add: dsum_def ucnt_wa cong: if_cong)

lemma usize_rename: \<open>usize_m (wa p (renames_m c g a)) = usize_m (wa p a)\<close>
  by (simp add: usize_dsum dsum_wa ucnt_wa ucnt_rename renames_map comp_def)

text \<open>The facts of a successful \<^const>\<open>elim_partner_m\<close>.\<close>
lemma elim_partner_facts:
  assumes E: \<open>elim_partner_m p a c = g\<close> and G: \<open>g < word_of_nat (length (SmtProblem_funs_l p))\<close>
    and C: \<open>unat c < length (SmtProblem_funs_l p)\<close> and L: \<open>length (SmtProblem_funs_l p) < 2 ^ 63\<close>
    and A: \<open>argss_ok a\<close>
  defines \<open>n \<equiv> word_of_nat (length (SmtProblem_funs_l p)) :: 64 word\<close>
  shows \<open>unat g < length (SmtProblem_funs_l p)\<close> \<open>c < n\<close> \<open>g < n\<close>
    and \<open>SmtProblem_funs_l p ! unat g = SmtProblem_funs_l p ! unat c\<close>
    and \<open>SmtFun_args_l (SmtProblem_funs_l p ! unat c) = []\<close>
    and \<open>\<exists>tot :: 64 word. find_conjs_m c tot n a = g \<and> occs_m c a = unat tot\<close>
    and \<open>\<forall>d \<in> set (SmtProblem_defs_l p). occ_m c (SmtDef_body d) = 0\<close>
proof -
  let ?fs = \<open>SmtProblem_funs_l p\<close>
  have un: \<open>unat n = length ?fs\<close> using L by (simp add: n_def unat_of_nat_eq)
  show cn: \<open>c < n\<close> using C un by (simp add: word_less_nat_alt)
  show gn: \<open>g < n\<close> using G by (simp add: n_def)
  show \<open>unat g < length ?fs\<close> using gn un by (simp add: word_less_nat_alt)
  let ?T = \<open>sat (occ_all_m p a c)\<close>
  have h: \<open>SmtFun_args_l (?fs ! unat c) = [] \<and> \<not> (?T = 0 \<or> 2 ^ 63 \<le> ?T) \<and>
      find_conjs_m c (word_of_nat ?T) n a = g \<and> SmtFun_args_l (?fs ! unat g) = [] \<and>
      SmtFun_ret (?fs ! unat g) = SmtFun_ret (?fs ! unat c)\<close>
    using E gn unfolding elim_partner_m_def n_def Let_def by (auto split: if_splits)
  show \<open>SmtFun_args_l (?fs ! unat c) = []\<close> using h by simp
  show \<open>?fs ! unat g = ?fs ! unat c\<close> using h by (cases \<open>?fs ! unat g\<close>; cases \<open>?fs ! unat c\<close>) auto
  have T: \<open>?T = occ_all_m p a c\<close> \<open>occ_all_m p a c < 2 ^ 63\<close> using h by (auto simp: sat_def)
  let ?tot = \<open>word_of_nat ?T :: 64 word\<close>
  have ut: \<open>unat ?tot = occ_all_m p a c\<close> using T by (simp add: unat_of_nat_eq)
  have \<open>unat ?tot \<le> occs_m c a\<close> using find_conj_occ(2)[OF cn _ A] h gn by simp
  then have \<open>occs_m c a = unat ?tot\<close> \<open>sum_list (map (\<lambda>d. occ_m c (SmtDef_body d)) (SmtProblem_defs_l p)) = 0\<close>
    using ut by (auto simp: occ_all_m_def)
  then show \<open>\<exists>tot :: 64 word. find_conjs_m c tot n a = g \<and> occs_m c a = unat tot\<close>
    and \<open>\<forall>d \<in> set (SmtProblem_defs_l p). occ_m c (SmtDef_body d) = 0\<close>
    using h by auto
qed

text \<open>The problem after one elimination is satisfiable if the problem before is.\<close>
lemma elim_satisfies:
  assumes E: \<open>elim_partner_m p a c = g\<close> and G: \<open>g < word_of_nat (length (SmtProblem_funs_l p))\<close>
    and C: \<open>unat c < length (SmtProblem_funs_l p)\<close> and L: \<open>length (SmtProblem_funs_l p) < 2 ^ 63\<close>
    and A: \<open>argss_ok a\<close> and S: \<open>smt_satisfies (wa p a) I\<close>
  shows \<open>smt_satisfies (wa p (renames_m c g a)) I\<close>
proof -
  let ?n = \<open>word_of_nat (length (SmtProblem_funs_l p)) :: 64 word\<close>
  note F = elim_partner_facts[OF E G C L A]
  obtain tot where tot: \<open>find_conjs_m c tot ?n a = g\<close> \<open>occs_m c a = unat tot\<close> using F(6) by blast
  let ?J = \<open>I(unat c := I (unat g))\<close>
  let ?dv = \<open>smt_def_sems I (SmtProblem_defs_l p)\<close>
  have JI: \<open>\<forall>f. f \<noteq> unat c \<longrightarrow> ?J f = I f\<close> by simp
  obtain k where k: \<open>k < length a\<close> \<open>find_conj_m c tot ?n (a ! k) = g\<close>
    \<open>\<forall>j < length a. j \<noteq> k \<longrightarrow> occ_m c (a ! j) = 0\<close>
    using find_conjs_split[OF F(2) tot(1) F(3) A] tot(2) by auto
  have true: \<open>smt_eval I ?dv [] t = VBool True\<close> if \<open>t \<in> set a\<close> for t
    using S that by (simp add: smt_satisfies_def)
  have \<open>smt_eval ?J ?dv [] (a ! j) = VBool True\<close> if j: \<open>j < length a\<close> for j
  proof (cases \<open>j = k\<close>)
    case True
    have \<open>smt_true (smt_eval I ?dv [] (a ! k))\<close> using true[OF nth_mem[OF k(1)]] by simp
    then have \<open>smt_true (smt_eval ?J ?dv [] (a ! k))\<close>
      using find_conj_true[OF F(2) F(3) HOL.refl k(2)] A k(1) occs_nth_le[OF k(1), of c] tot(2)
      by (auto simp: argss_ok_iff)
    then show ?thesis using True by (simp add: smt_true_iff)
  next
    case False
    have \<open>occ_m c (a ! j) = 0\<close> using k(3) j False by simp
    then have \<open>smt_eval ?J ?dv [] (a ! j) = smt_eval I ?dv [] (a ! j)\<close> by (rule eval_occ0(1)[OF JI])
    then show ?thesis using true[OF nth_mem[OF j]] by simp
  qed
  then have \<open>\<forall>t \<in> set a. smt_eval ?J ?dv [] t = VBool True\<close> by (metis in_set_conv_nth)
  moreover have \<open>smt_def_sems ?J (SmtProblem_defs_l p) = ?dv\<close>
    using def_sems_occ0[of c ?J I] F(7) by simp
  ultimately show ?thesis
    by (simp add: smt_satisfies_def renames_map eval_rename)
qed

text \<open>\<^verbatim>\<open>restore\<close>'s step on a model: \<open>c\<close> gets the table of \<open>g\<close>.\<close>
definition fixm :: \<open>SmtModel \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> SmtModel\<close> where
  \<open>fixm m c g \<equiv> make_SmtModel (SmtModel_domains_l m) ((SmtModel_funs_l m)[unat c := SmtModel_funs_l m ! unat g])\<close>

lemma fixm_interp:
  assumes \<open>unat c < length (SmtModel_funs_l m)\<close>
  shows \<open>smt_model_interp (fixm m c g) = (smt_model_interp m)(unat c := smt_model_interp m (unat g))\<close>
  using assms by (auto simp: fixm_def smt_model_interp_def fun_eq_iff nth_list_update)

text \<open>A model of the problem after one elimination, fixed by \<^const>\<open>fixm\<close>, is a model of the
  problem before.\<close>
lemma elim_model:
  assumes E: \<open>elim_partner_m p a c = g\<close> and G: \<open>g < word_of_nat (length (SmtProblem_funs_l p))\<close>
    and C: \<open>unat c < length (SmtProblem_funs_l p)\<close> and L: \<open>length (SmtProblem_funs_l p) < 2 ^ 63\<close>
    and A: \<open>argss_ok a\<close> and M: \<open>smt_is_model (wa p (renames_m c g a)) m\<close>
  shows \<open>smt_is_model (wa p a) (fixm m c g)\<close>
proof -
  note F = elim_partner_facts[OF E G C L A]
  let ?fs = \<open>SmtProblem_funs_l p\<close>
  have wf: \<open>smt_model_wf (wa p (renames_m c g a)) m\<close> and sat: \<open>smt_satisfies (wa p (renames_m c g a)) (smt_model_interp m)\<close>
    using M by (simp_all add: smt_is_model_def)
  have len: \<open>length (SmtModel_funs_l m) = length ?fs\<close> using wf by (simp add: smt_model_wf_def Let_def)
  let ?I = \<open>smt_model_interp m\<close>
  let ?J = \<open>?I(unat c := ?I (unat g))\<close>
  have J: \<open>smt_model_interp (fixm m c g) = ?J\<close> using fixm_interp C len by simp
  have \<open>smt_model_wf (wa p a) (fixm m c g)\<close>
    using wf C len F(1,4) unfolding smt_model_wf_def Let_def
    by (auto simp: fixm_def nth_list_update)
  moreover have \<open>smt_def_sems ?J (SmtProblem_defs_l p) = smt_def_sems ?I (SmtProblem_defs_l p)\<close>
    using def_sems_occ0[of c ?J ?I] F(7) by simp
  then have \<open>smt_satisfies (wa p a) ?J\<close>
    using sat by (simp add: smt_satisfies_def renames_map eval_rename)
  ultimately show ?thesis using J by (simp add: smt_is_model_def)
qed

lemma elim_wf:
  assumes \<open>unat c < length (SmtProblem_funs_l p)\<close> \<open>unat g < length (SmtProblem_funs_l p)\<close>
    \<open>SmtProblem_funs_l p ! unat g = SmtProblem_funs_l p ! unat c\<close>
  shows \<open>smt_wf (wa p (renames_m c g a)) = smt_wf (wa p a)\<close>
  using tsort_rename(1)[OF assms] by (simp add: smt_wf_def renames_map)

lemma elim_repr: \<open>smt_repr_ok (wa p (renames_m c g a)) = smt_repr_ok (wa p a)\<close>
  using repr_renames[of c g a] by (simp add: smt_repr_ok_def renames_map)

lemma elim_fragment: \<open>smt_fragment (wa p (renames_m c g a)) = smt_fragment (wa p a)\<close>
  using no_bv_renames[of c g a] by (simp add: smt_fragment_def renames_map)

subsection \<open>The whole elimination\<close>

lemma restore_nil: \<open>restore_m m [] [] = m\<close>
  by (cases m) (simp add: restore_m_def)

lemma restore_snoc:
  assumes L: \<open>length cs = length gs\<close> and C: \<open>unat c < length (SmtModel_funs_l m)\<close> and G: \<open>unat g < length (SmtModel_funs_l m)\<close>
  shows \<open>restore_m m (cs @ [c]) (gs @ [g]) = restore_m (fixm m c g) cs gs\<close>
proof -
  let ?L = \<open>length cs\<close>
  have u: \<open>[0..<Suc ?L] = 0 # map Suc [0..<?L]\<close> by (metis map_Suc_upt upt_conv_Cons zero_less_Suc)
  have s0: \<open>fix_m (cs @ [c]) (gs @ [g]) (SmtModel_funs_l m) 0 = (SmtModel_funs_l m)[unat c := SmtModel_funs_l m ! unat g]\<close>
    using L C G by (simp add: fix_m_def nth_append)
  have sk: \<open>fix_m (cs @ [c]) (gs @ [g]) F (Suc k) = fix_m cs gs F k\<close> if \<open>k \<in> set [0..<?L]\<close> for F k
    using L that by (auto simp: fix_m_def nth_append Let_def)
  have \<open>foldl (fix_m (cs @ [c]) (gs @ [g])) F (map Suc [0..<?L]) = foldl (fix_m cs gs) F [0..<?L]\<close> for F
    unfolding foldl_map using sk by (intro foldl_cong) auto
  then show ?thesis
    unfolding restore_m_def fixm_def using u s0 by simp
qed

text \<open>The invariant of the loop of \<^verbatim>\<open>eliminate\<close>, with the assertions \<open>a\<close> so far and the
  eliminated symbols \<open>cs\<close> with their partners \<open>gs\<close>.\<close>
definition elim_inv :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<times> 64 word list \<times> 64 word list \<Rightarrow> bool\<close> where
  \<open>elim_inv p s \<equiv>
     (case s of (a, cs, gs) \<Rightarrow>
        smt_wf (wa p a) = smt_wf p \<and> smt_repr_ok (wa p a) = smt_repr_ok p \<and>
        smt_fragment (wa p a) = smt_fragment p \<and> usize_m (wa p a) = usize_m p \<and>
        size_list size a = size_list size (SmtProblem_asserts_l p) \<and> length a = length (SmtProblem_asserts_l p) \<and>
        length cs = length gs \<and>
        (smt_satisfiable p \<longrightarrow> smt_satisfiable (wa p a)) \<and>
        (\<forall>m. smt_is_model (wa p a) m \<longrightarrow> smt_is_model p (restore_m m cs gs)))\<close>

lemma elim_inv_step:
  assumes R: \<open>smt_repr_ok p\<close> and K: \<open>k < length (SmtProblem_funs_l p)\<close> and I: \<open>elim_inv p s\<close>
  shows \<open>elim_inv p (elim_step_m p s k)\<close>
proof -
  obtain a cs gs where s: \<open>s = (a, cs, gs)\<close> by (cases s)
  let ?fs = \<open>SmtProblem_funs_l p\<close>
  let ?c = \<open>word_of_nat k :: 64 word\<close>
  let ?g = \<open>elim_partner_m p a ?c\<close>
  have L: \<open>length ?fs < 2 ^ 63\<close> using R by (simp add: smt_repr_ok_def)
  have C: \<open>unat ?c < length ?fs\<close> using K L by (simp add: unat_of_nat_eq)
  have inv: \<open>smt_wf (wa p a) = smt_wf p\<close> \<open>smt_repr_ok (wa p a)\<close> \<open>smt_fragment (wa p a) = smt_fragment p\<close>
    \<open>usize_m (wa p a) = usize_m p\<close> \<open>size_list size a = size_list size (SmtProblem_asserts_l p)\<close>
    \<open>length a = length (SmtProblem_asserts_l p)\<close> \<open>length cs = length gs\<close>
    \<open>smt_satisfiable p \<longrightarrow> smt_satisfiable (wa p a)\<close>
    \<open>\<forall>m. smt_is_model (wa p a) m \<longrightarrow> smt_is_model p (restore_m m cs gs)\<close>
    using I R by (simp_all add: elim_inv_def s)
  have A: \<open>argss_ok a\<close> using inv(2) reprs_argss_ok by (simp add: smt_repr_ok_def)
  show ?thesis
  proof (cases \<open>?g < word_of_nat (length ?fs)\<close>)
    case False
    then show ?thesis using I by (simp add: elim_step_m_def s)
  next
    case True
    note F = elim_partner_facts[OF HOL.refl True C L A]
    let ?a = \<open>renames_m ?c ?g a\<close>
    have sat: \<open>smt_satisfiable (wa p ?a)\<close> if \<open>smt_satisfiable (wa p a)\<close>
      using that elim_satisfies[OF HOL.refl True C L A]
      by (auto simp: smt_satisfiable_def smt_interp_ok_def)
    have model: \<open>smt_is_model p (restore_m m (cs @ [?c]) (gs @ [?g]))\<close> if \<open>smt_is_model (wa p ?a) m\<close> for m
    proof -
      have \<open>length (SmtModel_funs_l m) = length ?fs\<close>
        using that by (simp add: smt_is_model_def smt_model_wf_def Let_def)
      then have \<open>restore_m m (cs @ [?c]) (gs @ [?g]) = restore_m (fixm m ?c ?g) cs gs\<close>
        using restore_snoc[OF inv(7)] C F(1) by simp
      then show ?thesis using inv(9) elim_model[OF HOL.refl True C L A that] by simp
    qed
    show ?thesis
      using R True inv sat model length_renames elim_wf[OF C F(1) F(4)] elim_repr elim_fragment usize_rename size_renames
      by (simp add: elim_step_m_def s elim_inv_def Let_def)
  qed
qed

lemma elim_inv_foldl:
  assumes R: \<open>smt_repr_ok p\<close> and K: \<open>k \<le> length (SmtProblem_funs_l p)\<close>
  shows \<open>elim_inv p (foldl (elim_step_m p) (SmtProblem_asserts_l p, [], []) [0..<k])\<close>
  using K
proof (induction k)
  case 0
  then show ?case by (simp add: elim_inv_def wa_self restore_nil)
next
  case (Suc k)
  then show ?case using elim_inv_step[OF R] by simp
qed

text \<open>The result of the elimination.\<close>
theorem eliminate_correct:
  assumes R: \<open>smt_repr_ok p\<close> and E: \<open>eliminate_m p = (a, cs, gs)\<close>
  shows \<open>smt_wf (wa p a) = smt_wf p\<close> \<open>smt_repr_ok (wa p a)\<close> \<open>smt_fragment (wa p a) = smt_fragment p\<close>
    and \<open>usize_m (wa p a) = usize_m p\<close> \<open>size_list size a = size_list size (SmtProblem_asserts_l p)\<close>
    and \<open>length a = length (SmtProblem_asserts_l p)\<close>
    and \<open>smt_satisfiable p \<Longrightarrow> smt_satisfiable (wa p a)\<close>
    and \<open>smt_is_model (wa p a) m \<Longrightarrow> smt_is_model p (restore_m m cs gs)\<close>
  using elim_inv_foldl[OF R order.refl] E R by (simp_all add: eliminate_m_def elim_inv_def)

end
