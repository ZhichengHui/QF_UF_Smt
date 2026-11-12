theory QFUF_SmtBound
  imports QFUF_SmtSize
begin

section \<open>The size check bounds the translation\<close>

text \<open>The cost of a state: the numbers of terms, atoms and clauses, the lengths of the clauses and
  of the argument lists of the terms, and the next unused function symbol. The doc comment of
  \<^verbatim>\<open>uf_size\<close> bounds this sum by \<^const>\<open>usize_m\<close>.\<close>
definition cst :: \<open>st \<Rightarrow> nat\<close> where
  \<open>cst s \<equiv> length (st_terms s) + length (st_atoms s) + length (st_clauses s) +
     sum_list (map (\<lambda>c. length (Clause_lits c)) (st_clauses s)) +
     sum_list (map (\<lambda>t. length (Term_args t)) (st_terms s)) + st_next s\<close>

subsection \<open>The primitive operations\<close>

lemma cst_add_term: \<open>cst (fst (add_term_m s f a)) = cst s + 1 + length a\<close>
  by (simp add: cst_def add_term_m_def)

lemma cst_add_atom: \<open>cst (fst (add_atom_m s l r)) = Suc (cst s)\<close>
  by (simp add: cst_def add_atom_m_def)

lemma cst_add_clause: \<open>cst (add_clause_m s ls) = cst s + 1 + length ls\<close>
  by (simp add: cst_def add_clause_m_def)

lemma cst_new_const: \<open>cst (fst (new_const_m s)) = cst s + 2\<close>
  by (simp add: cst_def new_const_m_def add_term_m_def)

lemma cst_new_lit: \<open>cst (fst (new_lit_m s)) = cst s + 3\<close>
  by (simp add: new_lit_m_def Let_def cst_add_atom cst_new_const)

lemma cst_enc_term: \<open>cst (fst (enc_term_m s e)) \<le> cst s + 10\<close>
  by (cases e) (simp_all add: Let_def cst_add_clause cst_add_atom cst_new_const)

lemma cst_andor_fold: \<open>cst (foldl (\<lambda>s l. add_clause_m s (andor_cl_m v cj l)) s ls) = cst s + 3 * length ls\<close>
  by (induction ls arbitrary: s) (simp_all add: cst_add_clause andor_cl_m_def)

lemma cst_gate_andor: \<open>cst (fst (gate_andor_m s ls cj)) = cst s + 4 * length ls + 5\<close>
  by (simp add: gate_andor_m_def Let_def cst_add_clause cst_andor_fold cst_new_lit)

lemma cst_gate_xor: \<open>cst (fst (gate_xor_m s x y)) = cst s + 19\<close>
  by (simp add: gate_xor_m_def Let_def cst_add_clause cst_new_lit)

lemma cst_gate_ite: \<open>cst (fst (gate_ite_m s c x y)) = cst s + 19\<close>
  by (simp add: gate_ite_m_def Let_def cst_add_clause cst_new_lit)

lemma cst_ite_term: \<open>cst (fst (ite_term_m s es)) \<le> cst s + 30\<close>
proof -
  have e: \<open>cst (fst (enc_term_m (fst (enc_term_m s1 x)) y)) \<le> cst s1 + 20\<close> for s1 x y
    using cst_enc_term[of s1 x] cst_enc_term[of \<open>fst (enc_term_m s1 x)\<close> y] by simp
  show ?thesis using e[of \<open>fst (new_const_m s)\<close> \<open>es ! 1\<close> \<open>es ! 2\<close>] cst_new_const[of s]
    by (simp add: ite_term_m_def Let_def cst_add_clause cst_add_atom)
qed

lemma cst_eq_step:
  \<open>cst (fst (eq_step_m es dist sl ij)) \<le> cst (fst sl) + 21 \<and> length (snd (eq_step_m es dist sl ij)) = Suc (length (snd sl))\<close>
proof -
  obtain s ls i j where e: \<open>sl = (s, ls)\<close> \<open>ij = (i, j)\<close> by (cases sl, cases ij) auto
  have a: \<open>cst (fst (enc_term_m (fst (enc_term_m s (es ! i))) (es ! j))) \<le> cst s + 20\<close>
    using cst_enc_term[of s \<open>es ! i\<close>] cst_enc_term[of \<open>fst (enc_term_m s (es ! i))\<close> \<open>es ! j\<close>] by simp
  show ?thesis using a by (simp add: e eq_step_m_def Let_def cst_gate_xor cst_add_atom)
qed

lemma cst_eq_fold:
  \<open>cst (fst (foldl (eq_step_m es dist) sl prs)) \<le> cst (fst sl) + 21 * length prs \<and>
   length (snd (foldl (eq_step_m es dist) sl prs)) = length (snd sl) + length prs\<close>
proof (induction prs arbitrary: sl)
  case Nil
  then show ?case by simp
next
  case (Cons a prs)
  show ?case using Cons[of \<open>eq_step_m es dist sl a\<close>] cst_eq_step[of es dist sl a] by simp
qed

lemma eq_pairs_sum: \<open>2 * sum_list (map (\<lambda>i. n - Suc i) [0..<n]) \<le> n * n\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have m: \<open>map (\<lambda>i. n - i) [0..<n] = map (\<lambda>i. Suc (n - Suc i)) [0..<n]\<close>
    by (rule map_cong) (simp_all add: Suc_diff_Suc)
  have m2: \<open>sum_list (map (\<lambda>i. n - i) [0..<n]) = sum_list (map (\<lambda>i. n - Suc i) [0..<n]) + n\<close>
    unfolding m sum_list_Suc by simp
  have \<open>sum_list (map (\<lambda>i. Suc n - Suc i) [0..<Suc n]) = sum_list (map (\<lambda>i. n - Suc i) [0..<n]) + n\<close>
    using m2 by simp
  then show ?case using Suc by simp
qed

lemma eq_pairs_len: \<open>2 * length (eq_pairs_m n dist) \<le> n * n\<close>
proof -
  have \<open>length (eq_pairs_m n dist) \<le> length (concat (map (\<lambda>i. map (\<lambda>j. (i, j)) [Suc i..<n]) [0..<n]))\<close>
    unfolding eq_pairs_m_def by (rule length_filter_le)
  also have \<open>\<dots> = sum_list (map (\<lambda>i. n - Suc i) [0..<n])\<close>
    by (simp add: length_concat comp_def)
  finally show ?thesis using eq_pairs_sum[of n] by simp
qed

lemma nw_ge: \<open>16 * Suc k \<le> nw k\<close>
  by (simp add: nw_def power2_eq_square)

lemma nw_expand: \<open>nw k = 16 * (k * k) + 32 * k + 16\<close>
  by (simp add: nw_def power2_eq_square algebra_simps)

lemma cst_enc_eq: \<open>cst (fst (enc_eq_m s es dist)) \<le> cst s + nw (length es)\<close>
proof -
  define P where \<open>P = length (eq_pairs_m (length es) dist)\<close>
  define r where \<open>r = foldl (eq_step_m es dist) (s, []) (eq_pairs_m (length es) dist)\<close>
  have f: \<open>cst (fst r) \<le> cst s + 21 * P\<close> \<open>length (snd r) = P\<close>
    using cst_eq_fold[of es dist \<open>(s, [])\<close> \<open>eq_pairs_m (length es) dist\<close>] by (simp_all add: r_def P_def)
  have p: \<open>2 * P \<le> length es * length es\<close> unfolding P_def by (rule eq_pairs_len)
  have \<open>cst (fst (enc_eq_m s es dist)) = cst (fst r) + 4 * P + 5\<close>
    by (simp add: enc_eq_m_def Let_def cst_gate_andor f(2) flip: r_def)
  then show ?thesis using f(1) p by (simp add: nw_expand)
qed

lemma cst_xor_fold: \<open>cst (fst (foldl xor_step_m sa es)) = cst (fst sa) + 19 * length es\<close>
proof (induction es arbitrary: sa)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  show ?case using Cons[of \<open>xor_step_m sa e\<close>] by (cases sa) (simp add: xor_step_m_def cst_gate_xor)
qed

lemma cst_enc_terms_fold:
  \<open>cst (fst (foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) st0 es)) \<le> cst (fst st0) + 10 * length es \<and>
   length (snd (foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) st0 es)) = length (snd st0) + length es\<close>
proof (induction es arbitrary: st0)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain s ts where e: \<open>st0 = (s, ts)\<close> by (cases st0)
  show ?case using Cons[of \<open>(fst (enc_term_m s e), ts @ [snd (enc_term_m s e)])\<close>] cst_enc_term[of s e]
    by (simp add: e Let_def)
qed

lemma cst_enc_terms: \<open>cst (fst (enc_terms_m s es)) \<le> cst s + 10 * length es \<and> length (snd (enc_terms_m s es)) = length es\<close>
  using cst_enc_terms_fold[of \<open>(s, [])\<close> es] by (simp add: enc_terms_m_def)

lemma cst_enc_app: \<open>(op = SmtOp_Ite \<longrightarrow> es \<noteq> []) \<Longrightarrow> cst (fst (enc_app_m s op es)) \<le> cst s + nw (length es)\<close>
proof (cases op)
  case SmtOp_Ite
  assume a: \<open>op = SmtOp_Ite \<longrightarrow> es \<noteq> []\<close>
  have l: \<open>32 \<le> nw (length es)\<close> using a SmtOp_Ite nw_ge[of \<open>length es\<close>] by (cases es) auto
  show ?thesis using l cst_ite_term[of s es] by (simp add: SmtOp_Ite cst_gate_ite)
qed (use nw_ge[of \<open>length es\<close>] cst_enc_eq[of s es False] cst_enc_eq[of s es True] in \<open>auto simp: Let_def cst_gate_andor cst_xor_fold cst_enc_eq implies_lits_m_def nw_expand\<close>)

subsection \<open>The translation of terms\<close>

text \<open>Every \<open>ite\<close> has an argument (in a well-sorted term, it has three).\<close>
fun ar_ok :: \<open>SmtTerm \<Rightarrow> bool\<close> where
  \<open>ar_ok (SmtTerm_Fun f args) = (\<forall>a \<in> set args. ar_ok a)\<close>
| \<open>ar_ok (SmtTerm_Def d args) = (\<forall>a \<in> set args. ar_ok a)\<close>
| \<open>ar_ok (SmtTerm_App op args) = ((op = SmtOp_Ite \<longrightarrow> args \<noteq> []) \<and> (\<forall>a \<in> set args. ar_ok a))\<close>
| \<open>ar_ok _ = True\<close>

lemma tsort_ar_ok: \<open>smt_tsort fs ds ps t \<noteq> None \<Longrightarrow> ar_ok t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  then show ?case using map_eq_Some_ne by (fastforce split: if_splits)
next
  case (SmtTerm_Def d args)
  then show ?case using map_eq_Some_ne by (fastforce split: if_splits)
next
  case (SmtTerm_App op args)
  have n: \<open>None \<notin> set (map (smt_tsort fs ds ps) args)\<close>
    and o: \<open>smt_op_sort op (map (the \<circ> smt_tsort fs ds ps) args) \<noteq> None\<close>
    using SmtTerm_App.prems by (auto split: if_splits)
  have t: \<open>smt_tsort fs ds ps a \<noteq> None\<close> if \<open>a \<in> set args\<close> for a
    using n that by (metis imageI list.set_map)
  have i: \<open>op = SmtOp_Ite \<longrightarrow> args \<noteq> []\<close> using o op_sort_ite by fastforce
  show ?case using SmtTerm_App.IH t i by auto
qed auto

lemma tr_args_len: \<open>length (snd (tr_args_m p dm env n s ts)) = length ts\<close>
  by (induction ts arbitrary: s) (simp_all add: Let_def)

lemma tr_cst:
  \<open>(\<forall>d < n. ar_ok (SmtDef_body (SmtProblem_defs p ! d))) \<Longrightarrow> ar_ok t \<Longrightarrow>
     cst (fst (tr_term_m p dm env n s t)) \<le> cst s + ucnt p n t\<close>
  \<open>(\<forall>d < n. ar_ok (SmtDef_body (SmtProblem_defs p ! d))) \<Longrightarrow> (\<forall>a \<in> set ts. ar_ok a) \<Longrightarrow>
     cst (fst (tr_args_m p dm env n s ts)) \<le> cst s + ucnt_args p n ts\<close>
proof (induction p dm env n s t and p dm env n s ts rule: tr_term_m_tr_args_m.induct)
  case (4 p dm env n s f args)
  define r where \<open>r = tr_args_m p dm env n s args\<close>
  define r2 where \<open>r2 = enc_terms_m (fst r) (snd r)\<close>
  have a: \<open>cst (fst r) \<le> cst s + ucnt_args p n args\<close> using 4 by (simp add: r_def)
  have b: \<open>cst (fst r2) \<le> cst (fst r) + 10 * length args \<and> length (snd r2) = length args\<close>
    using cst_enc_terms[of \<open>fst r\<close> \<open>snd r\<close>] tr_args_len by (simp add: r2_def r_def)
  show ?case using a b nw_ge[of \<open>length args\<close>] by (simp add: Let_def cst_add_term cst_add_atom flip: r_def r2_def)
next
  case (5 p dm env n s d args)
  show ?case
  proof (cases \<open>SmtDef_params (SmtProblem_defs p ! unat d) = []\<close>)
    case True
    then show ?thesis by simp
  next
    case F: False
    show ?thesis
    proof (cases \<open>unat d < n\<close>)
      case False
      then show ?thesis using F by simp
    next
      case True
      define r where \<open>r = tr_args_m p dm env n s args\<close>
      have a: \<open>cst (fst r) \<le> cst s + ucnt_args p n args\<close> using 5 F True by (simp add: r_def)
      have b: \<open>cst (fst (tr_term_m p dm (snd r) (unat d) (fst r) (SmtDef_body (SmtProblem_defs p ! unat d)))) \<le>
          cst (fst r) + ucnt p (unat d) (SmtDef_body (SmtProblem_defs p ! unat d))\<close>
        using 5 F True by (simp add: r_def)
      show ?thesis using a b F True by (simp add: Let_def flip: r_def)
    qed
  qed
next
  case (6 p dm env n s op args)
  define r where \<open>r = tr_args_m p dm env n s args\<close>
  have a: \<open>cst (fst r) \<le> cst s + ucnt_args p n args\<close> using 6 by (simp add: r_def)
  have l: \<open>length (snd r) = length args\<close> by (simp add: r_def tr_args_len)
  have ne: \<open>op = SmtOp_Ite \<longrightarrow> snd r \<noteq> []\<close> using 6(3) l by auto
  have c: \<open>cst (fst (enc_app_m (fst r) op (snd r))) \<le> cst (fst r) + nw (length args)\<close>
    using cst_enc_app[OF ne] l by simp
  show ?case using a c by (simp add: Let_def flip: r_def)
next
  case (8 p dm env n s a rest)
  define r1 where \<open>r1 = tr_term_m p dm env n s a\<close>
  have a: \<open>cst (fst r1) \<le> cst s + ucnt p n a\<close> using 8 by (simp add: r1_def)
  have b: \<open>cst (fst (tr_args_m p dm env n (fst r1) rest)) \<le> cst (fst r1) + ucnt_args p n rest\<close>
    using 8 by (simp add: r1_def)
  show ?case using a b by (simp add: Let_def flip: r1_def)
qed (simp_all add: nw_def)

subsection \<open>The translation of a problem\<close>

lemma cst_init: \<open>cst (tr_init_m p) = length (SmtProblem_funs p) + 8\<close>
  by (simp add: tr_init_m_def Let_def cst_def add_term_m_def add_atom_m_def add_clause_m_def)

lemma cst_defs_step:
  \<open>(\<forall>d' < d. ar_ok (SmtDef_body (SmtProblem_defs p ! d'))) \<Longrightarrow> ar_ok (SmtDef_body (SmtProblem_defs p ! d)) \<Longrightarrow>
   cst (fst (tr_defs_step p sd d)) \<le> cst (fst sd) +
     (if SmtDef_params (SmtProblem_defs p ! d) = [] then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)\<close>
  by (cases sd) (auto simp: tr_defs_step_def Let_def intro: tr_cst(1))

lemma cst_defs_fold:
  \<open>(\<forall>d < k. ar_ok (SmtDef_body (SmtProblem_defs p ! d))) \<Longrightarrow>
   cst (fst (foldl (tr_defs_step p) sd [0..<k])) \<le> cst (fst sd) + dsum p k\<close>
proof (induction k)
  case 0
  then show ?case by (simp add: dsum_0)
next
  case (Suc k)
  show ?case
    using Suc cst_defs_step[of k p \<open>foldl (tr_defs_step p) sd [0..<k]\<close>] by (simp add: dsum_Suc)
qed

lemma cst_asserts_fold:
  \<open>(\<forall>d < length (SmtProblem_defs p). ar_ok (SmtDef_body (SmtProblem_defs p ! d))) \<Longrightarrow> (\<forall>t \<in> set ts. ar_ok t) \<Longrightarrow>
   cst (foldl (tr_asserts_step p dm) s ts) \<le> cst s + sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) ts)\<close>
proof (induction ts arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have \<open>cst (tr_asserts_step p dm s t) \<le> cst s + (ucnt p (length (SmtProblem_defs p)) t + 2)\<close>
    using tr_cst(1)[of \<open>length (SmtProblem_defs p)\<close> p t dm \<open>[]\<close> s] Cons.prems
    by (simp add: tr_asserts_step_def Let_def cst_add_clause)
  then show ?case using Cons.IH[of \<open>tr_asserts_step p dm s t\<close>] Cons.prems by simp
qed

lemma wf_ar_ok:
  \<open>smt_wf p \<Longrightarrow> (\<forall>d < length (SmtProblem_defs p). ar_ok (SmtDef_body (SmtProblem_defs p ! d))) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). ar_ok t)\<close>
proof -
  assume w: \<open>smt_wf p\<close>
  have d: \<open>smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p)) (SmtDef_params (SmtProblem_defs p ! d))
      (SmtDef_body (SmtProblem_defs p ! d)) \<noteq> None\<close> if \<open>d < length (SmtProblem_defs p)\<close> for d
    using w that by (simp add: smt_wf_def Let_def)
  have a: \<open>smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] t \<noteq> None\<close> if \<open>t \<in> set (SmtProblem_asserts p)\<close> for t
    using w that by (simp add: smt_wf_def Let_def)
  show ?thesis using tsort_ar_ok[OF d] tsort_ar_ok[OF a] by blast
qed

text \<open>The total cost of the translation is at most \<^const>\<open>usize_m\<close> (minus 8).\<close>
theorem cst_tr_state: \<open>smt_wf p \<Longrightarrow> cst (tr_state_m p) + 8 \<le> usize_m p\<close>
proof -
  assume w: \<open>smt_wf p\<close>
  have D: \<open>cst (fst (tr_defs_m p)) \<le> length (SmtProblem_funs p) + 8 + dsum p (length (SmtProblem_defs p))\<close>
    using cst_defs_fold[of \<open>length (SmtProblem_defs p)\<close> p \<open>(tr_init_m p, [])\<close>] wf_ar_ok[OF w]
    by (simp add: tr_defs_m_def cst_init)
  have A: \<open>cst (tr_state_m p) \<le> cst (fst (tr_defs_m p)) +
      sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) (SmtProblem_asserts p))\<close>
    using cst_asserts_fold wf_ar_ok[OF w] by (simp add: tr_state_m_def tr_asserts_m_def)
  show ?thesis using D A by (simp add: usize_dsum)
qed

lemma le_sum_list_map: \<open>x \<in> set xs \<Longrightarrow> (f :: 'a \<Rightarrow> nat) x \<le> sum_list (map f xs)\<close>
  using member_le_sum_list[of \<open>f x\<close> \<open>map f xs\<close>] by simp

text \<open>Goal 1: a problem that passes the size check translates into a problem within the bounds of
  the correctness proof and of the core solver.\<close>
theorem usize_tr_ok:
  assumes \<open>usize_m p < 2 ^ 63\<close> \<open>smt_wf p\<close>
  shows \<open>tr_bounded p \<and> sizes_ok (tr_problem_m p)\<close>
proof -
  define s where \<open>s = tr_state_m p\<close>
  have c: \<open>cst s < 2 ^ 63\<close> using cst_tr_state[OF assms(2)] assms(1) by (simp add: s_def)
  have f: \<open>length (SmtProblem_funs p) < 2 ^ 63\<close> using assms(1) by (simp add: usize_m_def)
  have q: \<open>Problem_terms (tr_problem_m p) = st_terms s\<close> \<open>Problem_atoms (tr_problem_m p) = st_atoms s\<close>
    \<open>Problem_clauses (tr_problem_m p) = st_clauses s\<close> by (simp_all add: tr_problem_m_def s_def Let_def)
  have ta: \<open>length (Term_args t) < 2 ^ 63\<close> if \<open>t \<in> set (st_terms s)\<close> for t
    using le_sum_list_map[OF that, of \<open>\<lambda>t. length (Term_args t)\<close>] c by (simp add: cst_def)
  have cl: \<open>length (Clause_lits cl) < 2 ^ 63\<close> if \<open>cl \<in> set (st_clauses s)\<close> for cl
    using le_sum_list_map[OF that, of \<open>\<lambda>c. length (Clause_lits c)\<close>] c by (simp add: cst_def)
  show ?thesis using c f ta cl by (simp add: q tr_bounded_def sizes_ok_def cst_def)
qed

subsection \<open>The size measure of the specification bounds \<^const>\<open>usize_m\<close>\<close>

lemma nw_node: \<open>nw (length args) \<le> 16 * smt_node_weight fs ds ps t args\<close>
proof -
  have \<open>1 \<le> smt_wcube (smt_tsort fs ds ps t) ^ 3\<close> by (simp add: smt_wcube_def)
  then have \<open>Suc (length args) ^ 2 * 1 \<le> smt_node_weight fs ds ps t args\<close>
    unfolding smt_node_weight_def by (intro mult_le_mono2) simp
  then show ?thesis by (simp add: nw_def)
qed

lemma ucnt_weight:
  \<open>n \<le> length (SmtProblem_defs p) \<Longrightarrow>
     \<forall>ps. ucnt p n t \<le> 16 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t\<close>
  \<open>n \<le> length (SmtProblem_defs p) \<Longrightarrow>
     \<forall>ps. ucnt_args p n ts \<le> 16 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts)\<close>
proof (induction p n t and p n ts rule: ucnt_ucnt_args.induct)
  case (1 p n f args)
  show ?case
  proof
    fix ps
    have a: \<open>ucnt_args p n args \<le> 16 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) args)\<close>
      using 1 by blast
    show \<open>ucnt p n (SmtTerm_Fun f args) \<le> 16 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_Fun f args)\<close>
      using a nw_node[of args \<open>SmtProblem_funs p\<close> \<open>take n (SmtProblem_defs p)\<close> ps \<open>SmtTerm_Fun f args\<close>] by simp
  qed
next
  case (2 p n d args)
  show ?case
  proof
    fix ps
    define e where \<open>e = SmtProblem_defs p ! unat d\<close>
    have N: \<open>nw (length args) \<le> 16 * smt_node_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_Def d args) args\<close> by (rule nw_node)
    show \<open>ucnt p n (SmtTerm_Def d args) \<le> 16 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_Def d args)\<close>
    proof (cases \<open>SmtDef_params e = []\<close>)
      case True
      then show ?thesis using N by (simp add: e_def)
    next
      case F: False
      have a: \<open>ucnt_args p n args \<le> 16 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) args)\<close>
        using 2 F 2(3) by (simp add: e_def)
      show ?thesis
      proof (cases \<open>unat d < n\<close>)
        case False
        then show ?thesis using N a F by (simp add: e_def)
      next
        case True
        have b: \<open>ucnt p (unat d) (SmtDef_body e) \<le> 16 * smt_weight (SmtProblem_funs p) (take (unat d) (SmtProblem_defs p)) (SmtDef_params e) (SmtDef_body e)\<close>
          using 2 F True by (simp add: e_def)
        have t: \<open>unat d < length (take n (SmtProblem_defs p))\<close> \<open>take n (SmtProblem_defs p) ! unat d = e\<close> \<open>take (unat d) (take n (SmtProblem_defs p)) = take (unat d) (SmtProblem_defs p)\<close>
          using True 2(3) by (simp_all add: e_def min_def)
        show ?thesis using N a b F True t 2(3) by (simp add: e_def)
      qed
    qed
  qed
next
  case (3 p n op args)
  show ?case
  proof
    fix ps
    have a: \<open>ucnt_args p n args \<le> 16 * sum_list (map (smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) args)\<close>
      using 3 by blast
    show \<open>ucnt p n (SmtTerm_App op args) \<le> 16 * smt_weight (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps (SmtTerm_App op args)\<close>
      using a nw_node[of args \<open>SmtProblem_funs p\<close> \<open>take n (SmtProblem_defs p)\<close> ps \<open>SmtTerm_App op args\<close>] by simp
  qed
qed (use nw_node[of \<open>[]\<close>] in \<open>auto intro: add_mono trans_le_add1\<close>)

text \<open>Goal 2: a problem of the fragment with \<^const>\<open>smt_sizes_ok\<close> passes the size check.\<close>
theorem sizes_ok_usize: \<open>smt_sizes_ok p \<Longrightarrow> usize_m p < 2 ^ 63\<close>
proof -
  assume ok: \<open>smt_sizes_ok p\<close>
  define WD where \<open>WD = sum_list (map (\<lambda>d. if SmtDef_params ((SmtProblem_defs p) ! d) = [] then smt_weight (SmtProblem_funs p) (take d (SmtProblem_defs p)) [] (SmtDef_body ((SmtProblem_defs p) ! d)) else 0)
                   [0..<length (SmtProblem_defs p)])\<close>
  define WA where \<open>WA = sum_list (map (smt_weight (SmtProblem_funs p) (SmtProblem_defs p) []) (SmtProblem_asserts p))\<close>
  define X where \<open>X = 1 + length (SmtProblem_funs p) + length (SmtProblem_defs p) + length (SmtProblem_asserts p) + sum_list (map (\<lambda>f. smt_width (SmtFun_ret f) + 1) (SmtProblem_funs p)) + WD + WA\<close>
  have B: \<open>smt_size_bound p = 1000000000 * X\<close> by (simp add: smt_size_bound_def Let_def X_def WD_def WA_def)
  have D: \<open>sum_list (map (\<lambda>d. if SmtDef_params ((SmtProblem_defs p) ! d) = [] then ucnt p d (SmtDef_body ((SmtProblem_defs p) ! d)) else 0) [0..<length (SmtProblem_defs p)]) \<le> 16 * WD\<close>
  proof -
    have \<open>sum_list (map (\<lambda>d. if SmtDef_params ((SmtProblem_defs p) ! d) = [] then ucnt p d (SmtDef_body ((SmtProblem_defs p) ! d)) else 0) [0..<length (SmtProblem_defs p)]) \<le>
          sum_list (map (\<lambda>d. 16 * (if SmtDef_params ((SmtProblem_defs p) ! d) = [] then smt_weight (SmtProblem_funs p) (take d (SmtProblem_defs p)) [] (SmtDef_body ((SmtProblem_defs p) ! d)) else 0)) [0..<length (SmtProblem_defs p)])\<close>
      by (rule sum_list_mono) (use ucnt_weight(1) in \<open>auto\<close>)
    then show ?thesis by (simp add: WD_def sum_list_const_mult)
  qed
  have A: \<open>sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) ts) \<le> 16 * sum_list (map (smt_weight (SmtProblem_funs p) (SmtProblem_defs p) []) ts) + 2 * length ts\<close> for ts
  proof (induction ts)
    case Nil
    then show ?case by simp
  next
    case (Cons t ts)
    have \<open>ucnt p (length (SmtProblem_defs p)) t \<le> 16 * smt_weight (SmtProblem_funs p) (SmtProblem_defs p) [] t\<close>
      using ucnt_weight(1)[of \<open>length (SmtProblem_defs p)\<close> p t] by simp
    then show ?case using Cons by simp
  qed
  have U: \<open>usize_m p \<le> 16 * X\<close>
    using D A[of \<open>SmtProblem_asserts p\<close>] by (simp add: usize_m_def X_def WA_def)
  show ?thesis using U ok B by (simp add: smt_sizes_ok_def)
qed

end
