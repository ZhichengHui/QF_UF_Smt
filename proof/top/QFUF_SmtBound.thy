theory QFUF_SmtBound
  imports QFUF_SmtSize
begin

section \<open>The size check bounds the translation\<close>

subsection \<open>A bound on the size of the translation\<close>

text \<open>The weight of a node with \<open>k\<close> arguments (\<^verbatim>\<open>node_weight\<close>).\<close>
definition nw :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nw k \<equiv> 16 * (k + 1) ^ 2\<close>

lemma nw_sat: \<open>sat (16 * sat (sat (Suc x) * sat (Suc x))) = sat (nw x)\<close>
proof -
  have a: \<open>sat (sat (Suc x) * sat (Suc x)) = sat ((Suc x) * (Suc x))\<close> by (rule sat_mul_sat)
  have \<open>sat (16 * sat (sat (Suc x) * sat (Suc x))) = sat (sat 16 * sat (sat (Suc x) * sat (Suc x)))\<close>
    by (simp only: sat_16)
  also have \<open>\<dots> = sat (sat 16 * sat ((Suc x) * (Suc x)))\<close> by (simp only: a)
  also have \<open>\<dots> = sat (16 * ((Suc x) * (Suc x)))\<close> by (rule sat_mul_sat)
  finally show ?thesis by (simp add: nw_def power2_eq_square)
qed

text \<open>\<^verbatim>\<open>uf_count\<close> and \<^verbatim>\<open>uf_count_args\<close> without saturation, with the definitions below \<open>n\<close>
  expanded (as \<^const>\<open>tr_term_m\<close>). As in Rust, an application of a definition without
  parameters counts only its node, and one of a definition with parameters its node, its arguments
  and the body of the definition.\<close>
function (sequential) ucnt :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and ucnt_args :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>ucnt p n (SmtTerm_Fun f args) = nw (length args) + ucnt_args p n args\<close>
| \<open>ucnt p n (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then nw (length args)
      else nw (length args) + (ucnt_args p n args +
             (if unat d < n then ucnt p (unat d) (SmtDef_body (SmtProblem_defs p ! unat d)) else 0)))\<close>
| \<open>ucnt p n (SmtTerm_App op args) = nw (length args) + ucnt_args p n args\<close>
| \<open>ucnt p n _ = nw 0\<close>
| \<open>ucnt_args p n [] = 0\<close>
| \<open>ucnt_args p n (a # rest) = ucnt p n a + ucnt_args p n rest\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, n, _) \<Rightarrow> n | Inr (_, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, t) \<Rightarrow> size t | Inr (_, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

text \<open>The value \<^verbatim>\<open>uf_size\<close> computes, without saturation: 16, the number of declared symbols,
  the counts of the bodies of the definitions without parameters, and the counts plus 2 of the
  assertions.\<close>
definition usize_m :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>usize_m p \<equiv>
     16 + length (SmtProblem_funs p) +
     sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                         then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)
                [0..<length (SmtProblem_defs p)]) +
     sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) (SmtProblem_asserts p))\<close>

text \<open>The definitions part of \<^const>\<open>usize_m\<close> for the first \<open>d\<close> definitions.\<close>
definition dsum :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dsum p d \<equiv> sum_list (map (\<lambda>i. if SmtDef_params (SmtProblem_defs p ! i) = []
                                   then ucnt p i (SmtDef_body (SmtProblem_defs p ! i)) else 0) [0..<d])\<close>

lemma dsum_0: \<open>dsum p 0 = 0\<close>
  by (simp add: dsum_def)

lemma dsum_Suc: \<open>dsum p (Suc d) = dsum p d +
  (if SmtDef_params (SmtProblem_defs p ! d) = [] then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)\<close>
  by (simp add: dsum_def)

lemma usize_dsum: \<open>usize_m p = 16 + length (SmtProblem_funs p) + dsum p (length (SmtProblem_defs p)) +
  sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) (SmtProblem_asserts p))\<close>
  by (simp add: usize_m_def dsum_def)

lemma ucnt_args_sum: \<open>ucnt_args p n ts = sum_list (map (ucnt p n) ts)\<close>
  by (induction ts) auto


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

subsection \<open>The input range bounds \<^const>\<open>usize_m\<close>\<close>

text \<open>The count \<^const>\<open>ucnt\<close> of a term is at most \<open>32\<close> times the square of its number of nodes
  \<^const>\<open>ncnt\<close>: a node with \<open>k\<close> arguments costs \<open>16 (k + 1)^2\<close>, and its arguments have at least
  \<open>k\<close> nodes.\<close>

lemma ncnt_pos: \<open>1 \<le> ncnt p n t\<close>
  by (cases t) simp_all

lemma sum_ge_length: \<open>(\<forall>x \<in> set xs. 1 \<le> (f x :: nat)) \<Longrightarrow> length xs \<le> sum_list (map f xs)\<close>
  by (induction xs) fastforce+

lemma sum_sq_le: \<open>(\<forall>x \<in> set xs. 1 \<le> (f x :: nat)) \<Longrightarrow>
  sum_list (map (\<lambda>x. f x ^ 2) xs) + length xs * (length xs - 1) \<le> (sum_list (map f xs)) ^ 2\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  define y where \<open>y = f a\<close>
  define X where \<open>X = sum_list (map f xs)\<close>
  define k where \<open>k = length xs\<close>
  have y: \<open>1 \<le> y\<close> using Cons.prems by (simp add: y_def)
  have kX: \<open>k \<le> X\<close> using sum_ge_length[of xs f] Cons.prems by (simp add: k_def X_def)
  have IH: \<open>sum_list (map (\<lambda>x. f x ^ 2) xs) + k * (k - 1) \<le> X ^ 2\<close>
    using Cons by (simp add: k_def X_def)
  have \<open>2 * k \<le> 2 * y * X\<close> using y kX by (metis mult_le_mono mult_le_mono2 nat_mult_1 mult.assoc)
  moreover have \<open>Suc k * k = k * (k - 1) + 2 * k\<close> by (cases k) (simp_all add: algebra_simps)
  ultimately show ?case using IH
    by (simp add: y_def[symmetric] X_def[symmetric] k_def[symmetric] power2_eq_square algebra_simps)
qed

lemma sum_sq_le_sq: \<open>sum_list (map (\<lambda>x. (f x :: nat) ^ 2) xs) \<le> (sum_list (map f xs)) ^ 2\<close>
proof (induction xs)
  case (Cons a xs)
  then show ?case by (simp add: power2_eq_square algebra_simps add_mono trans_le_add1)
qed simp

lemma node_arith: \<open>k \<le> X \<Longrightarrow> s + k * (k - 1) \<le> X ^ 2 \<Longrightarrow> nw k + 32 * s \<le> 32 * (1 + X) ^ 2\<close>
proof -
  assume kX: \<open>k \<le> X\<close> and s: \<open>s + k * (k - 1) \<le> X ^ 2\<close>
  have a: \<open>16 * (k + 1) ^ 2 \<le> 32 * (k * (k - 1)) + 32 + 64 * X\<close>
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have \<open>64 * Suc j \<le> 64 * X\<close> using kX Suc by simp
    then show ?thesis using Suc by (simp add: power2_eq_square algebra_simps)
  qed
  have b: \<open>32 * s + 32 * (k * (k - 1)) \<le> 32 * X ^ 2\<close> using s by simp
  have c: \<open>32 * (1 + X) ^ 2 = 32 + 64 * X + 32 * X ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
  show ?thesis using a b c by (simp add: nw_def)
qed

lemma ucnt_sq:
  \<open>ucnt p n t \<le> 32 * (ncnt p n t) ^ 2\<close>
  \<open>ucnt_args p n ts \<le> 32 * sum_list (map (\<lambda>a. (ncnt p n a) ^ 2) ts)\<close>
proof (induction p n t and p n ts rule: ucnt_ucnt_args.induct)
  case (1 p n f args)
  define X where \<open>X = ncnt_args p n args\<close>
  define s where \<open>s = sum_list (map (\<lambda>a. (ncnt p n a) ^ 2) args)\<close>
  have pos: \<open>\<forall>a \<in> set args. 1 \<le> ncnt p n a\<close> using ncnt_pos by blast
  have X: \<open>X = sum_list (map (ncnt p n) args)\<close> by (simp add: X_def ncnt_args_sum)
  have kX: \<open>length args \<le> X\<close> using sum_ge_length[OF pos] X by simp
  have sq: \<open>s + length args * (length args - 1) \<le> X ^ 2\<close> using sum_sq_le[OF pos] X by (simp add: s_def)
  have \<open>nw (length args) + 32 * s \<le> 32 * (1 + X) ^ 2\<close> by (rule node_arith[OF kX sq])
  then show ?case using 1 by (simp add: X_def s_def)
next
  case (2 p n d args)
  define X where \<open>X = ncnt_args p n args\<close>
  define s where \<open>s = sum_list (map (\<lambda>a. (ncnt p n a) ^ 2) args)\<close>
  define e where \<open>e = SmtProblem_defs p ! unat d\<close>
  have pos: \<open>\<forall>a \<in> set args. 1 \<le> ncnt p n a\<close> using ncnt_pos by blast
  have X: \<open>X = sum_list (map (ncnt p n) args)\<close> by (simp add: X_def ncnt_args_sum)
  have kX: \<open>length args \<le> X\<close> using sum_ge_length[OF pos] X by simp
  have sq: \<open>s + length args * (length args - 1) \<le> X ^ 2\<close> using sum_sq_le[OF pos] X by (simp add: s_def)
  have N: \<open>nw (length args) + 32 * s \<le> 32 * (1 + X) ^ 2\<close> by (rule node_arith[OF kX sq])
  show ?case
  proof (cases \<open>SmtDef_params e = []\<close>)
    case True
    have \<open>nw (length args) \<le> 32 * (1 + X) ^ 2\<close> using N by simp
    then show ?thesis using True by (simp add: e_def X_def)
  next
    case F: False
    have a: \<open>ucnt_args p n args \<le> 32 * s\<close> using 2 F by (simp add: e_def s_def)
    define B where \<open>B = (if unat d < n then ncnt p (unat d) (SmtDef_body e) else 0)\<close>
    define U where \<open>U = (if unat d < n then ucnt p (unat d) (SmtDef_body e) else 0)\<close>
    have b: \<open>U \<le> 32 * B ^ 2\<close> using 2 F by (simp add: U_def B_def e_def)
    have c: \<open>32 * (1 + X) ^ 2 + 32 * B ^ 2 \<le> 32 * (1 + (X + B)) ^ 2\<close>
      by (simp add: power2_eq_square algebra_simps)
    have \<open>nw (length args) + (ucnt_args p n args + U) \<le> 32 * (1 + (X + B)) ^ 2\<close>
      using N a b c by linarith
    then show ?thesis using F by (auto simp: e_def[symmetric] X_def[symmetric] U_def B_def split: if_splits)
  qed
next
  case (3 p n op args)
  define X where \<open>X = ncnt_args p n args\<close>
  define s where \<open>s = sum_list (map (\<lambda>a. (ncnt p n a) ^ 2) args)\<close>
  have pos: \<open>\<forall>a \<in> set args. 1 \<le> ncnt p n a\<close> using ncnt_pos by blast
  have X: \<open>X = sum_list (map (ncnt p n) args)\<close> by (simp add: X_def ncnt_args_sum)
  have kX: \<open>length args \<le> X\<close> using sum_ge_length[OF pos] X by simp
  have sq: \<open>s + length args * (length args - 1) \<le> X ^ 2\<close> using sum_sq_le[OF pos] X by (simp add: s_def)
  have \<open>nw (length args) + 32 * s \<le> 32 * (1 + X) ^ 2\<close> by (rule node_arith[OF kX sq])
  then show ?case using 3 by (simp add: X_def s_def)
qed (simp_all add: nw_def)

text \<open>Goal 2: a problem of the input range passes the bounds of the translation.\<close>
theorem in_range_usize:
  assumes \<open>smt_size p \<le> 2 ^ 28\<close>
  shows \<open>usize_m p < 2 ^ 63\<close>
proof -
  define L where \<open>L = length (SmtProblem_defs p)\<close>
  define fd where \<open>fd = (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = [] then ncnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)\<close>
  define ud where \<open>ud = (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = [] then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)\<close>
  define ID where \<open>ID = sum_list (map fd [0..<L])\<close>
  define IA where \<open>IA = sum_list (map (ncnt p L) (SmtProblem_asserts p))\<close>
  define S where \<open>S = smt_size p\<close>
  have S: \<open>S = length (SmtProblem_funs p) + L + length (SmtProblem_asserts p) + ID + IA\<close>
    using isize_smt_size[of p] by (simp add: S_def isize_m_def ID_def IA_def fd_def L_def)
  have ud: \<open>ud d \<le> 32 * (fd d) ^ 2\<close> for d by (simp add: ud_def fd_def ucnt_sq(1))
  have D: \<open>sum_list (map ud [0..<L]) \<le> 32 * ID ^ 2\<close>
  proof -
    have \<open>sum_list (map ud [0..<L]) \<le> sum_list (map (\<lambda>d. 32 * (fd d) ^ 2) [0..<L])\<close>
      by (rule sum_list_mono) (rule ud)
    also have \<open>\<dots> = 32 * sum_list (map (\<lambda>d. (fd d) ^ 2) [0..<L])\<close> by (simp add: sum_list_const_mult)
    also have \<open>\<dots> \<le> 32 * ID ^ 2\<close> using sum_sq_le_sq[of fd \<open>[0..<L]\<close>] by (simp add: ID_def)
    finally show ?thesis .
  qed
  have A1: \<open>sum_list (map (\<lambda>t. ucnt p L t + 2) ts) \<le> sum_list (map (\<lambda>t. 32 * (ncnt p L t) ^ 2) ts) + 2 * length ts\<close> for ts
  proof (induction ts)
    case (Cons a ts)
    have \<open>ucnt p L a \<le> 32 * (ncnt p L a) ^ 2\<close> by (rule ucnt_sq(1))
    then show ?case using Cons.IH by simp
  qed simp
  have A2: \<open>sum_list (map (\<lambda>t. 32 * (ncnt p L t) ^ 2) ts) \<le> 32 * (sum_list (map (ncnt p L) ts)) ^ 2\<close> for ts
    using sum_sq_le_sq[of \<open>ncnt p L\<close> ts] by (simp add: sum_list_const_mult)
  have A: \<open>sum_list (map (\<lambda>t. ucnt p L t + 2) (SmtProblem_asserts p)) \<le> 32 * IA ^ 2 + 2 * length (SmtProblem_asserts p)\<close>
    using A1[of \<open>SmtProblem_asserts p\<close>] A2[of \<open>SmtProblem_asserts p\<close>] by (simp add: IA_def)
  have U: \<open>usize_m p \<le> 16 + length (SmtProblem_funs p) + 32 * ID ^ 2 + 32 * IA ^ 2 + 2 * length (SmtProblem_asserts p)\<close>
    using D A by (simp add: usize_m_def ud_def L_def)
  have sq1: \<open>ID ^ 2 + IA ^ 2 \<le> (ID + IA) ^ 2\<close> by (simp add: power2_eq_square algebra_simps)
  have sq2: \<open>(ID + IA) ^ 2 \<le> S ^ 2\<close> using S by (intro power_mono) simp_all
  have S28: \<open>S \<le> 2 ^ 28\<close> using assms by (simp add: S_def)
  have S56: \<open>S ^ 2 \<le> 2 ^ 56\<close> using power_mono[OF S28, of 2] by (simp add: power_mult[symmetric])
  have \<open>usize_m p \<le> 16 + 3 * S + 32 * S ^ 2\<close> using U sq1 sq2 S by linarith
  moreover have \<open>16 + 3 * S + 32 * S ^ 2 \<le> 16 + 3 * 2 ^ 28 + 32 * 2 ^ 56\<close> using S28 S56 by linarith
  ultimately show ?thesis by simp
qed

end
