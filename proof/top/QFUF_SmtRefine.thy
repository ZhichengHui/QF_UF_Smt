theory QFUF_SmtRefine
  imports "QFUF_Smt.QFUF_SmtModel"
begin

section \<open>The Rust functions of the translation compute their models\<close>

subsection \<open>Rust values and model values\<close>

text \<open>The model state of a Rust state, and the Rust state of a model state.\<close>
definition st_of :: \<open>Tr \<Rightarrow> st\<close> where
  \<open>st_of s \<equiv> St (Tr_terms s) (Tr_atoms s) (Tr_clauses s) (unat (Tr_next_fun s))\<close>

definition tr_of :: \<open>st \<Rightarrow> Tr\<close> where
  \<open>tr_of S \<equiv> make_Tr (st_terms S) (st_atoms S) (st_clauses S) (word_of_nat (st_next S))\<close>

fun encm :: \<open>Enc \<Rightarrow> enc_m\<close> where
  \<open>encm (Enc_Term i) = ETerm (unat i)\<close>
| \<open>encm (Enc_Lit a pos) = ELit (unat a) pos\<close>

fun enc_of :: \<open>enc_m \<Rightarrow> Enc\<close> where
  \<open>enc_of (ETerm i) = Enc_Term (word_of_nat i)\<close>
| \<open>enc_of (ELit a pos) = Enc_Lit (word_of_nat a) pos\<close>

text \<open>The indices of an encoding are below \<open>2^64\<close>.\<close>
fun ib :: \<open>enc_m \<Rightarrow> bool\<close> where
  \<open>ib (ETerm i) = (i < 2 ^ 64)\<close>
| \<open>ib (ELit a pos) = (a < 2 ^ 64)\<close>

definition lw :: \<open>nat \<times> bool \<Rightarrow> 64 word \<times> bool \<times> tnil\<close> where
  \<open>lw l \<equiv> (word_of_nat (fst l), snd l, TNil)\<close>

definition lm :: \<open>64 word \<times> bool \<times> tnil \<Rightarrow> nat \<times> bool\<close> where
  \<open>lm l \<equiv> (unat (fst l), fst (snd l))\<close>

lemma st_tr_of: \<open>st_next S < 2 ^ 64 \<Longrightarrow> st_of (tr_of S) = S\<close>
  by (cases S) (simp add: st_of_def tr_of_def unat_of_nat_eq)

lemma tr_st_of: \<open>tr_of (st_of s) = s\<close>
  by (cases s) (simp add: st_of_def tr_of_def)

lemma encm_enc_of: \<open>ib e \<Longrightarrow> encm (enc_of e) = e\<close>
  by (cases e) (simp_all add: unat_of_nat_eq)

lemma enc_of_encm: \<open>enc_of (encm e) = e\<close>
  by (cases e) simp_all

lemma ib_encm: \<open>ib (encm e)\<close>
  by (cases e) (simp_all add: unat_lt2p[where 'a=64, simplified])

lemma lm_lw: \<open>fst l < 2 ^ 64 \<Longrightarrow> lm (lw l) = l\<close>
  by (simp add: lm_def lw_def unat_of_nat_eq)

lemma ib_map_encm: \<open>\<forall>e \<in> set (map encm es). ib e\<close>
  by (simp add: ib_encm)

lemma map_encm_enc_of: \<open>\<forall>e \<in> set es. ib e \<Longrightarrow> map encm (map enc_of es) = es\<close>
  by (induction es) (simp_all add: encm_enc_of)

lemma map_enc_of_encm: \<open>map enc_of (map encm es) = es\<close>
  by (induction es) (simp_all add: enc_of_encm)

lemma wn_unat: \<open>(word_of_nat (unat (w :: 64 word)) :: 64 word) = w\<close>
  by simp

lemma wn_unat_wn: \<open>(word_of_nat (unat (word_of_nat a :: 64 word)) :: 64 word) = word_of_nat a\<close>
  by simp

subsection \<open>The precondition of the recursion\<close>

text \<open>The least number of arguments with which \<^verbatim>\<open>enc_app\<close> does not panic.\<close>
fun min_ar :: \<open>SmtOp \<Rightarrow> nat\<close> where
  \<open>min_ar SmtOp_Not = 1\<close>
| \<open>min_ar SmtOp_Xor = 1\<close>
| \<open>min_ar SmtOp_Ite = 3\<close>
| \<open>min_ar _ = 0\<close>

text \<open>\<open>tok p F dl el n t\<close>: what \<^verbatim>\<open>enc\<close> needs not to panic and to compute \<^const>\<open>tr_term_m\<close> with
  the bound \<open>n\<close>, for \<open>dl\<close> entries of \<^verbatim>\<open>dm\<close> and \<open>el\<close> of \<^verbatim>\<open>env\<close>: indices in bounds, a
  definition with parameters expanded only below \<open>n\<close>, enough arguments for each theory function,
  and every argument list shorter than \<open>2^64\<close>, with at most \<open>F\<close> (the loop fuel) elements and
  pairs of elements.\<close>
function (sequential) tok :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> bool\<close>
  and toks :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> bool\<close>
  where
  \<open>tok p F dl el n (SmtTerm_Param k) = (unat k < el)\<close>
| \<open>tok p F dl el n (SmtTerm_Fun f args) =
     (unat f < length (SmtProblem_funs p) \<and> length args < 2 ^ 64 \<and> length args \<le> F \<and> toks p F dl el n args)\<close>
| \<open>tok p F dl el n (SmtTerm_Def d args) =
     (unat d < length (SmtProblem_defs p) \<and> length (SmtDef_params (SmtProblem_defs p ! unat d)) < 2 ^ 64 \<and>
      (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then unat d < dl
       else if unat d < n then length args < 2 ^ 64 \<and> length args \<le> F \<and> toks p F dl el n args \<and>
            tok p F dl (length args) (unat d) (SmtDef_body (SmtProblem_defs p ! unat d))
       else False))\<close>
| \<open>tok p F dl el n (SmtTerm_App op args) =
     (length args < 2 ^ 64 \<and> length args \<le> F \<and> length args * length args \<le> F \<and> min_ar op \<le> length args \<and>
      toks p F dl el n args)\<close>
| \<open>tok p F dl el n _ = True\<close>
| \<open>toks p F dl el n [] = True\<close>
| \<open>toks p F dl el n (a # rest) = (tok p F dl el n a \<and> toks p F dl el n rest)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, _, _, _, n, _) \<Rightarrow> n | Inr (_, _, _, _, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, _, _, _, t) \<Rightarrow> size t | Inr (_, _, _, _, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

text \<open>The depth of the recursion of \<^verbatim>\<open>enc\<close> and \<^verbatim>\<open>enc_args\<close>.\<close>
function (sequential) dep :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and deps :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>dep p n (SmtTerm_Fun f args) = Suc (deps p n args)\<close>
| \<open>dep p n (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then 0
      else if unat d < n then Suc (max (deps p n args) (dep p (unat d) (SmtDef_body (SmtProblem_defs p ! unat d))))
      else 0)\<close>
| \<open>dep p n (SmtTerm_App op args) = Suc (deps p n args)\<close>
| \<open>dep p n _ = 0\<close>
| \<open>deps p n [] = 0\<close>
| \<open>deps p n (a # rest) = max (Suc (dep p n a)) (deps p n rest)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, n, _) \<Rightarrow> n | Inr (_, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, t) \<Rightarrow> size t | Inr (_, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

lemma toks_iff: \<open>toks p F dl el n ts = (\<forall>a \<in> set ts. tok p F dl el n a)\<close>
  by (induction ts) auto

lemma deps_ge: \<open>a \<in> set ts \<Longrightarrow> Suc (dep p n a) \<le> deps p n ts\<close>
  by (induction ts) auto

lemma deps_nth: \<open>deps p n ts \<le> k \<Longrightarrow> i < length ts \<Longrightarrow> Suc (dep p n (ts ! i)) \<le> k\<close>
  using deps_ge[of \<open>ts ! i\<close> ts p n] by simp

lemma toks_nth: \<open>toks p F dl el n ts \<Longrightarrow> i < length ts \<Longrightarrow> tok p F dl el n (ts ! i)\<close>
  by (simp add: toks_iff)

text \<open>The bound \<open>n\<close> does not matter once the expanded definitions are below it.\<close>
lemma tok_n_indep:
  \<open>tok p F dl el n t \<Longrightarrow> n \<le> n' \<Longrightarrow>
     tok p F dl el n' t \<and> dep p n' t = dep p n t \<and> tr_term_m p dm env n' S t = tr_term_m p dm env n S t\<close>
  \<open>toks p F dl el n ts \<Longrightarrow> n \<le> n' \<Longrightarrow>
     toks p F dl el n' ts \<and> deps p n' ts = deps p n ts \<and> tr_args_m p dm env n' S ts = tr_args_m p dm env n S ts\<close>
proof (induction p F dl el n t and p F dl el n ts arbitrary: env S n' and env S n' rule: tok_toks.induct)
  case (2 p F dl el n f args)
  have a: \<open>toks p F dl el n args\<close> using 2(2) by simp
  show ?case using 2(1)[OF a 2(3)] 2(2) by (simp add: Let_def)
next
  case (3 p F dl el n d args)
  show ?case
  proof (cases \<open>SmtDef_params (SmtProblem_defs p ! unat d) = []\<close>)
    case True
    then show ?thesis using 3(3) by simp
  next
    case False
    have a: \<open>unat d < n\<close> \<open>toks p F dl el n args\<close> using 3(3) False by (auto split: if_splits)
    note I = 3(1)[OF False a(1) a(2) 3(4)]
    show ?thesis using I 3(3) 3(4) False a by (auto simp: Let_def split: if_splits)
  qed
next
  case (4 p F dl el n op args)
  have a: \<open>toks p F dl el n args\<close> using 4(2) by simp
  show ?case using 4(1)[OF a 4(3)] 4(2) by (simp add: Let_def)
next
  case (7 p F dl el n a rest)
  have t: \<open>tok p F dl el n a\<close> \<open>toks p F dl el n rest\<close> using 7(3) by simp_all
  show ?case using 7(1)[OF t(1) 7(4)] 7(2)[OF t(2) 7(4)] by (simp add: Let_def)
qed simp_all

subsection \<open>The indices of the translated terms are below \<open>2^64\<close>\<close>

lemma xor_fold_idx:
  \<open>fst (snd (foldl xor_step_m sa es)) = fst (snd sa) \<or>
   fst (snd (foldl xor_step_m sa es)) < length (st_atoms (fst (foldl xor_step_m sa es)))\<close>
proof (induction es arbitrary: sa)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain s a pa where sa: \<open>sa = (s, (a, pa))\<close> by (cases sa) auto
  obtain b pb where l: \<open>enc_lit_m e = (b, pb)\<close> by (cases \<open>enc_lit_m e\<close>)
  let ?s1 = \<open>xor_step_m sa e\<close>
  have s1: \<open>?s1 = gate_xor_m s (a, pa) (b, pb)\<close> by (simp add: sa l xor_step_m_def)
  have p: \<open>pre (fst ?s1) (fst (foldl xor_step_m ?s1 es))\<close> using pre_xor_fold[OF pre_refl] .
  have \<open>fst (snd ?s1) < length (st_atoms (fst ?s1))\<close> by (simp add: s1 gate_xor_eq)
  then have \<open>fst (snd ?s1) < length (st_atoms (fst (foldl xor_step_m ?s1 es)))\<close>
    using pre_len[OF p] by linarith
  then show ?case using Cons.IH[of ?s1] by auto
qed

lemma len_atoms_gate_andor: \<open>length (st_atoms (fst (gate_andor_m s ls cj))) = Suc (length (st_atoms s))\<close>
  by (simp add: gate_andor_eq)

lemma enc_app_ib:
  assumes \<open>\<forall>e \<in> set es. ib e\<close> \<open>min_ar op \<le> length es\<close> \<open>bnd (fst (enc_app_m s op es))\<close>
  shows \<open>ib (snd (enc_app_m s op es))\<close>
proof (cases op)
  case SmtOp_Not
  have \<open>es ! 0 \<in> set es\<close> using assms(2) SmtOp_Not by (intro nth_mem) auto
  then have \<open>ib (es ! 0)\<close> using assms(1) by blast
  then show ?thesis using SmtOp_Not by (cases \<open>es ! 0\<close>) simp_all
next
  case SmtOp_Xor
  let ?X = \<open>foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es)\<close>
  have \<open>es ! 0 \<in> set es\<close> using assms(2) SmtOp_Xor by (intro nth_mem) auto
  then have \<open>ib (es ! 0)\<close> using assms(1) by blast
  then have i0: \<open>fst (enc_lit_m (es ! 0)) < 2 ^ 64\<close> by (cases \<open>es ! 0\<close>) auto
  have b: \<open>length (st_atoms (fst ?X)) < 2 ^ 64\<close> using assms(3) SmtOp_Xor by (simp add: Let_def bnd_def)
  show ?thesis using xor_fold_idx[of \<open>(s, enc_lit_m (es ! 0))\<close> \<open>tl es\<close>] i0 b SmtOp_Xor by (auto simp: Let_def)
next
  case SmtOp_Ite
  show ?thesis
  proof (cases \<open>is_lit_m (es ! 1)\<close>)
    case True
    obtain c pc a pa b pb where l: \<open>enc_lit_m (es ! 0) = (c, pc)\<close> \<open>enc_lit_m (es ! 1) = (a, pa)\<close> \<open>enc_lit_m (es ! 2) = (b, pb)\<close>
      by (metis prod.exhaust)
    show ?thesis using assms(3) SmtOp_Ite True l by (simp add: gate_ite_eq bnd_def)
  next
    case False
    let ?r = \<open>new_const_m s\<close>
    have e: \<open>enc_app_m s op es = ite_term_m s es\<close> using SmtOp_Ite False by simp
    have p: \<open>pre (fst ?r) (fst (ite_term_m s es))\<close>
      unfolding ite_term_m_def Let_def
      by (simp, intro pre_add_clause pre_add_atom pre_enc_term pre_refl)
    have \<open>snd (ite_term_m s es) = ETerm (length (st_terms s))\<close> by (simp add: ite_term_m_def Let_def new_const_eq)
    moreover have \<open>Suc (length (st_terms s)) \<le> length (st_terms (fst (ite_term_m s es)))\<close>
      using pre_len[OF p] by (simp add: new_const_eq)
    ultimately show ?thesis using assms(3) e by (simp add: bnd_def)
  qed
qed (use assms(3) in \<open>simp_all add: gate_andor_eq enc_eq_m_def Let_def bnd_def\<close>)

lemma tr_ib:
  \<open>tok p F dl el n t \<Longrightarrow> length env = el \<Longrightarrow> (\<forall>e \<in> set env. ib e) \<Longrightarrow> dl \<le> length dm \<Longrightarrow> (\<forall>e \<in> set dm. ib e) \<Longrightarrow>
     bnd (fst (tr_term_m p dm env n S t)) \<Longrightarrow> ib (snd (tr_term_m p dm env n S t))\<close>
  \<open>toks p F dl el n ts \<Longrightarrow> length env = el \<Longrightarrow> (\<forall>e \<in> set env. ib e) \<Longrightarrow> dl \<le> length dm \<Longrightarrow> (\<forall>e \<in> set dm. ib e) \<Longrightarrow>
     bnd (fst (tr_args_m p dm env n S ts)) \<Longrightarrow> (\<forall>e \<in> set (snd (tr_args_m p dm env n S ts)). ib e)\<close>
proof (induction p F dl el n t and p F dl el n ts arbitrary: env S and env S rule: tok_toks.induct)
  case (1 p F dl el n k)
  then show ?case by simp
next
  case (2 p F dl el n f args)
  then show ?case by (auto simp: Let_def add_term_m_def add_atom_m_def bnd_def)
next
  case (3 p F dl el n d args)
  let ?D = \<open>SmtProblem_defs p ! unat d\<close>
  show ?case
  proof (cases \<open>SmtDef_params ?D = []\<close>)
    case True
    then have \<open>unat d < length dm\<close> using 3(3,6) by simp
    then show ?thesis using True 3(7) by simp
  next
    case False
    have a: \<open>unat d < n\<close> \<open>toks p F dl el n args\<close> \<open>tok p F dl (length args) (unat d) (SmtDef_body ?D)\<close>
      using 3(3) False by (auto split: if_splits)
    obtain s1 es1 where r: \<open>tr_args_m p dm env n S args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n S args\<close>)
    have l: \<open>length es1 = length args\<close> using tr_pre(2)[OF r] by simp
    have e: \<open>tr_term_m p dm env n S (SmtTerm_Def d args) = tr_term_m p dm es1 (unat d) s1 (SmtDef_body ?D)\<close>
      using False a(1) r by simp
    have pb: \<open>pre s1 (fst (tr_term_m p dm es1 (unat d) s1 (SmtDef_body ?D)))\<close>
      using tr_pre(1)[of p dm es1 \<open>unat d\<close> s1 \<open>SmtDef_body ?D\<close>] by (cases \<open>tr_term_m p dm es1 (unat d) s1 (SmtDef_body ?D)\<close>) simp
    have b1: \<open>bnd s1\<close> using bnd_pre[OF pb] 3(8) e by simp
    have i1: \<open>\<forall>e \<in> set es1. ib e\<close> using 3(1)[OF False a(1) a(2) 3(4,5,6,7), where S=S] b1 r by simp
    show ?thesis using 3(2)[OF False a(1) a(3) l i1 3(6,7)] e 3(8) r by simp
  qed
next
  case (4 p F dl el n op args)
  obtain s1 es1 where r: \<open>tr_args_m p dm env n S args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n S args\<close>)
  have l: \<open>length es1 = length args\<close> using tr_pre(2)[OF r] by simp
  have e: \<open>tr_term_m p dm env n S (SmtTerm_App op args) = enc_app_m s1 op es1\<close> using r by simp
  have b1: \<open>bnd s1\<close> using bnd_pre[OF pre_enc_app[OF pre_refl]] 4(7) e by simp
  have a: \<open>toks p F dl el n args\<close> using 4(2) by simp
  have i1: \<open>\<forall>e \<in> set es1. ib e\<close> using 4(1)[OF a 4(3,4,5,6), where S=S] b1 r by simp
  show ?case using enc_app_ib[OF i1] 4(2) l 4(7) e by simp
next
  case (7 p F dl el n a rest)
  obtain s1 e1 where r1: \<open>tr_term_m p dm env n S a = (s1, e1)\<close> by (cases \<open>tr_term_m p dm env n S a\<close>)
  obtain s2 es2 where r2: \<open>tr_args_m p dm env n s1 rest = (s2, es2)\<close> by (cases \<open>tr_args_m p dm env n s1 rest\<close>)
  have e: \<open>tr_args_m p dm env n S (a # rest) = (s2, e1 # es2)\<close> using r1 r2 by simp
  have b1: \<open>bnd s1\<close> using bnd_pre[of s1 s2] tr_pre(2)[OF r2] 7(8) e by simp
  have \<open>ib e1\<close> using 7(1)[of env S] 7(3-7) b1 r1 by simp
  moreover have \<open>\<forall>e \<in> set es2. ib e\<close> using 7(2)[of env s1] 7(3-7) 7(8) e r2 by simp
  ultimately show ?case using e by simp
qed simp_all


subsection \<open>The loops of \<^verbatim>\<open>enc_eq\<close> in closed form\<close>

text \<open>The pairs the two loops of \<^verbatim>\<open>enc_eq\<close> have visited before the inner loop reaches \<open>(i, j)\<close>.\<close>
definition eq_pre :: \<open>nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>eq_pre n dst i j \<equiv>
     filter (\<lambda>(i, j). dst \<or> j = Suc i)
       (concat (map (\<lambda>i'. map (\<lambda>j'. (i', j')) [Suc i'..<n]) [0..<i]) @ map (\<lambda>j'. (i, j')) [Suc i..<j])\<close>

definition EQ :: \<open>enc_m list \<Rightarrow> bool \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> st \<times> (nat \<times> bool) list\<close> where
  \<open>EQ es dst S i j \<equiv> foldl (eq_step_m es dst) (S, []) (eq_pre (length es) dst i j)\<close>

lemma eq_pre_Suc: \<open>Suc i \<le> j \<Longrightarrow> eq_pre n dst i (Suc j) = eq_pre n dst i j @ (if dst \<or> j = Suc i then [(i, j)] else [])\<close>
  by (simp add: eq_pre_def)

lemma eq_pre_next: \<open>eq_pre n dst i n = eq_pre n dst (Suc i) (Suc (Suc i))\<close>
  by (simp add: eq_pre_def)

lemma eq_pre_0: \<open>eq_pre n dst 0 (Suc 0) = []\<close>
  by (simp add: eq_pre_def)

lemma eq_pre_final: \<open>eq_pre n dst n (Suc n) = eq_pairs_m n dst\<close>
  by (simp add: eq_pre_def eq_pairs_m_def)

lemma EQ_Suc: \<open>Suc i \<le> j \<Longrightarrow> EQ es dst S i (Suc j) = (if dst \<or> j = Suc i then eq_step_m es dst (EQ es dst S i j) (i, j) else EQ es dst S i j)\<close>
  by (simp add: EQ_def eq_pre_Suc)

lemma EQ_next: \<open>EQ es dst S i (length es) = EQ es dst S (Suc i) (Suc (Suc i))\<close>
  by (simp add: EQ_def eq_pre_next)

lemma EQ_0: \<open>EQ es dst S 0 (Suc 0) = (S, [])\<close>
  by (simp add: EQ_def eq_pre_0)

lemma EQ_final: \<open>enc_eq_m S es dst = gate_andor_m (fst (EQ es dst S (length es) (Suc (length es)))) (snd (EQ es dst S (length es) (Suc (length es)))) True\<close>
  by (simp add: enc_eq_m_def EQ_def eq_pre_final Let_def)

lemma eq_pairs_split:
  assumes \<open>i < n\<close> \<open>Suc i \<le> j\<close> \<open>j \<le> n\<close>
  shows \<open>\<exists>rest. eq_pairs_m n dst = eq_pre n dst i j @ rest\<close>
proof -
  let ?row = \<open>\<lambda>i'. map (\<lambda>j'. (i', j')) [Suc i'..<n]\<close>
  have u: \<open>[0..<n] = [0..<i] @ i # [Suc i..<n]\<close>
    using assms(1) upt_add_eq_append'[of 0 i n] upt_conv_Cons[of i n] by simp
  have v: \<open>map (\<lambda>j'. (i, j')) [Suc i..<n] = map (\<lambda>j'. (i, j')) [Suc i..<j] @ map (\<lambda>j'. (i, j')) [j..<n]\<close>
    using assms(2,3) upt_add_eq_append'[of \<open>Suc i\<close> j n] by simp
  have c: \<open>concat (map ?row [0..<n]) =
      (concat (map ?row [0..<i]) @ map (\<lambda>j'. (i, j')) [Suc i..<j]) @ (map (\<lambda>j'. (i, j')) [j..<n] @ concat (map ?row [Suc i..<n]))\<close>
    unfolding u by (simp add: v)
  show ?thesis unfolding eq_pairs_m_def eq_pre_def c filter_append by blast
qed

lemma pre_EQ_final:
  assumes \<open>(i < length es \<and> Suc i \<le> j \<and> j \<le> length es) \<or> (i = length es \<and> j = Suc i)\<close>
  shows \<open>pre (fst (EQ es dst S i j)) (fst (enc_eq_m S es dst))\<close>
proof -
  obtain rest where r: \<open>eq_pairs_m (length es) dst = eq_pre (length es) dst i j @ rest\<close>
    using assms eq_pairs_split[of i \<open>length es\<close> j dst] eq_pre_final[of \<open>length es\<close> dst] by (metis append_Nil2)
  have \<open>pre (fst (EQ es dst S i j)) (fst (foldl (eq_step_m es dst) (EQ es dst S i j) rest))\<close>
    by (rule pre_eq_fold[OF pre_refl])
  then show ?thesis unfolding enc_eq_m_def Let_def r EQ_def foldl_append by (rule pre_gate_andor)
qed

lemma eq_fold_len:
  \<open>length (snd (foldl (eq_step_m es dst) sl prs)) = length (snd sl) + length prs \<and>
   length (st_atoms (fst sl)) + length prs \<le> length (st_atoms (fst (foldl (eq_step_m es dst) sl prs)))\<close>
proof (induction prs arbitrary: sl)
  case Nil
  then show ?case by simp
next
  case (Cons ij prs)
  obtain S L where sl: \<open>sl = (S, L)\<close> by (cases sl)
  obtain i j where ij: \<open>ij = (i, j)\<close> by (cases ij)
  let ?s1 = \<open>eq_step_m es dst sl ij\<close>
  have \<open>length (snd ?s1) = Suc (length L) \<and> Suc (length (st_atoms S)) \<le> length (st_atoms (fst ?s1))\<close>
  proof (cases \<open>is_lit_m (es ! i)\<close>)
    case True
    obtain a pa b pb where l: \<open>enc_lit_m (es ! i) = (a, pa)\<close> \<open>enc_lit_m (es ! j) = (b, pb)\<close> by (metis prod.exhaust)
    then show ?thesis using True by (simp add: sl ij eq_step_m_def gate_xor_eq Let_def)
  next
    case False
    let ?r1 = \<open>enc_term_m S (es ! i)\<close>
    let ?r2 = \<open>enc_term_m (fst ?r1) (es ! j)\<close>
    have p: \<open>pre S (fst ?r2)\<close> by (intro pre_enc_term pre_refl)
    show ?thesis using False pre_len[OF p] by (simp add: sl ij eq_step_m_def Let_def add_atom_m_def)
  qed
  then show ?case using Cons.IH[of ?s1] by (simp add: sl)
qed

lemma eq_pairs_len: \<open>length (eq_pairs_m n dst) \<le> n * n\<close>
proof -
  have \<open>length (concat (map (\<lambda>i'. map (\<lambda>j'. (i', j')) [Suc i'..<n]) [0..<n])) \<le> n * n\<close>
  proof -
    have \<open>length (concat (map (\<lambda>i'. map (\<lambda>j'. (i', j')) [Suc i'..<n]) [0..<m])) \<le> m * n\<close> for m
      by (induction m) auto
    then show ?thesis .
  qed
  then show ?thesis unfolding eq_pairs_m_def by (meson le_trans length_filter_le)
qed

lemma EQ_bnd:
  \<open>bnd (fst (enc_eq_m S es dst)) \<Longrightarrow> (i < length es \<and> Suc i \<le> j \<and> j \<le> length es) \<or> (i = length es \<and> j = Suc i) \<Longrightarrow>
   bnd (fst (EQ es dst S i j))\<close>
  using bnd_pre pre_EQ_final by blast

lemma st_tr_of_bnd: \<open>bnd S \<Longrightarrow> st_of (tr_of S) = S\<close>
  by (simp add: bnd_def st_tr_of)

lemma unat_next_tr_of: \<open>st_next S < 2 ^ 64 \<Longrightarrow> unat (Tr_next_fun (tr_of S)) = st_next S\<close>
  by (simp add: tr_of_def unat_of_nat_eq)

lemma gate_andor_lmlw: \<open>gate_andor_m S (map (lm \<circ> lw) ls) cj = gate_andor_m S ls cj\<close>
  by (simp add: gate_andor_eq andor_cl_m_def lit_m_def lm_def lw_def comp_def)

lemma enc_lit_encm_lt: \<open>fst (enc_lit_m (encm e)) < 2 ^ 64\<close>
  by (cases e) (simp_all add: unat_lt2p[where 'a=64, simplified])

lemma lm_lw_enc: \<open>lm (lw (enc_lit_m (encm e))) = enc_lit_m (encm e)\<close>
  by (rule lm_lw[OF enc_lit_encm_lt])

lemma EQ_final_facts:
  assumes \<open>bnd (fst (enc_eq_m S es dst))\<close>
  shows \<open>bnd (fst (EQ es dst S (length es) (Suc (length es))))\<close>
    and \<open>Suc (st_next (fst (EQ es dst S (length es) (Suc (length es))))) < 2 ^ 64\<close>
    and \<open>length (snd (EQ es dst S (length es) (Suc (length es)))) < 2 ^ 64\<close>
    and \<open>length (snd (EQ es dst S (length es) (Suc (length es)))) \<le> length es * length es\<close>
proof -
  let ?X = \<open>EQ es dst S (length es) (Suc (length es))\<close>
  show \<open>bnd (fst ?X)\<close> using EQ_bnd[OF assms] by simp
  have g: \<open>enc_eq_m S es dst = gate_andor_m (fst ?X) (snd ?X) True\<close> by (rule EQ_final)
  show \<open>Suc (st_next (fst ?X)) < 2 ^ 64\<close> using assms by (simp add: g gate_andor_eq bnd_def)
  have l: \<open>length (snd ?X) = length (eq_pairs_m (length es) dst) \<and> length (eq_pairs_m (length es) dst) \<le> length (st_atoms (fst ?X))\<close>
    using eq_fold_len[of es dst \<open>(S, [])\<close> \<open>eq_pairs_m (length es) dst\<close>] by (simp add: EQ_def eq_pre_final)
  show \<open>length (snd ?X) < 2 ^ 64\<close> using l \<open>bnd (fst ?X)\<close> by (simp add: bnd_def)
  show \<open>length (snd ?X) \<le> length es * length es\<close> using l eq_pairs_len by simp
qed

lemma bnd_EQ_Suc:
  \<open>bnd (fst (enc_eq_m S es dst)) \<Longrightarrow> i < length es \<Longrightarrow> Suc i \<le> j \<Longrightarrow> j < length es \<Longrightarrow> (dst \<or> j = Suc i) \<Longrightarrow>
   bnd (fst (eq_step_m es dst (EQ es dst S i j) (i, j)))\<close>
  using EQ_bnd[of S es dst i \<open>Suc j\<close>] EQ_Suc[of i j es dst S] by simp

lemma eq_step_lit:
  assumes \<open>is_lit_m (es ! i)\<close> \<open>bnd (fst (eq_step_m es dst X (i, j)))\<close>
  shows \<open>bnd (fst X)\<close> \<open>Suc (st_next (fst X)) < 2 ^ 64\<close>
    \<open>eq_step_m es dst X (i, j) =
       (fst (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j))),
        snd X @ [(fst (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j)))),
                  if dst then snd (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j))))
                  else \<not> snd (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j)))))])\<close>
proof -
  show e: \<open>eq_step_m es dst X (i, j) =
       (fst (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j))),
        snd X @ [(fst (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j)))),
                  if dst then snd (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j))))
                  else \<not> snd (snd (gate_xor_m (fst X) (enc_lit_m (es ! i)) (enc_lit_m (es ! j)))))])\<close>
    using assms(1) by (cases X) (simp add: eq_step_m_def Let_def)
  obtain a pa b pb where l: \<open>enc_lit_m (es ! i) = (a, pa)\<close> \<open>enc_lit_m (es ! j) = (b, pb)\<close> by (metis prod.exhaust)
  have p: \<open>pre (fst X) (fst (eq_step_m es dst X (i, j)))\<close> unfolding e fst_conv by (intro pre_gate_xor pre_refl)
  show \<open>bnd (fst X)\<close> by (rule bnd_pre[OF p assms(2)])
  show \<open>Suc (st_next (fst X)) < 2 ^ 64\<close> using assms(2) unfolding e by (simp add: l gate_xor_eq bnd_def)
qed

lemma eq_step_term:
  assumes \<open>\<not> is_lit_m (es ! i)\<close> \<open>bnd (fst (eq_step_m es dst X (i, j)))\<close>
  shows \<open>bnd (fst X)\<close> \<open>bnd (fst (enc_term_m (fst X) (es ! i)))\<close>
    \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))\<close>
    \<open>eq_step_m es dst X (i, j) =
       (fst (add_atom_m (fst (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))
               (snd (enc_term_m (fst X) (es ! i))) (snd (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))),
        snd X @ [(length (st_atoms (fst (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))), \<not> dst)])\<close>
proof -
  show e: \<open>eq_step_m es dst X (i, j) =
       (fst (add_atom_m (fst (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))
               (snd (enc_term_m (fst X) (es ! i))) (snd (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))),
        snd X @ [(length (st_atoms (fst (enc_term_m (fst (enc_term_m (fst X) (es ! i))) (es ! j)))), \<not> dst)])\<close>
    using assms(1) by (cases X) (simp add: eq_step_m_def Let_def add_atom_m_def)
  let ?Y1 = \<open>fst (enc_term_m (fst X) (es ! i))\<close>
  let ?Y2 = \<open>fst (enc_term_m ?Y1 (es ! j))\<close>
  have p2: \<open>pre ?Y2 (fst (eq_step_m es dst X (i, j)))\<close> unfolding e fst_conv by (intro pre_add_atom pre_refl)
  have p1: \<open>pre ?Y1 ?Y2\<close> by (intro pre_enc_term pre_refl)
  have p0: \<open>pre (fst X) ?Y1\<close> by (intro pre_enc_term pre_refl)
  show b2: \<open>bnd ?Y2\<close> by (rule bnd_pre[OF p2 assms(2)])
  show b1: \<open>bnd ?Y1\<close> by (rule bnd_pre[OF p1 b2])
  show \<open>bnd (fst X)\<close> by (rule bnd_pre[OF p0 b1])
qed

lemma word_eq_plus1: \<open>unat (r :: 64 word) < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> (j = r + 1) = (unat j = Suc (unat r))\<close>
proof -
  assume a: \<open>unat r < n\<close> and b: \<open>n < 2 ^ 64\<close>
  have u: \<open>unat (r + 1) = Suc (unat r)\<close> using unat_plus_one_of_less_bound[OF a] b by simp
  show ?thesis by (simp add: word_unat_eq_iff u)
qed

context QFUF_ctx
begin

subsection \<open>Small functions\<close>

definition copy_enc_contract :: \<open>Enc \<Rightarrow> ('s, Enc, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>copy_enc_contract e \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = e\<rangle>)\<close>

lemma copy_enc_spec [crush_specs]:
  shows \<open>\<Gamma>; copy_enc e \<Turnstile>\<^sub>F copy_enc_contract e\<close>
  apply (crush_boot f: copy_enc_def contract: copy_enc_contract_def)
  apply (crush_base split: Enc.splits)
  done

definition add_term_contract :: \<open>Tr \<Rightarrow> 64 word \<Rightarrow> 64 word list \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>add_term_contract s f args \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (make_Tr (Tr_terms s @ [make_Term f args]) (Tr_atoms s) (Tr_clauses s) (Tr_next_fun s),
                word_of_nat (length (Tr_terms s)), TNil)\<rangle>)\<close>

lemma add_term_spec [crush_specs]:
  shows \<open>\<Gamma>; add_term s f args \<Turnstile>\<^sub>F add_term_contract s f args\<close>
  apply (crush_boot f: add_term_def contract: add_term_contract_def)
  apply (crush_base inline: vec_push_def len_def)
  done

definition add_atom_contract :: \<open>Tr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>add_atom_contract s l r0 \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (make_Tr (Tr_terms s) (Tr_atoms s @ [make_Atom l r0]) (Tr_clauses s) (Tr_next_fun s),
                word_of_nat (length (Tr_atoms s)), TNil)\<rangle>)\<close>

lemma add_atom_spec [crush_specs]:
  shows \<open>\<Gamma>; add_atom s l r0 \<Turnstile>\<^sub>F add_atom_contract s l r0\<close>
  apply (crush_boot f: add_atom_def contract: add_atom_contract_def)
  apply (crush_base inline: vec_push_def len_def)
  done

definition add_clause_contract :: \<open>Tr \<Rightarrow> Lit list \<Rightarrow> ('s, Tr, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>add_clause_contract s ls \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = make_Tr (Tr_terms s) (Tr_atoms s) (Tr_clauses s @ [make_Clause ls]) (Tr_next_fun s)\<rangle>)\<close>

lemma add_clause_spec [crush_specs]:
  shows \<open>\<Gamma>; add_clause s ls \<Turnstile>\<^sub>F add_clause_contract s ls\<close>
  apply (crush_boot f: add_clause_def contract: add_clause_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition new_const_contract :: \<open>Tr \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>new_const_contract s \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (unat (Tr_next_fun s)) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []]) (Tr_atoms s) (Tr_clauses s) (Tr_next_fun s + 1),
                word_of_nat (length (Tr_terms s)), TNil)\<rangle>)\<close>

lemma new_const_spec [crush_specs]:
  shows \<open>\<Gamma>; new_const s \<Turnstile>\<^sub>F new_const_contract s\<close>
  apply (crush_boot f: new_const_def contract: new_const_contract_def)
  apply (crush_base simp add: unat_plus_one_of_less_bound)
  done

definition new_lit_contract :: \<open>Tr \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>new_lit_contract s \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (unat (Tr_next_fun s)) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []])
                  (Tr_atoms s @ [make_Atom (word_of_nat (length (Tr_terms s))) 0]) (Tr_clauses s) (Tr_next_fun s + 1),
                word_of_nat (length (Tr_atoms s)), TNil)\<rangle>)\<close>

lemma new_lit_spec [crush_specs]:
  shows \<open>\<Gamma>; new_lit s \<Turnstile>\<^sub>F new_lit_contract s\<close>
  apply (crush_boot f: new_lit_def contract: new_lit_contract_def)
  apply crush_base
  done

definition lit_contract :: \<open>64 word \<Rightarrow> bool \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>lit_contract a pos \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = make_Lit a pos\<rangle>)\<close>

lemma lit_spec [crush_specs]:
  shows \<open>\<Gamma>; lit a pos \<Turnstile>\<^sub>F lit_contract a pos\<close>
  apply (crush_boot f: lit_def contract: lit_contract_def)
  apply crush_base
  done

definition enc_lit_contract :: \<open>Enc \<Rightarrow> ('s, 64 word \<times> bool \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>enc_lit_contract e \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = lw (enc_lit_m (encm e))\<rangle>)\<close>

lemma enc_lit_spec [crush_specs]:
  shows \<open>\<Gamma>; enc_lit e \<Turnstile>\<^sub>F enc_lit_contract e\<close>
  apply (crush_boot f: enc_lit_def contract: enc_lit_contract_def)
  apply (crush_base split: Enc.splits simp add: lw_def)
  done

definition is_lit_contract :: \<open>Enc \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>is_lit_contract e \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = is_lit_m (encm e)\<rangle>)\<close>

lemma is_lit_spec [crush_specs]:
  shows \<open>\<Gamma>; is_lit e \<Turnstile>\<^sub>F is_lit_contract e\<close>
  apply (crush_boot f: is_lit_def contract: is_lit_contract_def)
  apply (crush_base split: Enc.splits)
  done

definition clause1_contract :: \<open>Lit \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause1_contract a \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = [a]\<rangle>)\<close>

lemma clause1_spec [crush_specs]:
  shows \<open>\<Gamma>; clause1 a \<Turnstile>\<^sub>F clause1_contract a\<close>
  apply (crush_boot f: clause1_def contract: clause1_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition clause2_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause2_contract a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = [a, b]\<rangle>)\<close>

lemma clause2_spec [crush_specs]:
  shows \<open>\<Gamma>; clause2 a b \<Turnstile>\<^sub>F clause2_contract a b\<close>
  apply (crush_boot f: clause2_def contract: clause2_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition clause3_contract :: \<open>Lit \<Rightarrow> Lit \<Rightarrow> Lit \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>clause3_contract a b d \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = [a, b, d]\<rangle>)\<close>

lemma clause3_spec [crush_specs]:
  shows \<open>\<Gamma>; clause3 a b d \<Turnstile>\<^sub>F clause3_contract a b d\<close>
  apply (crush_boot f: clause3_def contract: clause3_contract_def)
  apply (crush_base inline: vec_push_def)
  done

lemma wn_Suc_unat: \<open>(word_of_nat (Suc (unat w)) :: 64 word) = w + 1\<close>
  by simp

subsection \<open>The gates\<close>

definition enc_term_contract :: \<open>Tr \<Rightarrow> Enc \<Rightarrow> ('s, Tr \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>enc_term_contract s e \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>st_next (fst (enc_term_m (st_of s) (encm e))) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (tr_of (fst (enc_term_m (st_of s) (encm e))), word_of_nat (snd (enc_term_m (st_of s) (encm e))), TNil)\<rangle>)\<close>

lemma enc_term_spec [crush_specs]:
  shows \<open>\<Gamma>; enc_term s e \<Turnstile>\<^sub>F enc_term_contract s e\<close>
  apply (crush_boot f: enc_term_def contract: enc_term_contract_def)
  apply (crush_base split: Enc.splits simp add: enc_term_lit_eq tr_of_def st_of_def lit_m_def wn_Suc_unat)
  apply (auto simp: new_const_eq add_atom_m_def add_clause_m_def tr_of_def lit_m_def wn_Suc_unat)
  done

definition gate_xor_contract :: \<open>Tr \<Rightarrow> 64 word \<times> bool \<times> tnil \<Rightarrow> 64 word \<times> bool \<times> tnil \<Rightarrow>
    ('s, Tr \<times> (64 word \<times> bool \<times> tnil) \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_xor_contract s x y \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (unat (Tr_next_fun s)) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (tr_of (fst (gate_xor_m (st_of s) (lm x) (lm y))), lw (snd (gate_xor_m (st_of s) (lm x) (lm y))), TNil)\<rangle>)\<close>

lemma gate_xor_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_xor s x y \<Turnstile>\<^sub>F gate_xor_contract s x y\<close>
  apply (crush_boot f: gate_xor_def contract: gate_xor_contract_def)
  apply (crush_base simp add: lm_def lw_def gate_xor_eq tr_of_def st_of_def lit_m_def wn_Suc_unat)
  done

definition gate_ite_contract :: \<open>Tr \<Rightarrow> 64 word \<times> bool \<times> tnil \<Rightarrow> 64 word \<times> bool \<times> tnil \<Rightarrow> 64 word \<times> bool \<times> tnil \<Rightarrow>
    ('s, Tr \<times> Enc \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_ite_contract s c x y \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (unat (Tr_next_fun s)) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (tr_of (fst (gate_ite_m (st_of s) (lm c) (lm x) (lm y))), enc_of (snd (gate_ite_m (st_of s) (lm c) (lm x) (lm y))), TNil)\<rangle>)\<close>

lemma gate_ite_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_ite s c x y \<Turnstile>\<^sub>F gate_ite_contract s c x y\<close>
  apply (crush_boot f: gate_ite_def contract: gate_ite_contract_def)
  apply (crush_base simp add: lm_def lw_def gate_ite_eq tr_of_def st_of_def lit_m_def wn_Suc_unat)
  done

definition gate_andor_contract :: \<open>Tr \<Rightarrow> (64 word \<times> bool \<times> tnil) list \<Rightarrow> bool \<Rightarrow>
    ('s, Tr \<times> Enc \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>gate_andor_contract s ls cj \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (unat (Tr_next_fun s)) < 2 ^ 64 \<and> length ls < 2 ^ 64 \<and> length ls \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (tr_of (fst (gate_andor_m (st_of s) (map lm ls) cj)), enc_of (snd (gate_andor_m (st_of s) (map lm ls) cj)), TNil)\<rangle>)\<close>

lemma gate_andor_spec [crush_specs]:
  shows \<open>\<Gamma>; gate_andor s ls cj \<Turnstile>\<^sub>F gate_andor_contract s ls cj\<close>
  apply (crush_boot f: gate_andor_def contract: gate_andor_contract_def)
  apply (crush_base inline: len_def)
  subgoal for s_ref big_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gs sv gb bv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> big_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>bv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i \<le> length ls \<and>
            sv = make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []])
                   (Tr_atoms s @ [make_Atom (word_of_nat (length (Tr_terms s))) 0])
                   (Tr_clauses s @ map (\<lambda>l. make_Clause (andor_cl_m (length (Tr_atoms s)) cj l)) (map lm (take (unat i) ls)))
                   (Tr_next_fun s + 1) \<and>
            bv = lit_m (length (Tr_atoms s)) cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) (map lm (take (unat i) ls)) \<and>
            length ls - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gs sv gb bv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> big_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>bv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i < length ls \<and>
            sv = make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []])
                   (Tr_atoms s @ [make_Atom (word_of_nat (length (Tr_terms s))) 0])
                   (Tr_clauses s @ map (\<lambda>l. make_Clause (andor_cl_m (length (Tr_atoms s)) cj l)) (map lm (take (unat i) ls)))
                   (Tr_next_fun s + 1) \<and>
            bv = lit_m (length (Tr_atoms s)) cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) (map lm (take (unat i) ls)) \<and>
            length ls - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
        take_Suc_conv_app_nth gate_andor_eq st_of_def tr_of_def wn_Suc_unat lm_def lit_m_def andor_cl_m_def)
    done
  done

definition enc_eq_contract :: \<open>Tr \<Rightarrow> Enc list \<Rightarrow> bool \<Rightarrow> ('s, Tr \<times> Enc \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>enc_eq_contract s es dst \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>length es < 2 ^ 64 \<and> length es \<le> urust_fuel \<and> length es * length es \<le> urust_fuel \<and>
         bnd (fst (enc_eq_m (st_of s) (map encm es) dst))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>r = (tr_of (fst (enc_eq_m (st_of s) (map encm es) dst)), enc_of (snd (enc_eq_m (st_of s) (map encm es) dst)), TNil)\<rangle>)\<close>

lemma enc_eq_spec [crush_specs]:
  shows \<open>\<Gamma>; enc_eq s es dst \<Turnstile>\<^sub>F enc_eq_contract s es dst\<close>
  apply (crush_boot f: enc_eq_def contract: enc_eq_contract_def)
  apply (crush_base inline: len_def)
  subgoal for s_ref ls_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gs sv gl lv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i \<le> length es \<and>
            sv = tr_of (fst (EQ (map encm es) dst (st_of s) (unat i) (Suc (unat i)))) \<and>
            lv = map lw (snd (EQ (map encm es) dst (st_of s) (unat i) (Suc (unat i)))) \<and>
            length es - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gs sv gl lv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i < length es \<and>
            sv = tr_of (fst (EQ (map encm es) dst (st_of s) (unat i) (Suc (unat i)))) \<and>
            lv = map lw (snd (EQ (map encm es) dst (st_of s) (unat i) (Suc (unat i)))) \<and>
            length es - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound EQ_0 tr_st_of)
    sorry
  done

end

end

