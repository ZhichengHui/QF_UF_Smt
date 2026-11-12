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
    and \<open>st_next (fst (EQ es dst S (length es) (Suc (length es)))) < 2 ^ 64\<close>
proof -
  let ?X = \<open>EQ es dst S (length es) (Suc (length es))\<close>
  show \<open>bnd (fst ?X)\<close> using EQ_bnd[OF assms] by simp
  have g: \<open>enc_eq_m S es dst = gate_andor_m (fst ?X) (snd ?X) True\<close> by (rule EQ_final)
  show \<open>Suc (st_next (fst ?X)) < 2 ^ 64\<close> using assms by (simp add: g gate_andor_eq bnd_def)
  have l: \<open>length (snd ?X) = length (eq_pairs_m (length es) dst) \<and> length (eq_pairs_m (length es) dst) \<le> length (st_atoms (fst ?X))\<close>
    using eq_fold_len[of es dst \<open>(S, [])\<close> \<open>eq_pairs_m (length es) dst\<close>] by (simp add: EQ_def eq_pre_final)
  show \<open>length (snd ?X) < 2 ^ 64\<close> using l \<open>bnd (fst ?X)\<close> by (simp add: bnd_def)
  show \<open>length (snd ?X) \<le> length es * length es\<close> using l eq_pairs_len by simp
  show \<open>st_next (fst ?X) < 2 ^ 64\<close> using \<open>bnd (fst ?X)\<close> by (simp add: bnd_def)
qed

lemma EQ_final_all:
  \<open>bnd (fst (enc_eq_m S es dst)) \<Longrightarrow>
   bnd (fst (EQ es dst S (length es) (Suc (length es)))) \<and>
   Suc (st_next (fst (EQ es dst S (length es) (Suc (length es))))) < 2 ^ 64 \<and>
   length (snd (EQ es dst S (length es) (Suc (length es)))) < 2 ^ 64 \<and>
   length (snd (EQ es dst S (length es) (Suc (length es)))) \<le> length es * length es \<and>
   st_next (fst (EQ es dst S (length es) (Suc (length es)))) < 2 ^ 64 \<and>
   bnd (fst (enc_eq_m S es dst))\<close>
  using EQ_final_facts by blast


lemma EQ_final_r: \<open>n = length es \<Longrightarrow> gate_andor_m (fst (EQ es dst S n (Suc n))) (snd (EQ es dst S n (Suc n))) True = enc_eq_m S es dst\<close>
  by (simp add: EQ_final)


lemma EQ_next_r: \<open>n = length es \<Longrightarrow> EQ es dst S i n = EQ es dst S (Suc i) (Suc (Suc i))\<close>
  by (simp add: EQ_next)

lemma EQ_bnd_lt:
  \<open>bnd (fst (enc_eq_m S es dst)) \<Longrightarrow> Suc i \<le> j \<Longrightarrow> j < length es \<Longrightarrow> bnd (fst (EQ es dst S i j))\<close>
  using EQ_bnd[of S es dst i j] by simp

lemma unat_2_plus: \<open>unat (r :: 64 word) < n \<Longrightarrow> Suc (unat r) < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (2 + r) = Suc (Suc (unat r))\<close>
proof -
  assume a: \<open>unat r < n\<close> and b: \<open>Suc (unat r) < n\<close> and c: \<open>n < 2 ^ 64\<close>
  have u: \<open>unat (r + 1) = Suc (unat r)\<close> using unat_plus_one_of_less_bound[OF a] c by simp
  have \<open>unat (r + 1 + 1) = Suc (unat (r + 1))\<close> using unat_plus_one_of_less_bound[of \<open>r + 1\<close> n] u b c by simp
  moreover have \<open>r + 1 + 1 = 2 + r\<close> by simp
  ultimately show ?thesis using u by simp
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

lemma bnd_next: \<open>bnd S \<Longrightarrow> st_next S < 18446744073709551616\<close>
  by (simp add: bnd_def)

lemma eq_step_lit_r:
  assumes \<open>is_lit_m (encm (es ! i))\<close> \<open>i < length es\<close> \<open>j < length es\<close> \<open>bnd (fst (eq_step_m (map encm es) dst X (i, j)))\<close>
  shows \<open>bnd (fst X)\<close> \<open>st_next (fst X) < 18446744073709551615\<close>
    \<open>eq_step_m (map encm es) dst X (i, j) =
       (fst (gate_xor_m (fst X) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j)))),
        snd X @ [(fst (snd (gate_xor_m (fst X) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j))))),
                  if dst then snd (snd (gate_xor_m (fst X) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j)))))
                  else \<not> snd (snd (gate_xor_m (fst X) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j))))))])\<close>
  using eq_step_lit[of \<open>map encm es\<close> i dst X j] assms by simp_all

lemma eq_step_term_r:
  assumes \<open>\<not> is_lit_m (encm (es ! i))\<close> \<open>i < length es\<close> \<open>j < length es\<close> \<open>bnd (fst (eq_step_m (map encm es) dst X (i, j)))\<close>
  shows \<open>bnd (fst X)\<close> \<open>bnd (fst (enc_term_m (fst X) (encm (es ! i))))\<close>
    \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst X) (encm (es ! i)))) (encm (es ! j))))\<close>
    \<open>eq_step_m (map encm es) dst X (i, j) =
       (fst (add_atom_m (fst (enc_term_m (fst (enc_term_m (fst X) (encm (es ! i)))) (encm (es ! j))))
               (snd (enc_term_m (fst X) (encm (es ! i)))) (snd (enc_term_m (fst (enc_term_m (fst X) (encm (es ! i)))) (encm (es ! j))))),
        snd X @ [(length (st_atoms (fst (enc_term_m (fst (enc_term_m (fst X) (encm (es ! i)))) (encm (es ! j))))), \<not> dst)])\<close>
  using eq_step_term[of \<open>map encm es\<close> i dst X j] assms by simp_all


lemma eq_step_lit_R:
  assumes \<open>bnd (fst (enc_eq_m S (map encm es) dst))\<close> \<open>Suc i \<le> j\<close> \<open>j < length es\<close> \<open>dst \<or> j = Suc i\<close>
    \<open>is_lit_m (encm (es ! i))\<close>
  shows \<open>bnd (fst (EQ (map encm es) dst S i j))\<close> \<open>st_next (fst (EQ (map encm es) dst S i j)) < 18446744073709551615\<close>
    \<open>eq_step_m (map encm es) dst (EQ (map encm es) dst S i j) (i, j) =
       (fst (gate_xor_m (fst (EQ (map encm es) dst S i j)) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j)))),
        snd (EQ (map encm es) dst S i j) @
          [(fst (snd (gate_xor_m (fst (EQ (map encm es) dst S i j)) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j))))),
            if dst then snd (snd (gate_xor_m (fst (EQ (map encm es) dst S i j)) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j)))))
            else \<not> snd (snd (gate_xor_m (fst (EQ (map encm es) dst S i j)) (enc_lit_m (encm (es ! i))) (enc_lit_m (encm (es ! j))))))])\<close>
  using eq_step_lit_r[OF assms(5) _ assms(3) bnd_EQ_Suc[OF assms(1) _ assms(2)]] assms(2-4) by simp_all

lemma eq_step_term_R:
  assumes \<open>bnd (fst (enc_eq_m S (map encm es) dst))\<close> \<open>Suc i \<le> j\<close> \<open>j < length es\<close> \<open>dst \<or> j = Suc i\<close>
    \<open>\<not> is_lit_m (encm (es ! i))\<close>
  shows \<open>bnd (fst (EQ (map encm es) dst S i j))\<close>
    \<open>bnd (fst (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i))))\<close>
    \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i)))) (encm (es ! j))))\<close>
    \<open>eq_step_m (map encm es) dst (EQ (map encm es) dst S i j) (i, j) =
       (fst (add_atom_m (fst (enc_term_m (fst (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i)))) (encm (es ! j))))
               (snd (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i))))
               (snd (enc_term_m (fst (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i)))) (encm (es ! j))))),
        snd (EQ (map encm es) dst S i j) @
          [(length (st_atoms (fst (enc_term_m (fst (enc_term_m (fst (EQ (map encm es) dst S i j)) (encm (es ! i)))) (encm (es ! j))))), \<not> dst)])\<close>
  using eq_step_term_r[OF assms(5) _ assms(3) bnd_EQ_Suc[OF assms(1) _ assms(2)]] assms(2-4) by simp_all


lemma unat_r1: \<open>unat (r :: 64 word) < 18446744073709551615 \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
  using unat_plus_one_of_less_bound[of r 18446744073709551615] by simp

lemma unat_2_plus': \<open>unat ((r :: 64 word) + 1) < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (2 + r) = Suc (unat (r + 1))\<close>
proof -
  assume a: \<open>unat (r + 1) < n\<close> and c: \<open>n < 2 ^ 64\<close>
  have \<open>unat (r + 1 + 1) = Suc (unat (r + 1))\<close> using unat_plus_one_of_less_bound[OF a] c by simp
  moreover have \<open>r + 1 + 1 = 2 + r\<close> by simp
  ultimately show ?thesis by simp
qed


lemma tr_of_sel: \<open>Tr_terms (tr_of S) = st_terms S\<close> \<open>Tr_atoms (tr_of S) = st_atoms S\<close>
  \<open>Tr_clauses (tr_of S) = st_clauses S\<close> \<open>Tr_next_fun (tr_of S) = word_of_nat (st_next S)\<close>
  by (simp_all add: tr_of_def)


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
    subgoal for k gs gl gi r j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gs sv gl lv gi' gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi'\<down>r \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>Suc (unat r) \<le> unat j \<and> unat j \<le> length es \<and> unat r < 18446744073709551615 \<and>
              sv = tr_of (fst (EQ (map encm es) dst (st_of s) (unat r) (unat j))) \<and>
              lv = map lw (snd (EQ (map encm es) dst (st_of s) (unat r) (unat j))) \<and>
              length es - unat j \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gs sv gl lv gi' gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi'\<down>r \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>Suc (unat r) \<le> unat j \<and> unat j < length es \<and> unat r < 18446744073709551615 \<and>
              sv = tr_of (fst (EQ (map encm es) dst (st_of s) (unat r) (unat j))) \<and>
              lv = map lw (snd (EQ (map encm es) dst (st_of s) (unat r) (unat j))) \<and>
              length es - unat j \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def
          simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound lm_lw_enc)
      apply (simp_all add: unat_r1 unat_2_plus'[where n=\<open>length es\<close>] word_eq_plus1[where n=\<open>length es\<close>])
      apply (simp_all add: EQ_Suc EQ_next_r eq_step_lit_R eq_step_term_R st_tr_of_bnd EQ_bnd_lt lw_def
          bnd_next unat_next_tr_of)
      apply (simp_all add: eq_step_lit_R eq_step_term_R st_tr_of_bnd EQ_bnd_lt bnd_next unat_next_tr_of tr_of_sel)
      apply (simp_all add: add_atom_m_def tr_of_def)
      done
    apply (all \<open>frule EQ_final_all, elim conjE\<close>)
    apply (simp_all add: EQ_final_r st_tr_of_bnd gate_andor_lmlw unat_next_tr_of)
    done
  done

subsection \<open>The loops of \<^verbatim>\<open>enc_app\<close> in closed form\<close>

text \<open>The bound and the result of \<^verbatim>\<open>enc_app\<close> as constants, so that the simplifier does not unfold
  \<^const>\<open>enc_app_m\<close> in the contract.\<close>
definition abnd :: \<open>st \<Rightarrow> SmtOp \<Rightarrow> enc_m list \<Rightarrow> bool\<close> where
  \<open>abnd S op es \<equiv> bnd (fst (enc_app_m S op es))\<close>

definition ares :: \<open>st \<Rightarrow> SmtOp \<Rightarrow> enc_m list \<Rightarrow> Tr \<times> Enc \<times> tnil\<close> where
  \<open>ares S op es \<equiv> (tr_of (fst (enc_app_m S op es)), enc_of (snd (enc_app_m S op es)), TNil)\<close>

definition XF :: \<open>enc_m list \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> st \<times> (nat \<times> bool)\<close> where
  \<open>XF es S k \<equiv> foldl xor_step_m (S, enc_lit_m (es ! 0)) (take k (tl es))\<close>

lemma XF_0: \<open>XF es S 0 = (S, enc_lit_m (es ! 0))\<close>
  by (simp add: XF_def)

lemma XF_step: \<open>1 \<le> m \<Longrightarrow> m < length es \<Longrightarrow>
  XF es S m = gate_xor_m (fst (XF es S (m - 1))) (snd (XF es S (m - 1))) (enc_lit_m (es ! m))\<close>
proof -
  assume a: \<open>1 \<le> m\<close> \<open>m < length es\<close>
  have t: \<open>take m (tl es) = take (m - 1) (tl es) @ [es ! m]\<close>
    using a by (cases es) (simp_all add: take_Suc_conv_app_nth[symmetric])
  show ?thesis unfolding XF_def t by (simp add: xor_step_m_def split_def)
qed

lemma XF_final: \<open>es \<noteq> [] \<Longrightarrow> enc_app_m S SmtOp_Xor es =
  (fst (XF es S (length es - 1)), ELit (fst (snd (XF es S (length es - 1)))) (snd (snd (XF es S (length es - 1)))))\<close>
  by (simp add: XF_def Let_def)

lemma XF_pre: \<open>k \<le> length es - 1 \<Longrightarrow> pre (fst (XF es S k)) (fst (XF es S (length es - 1)))\<close>
proof -
  assume k: \<open>k \<le> length es - 1\<close>
  have \<open>tl es = take k (tl es) @ drop k (tl es)\<close> by simp
  then have \<open>XF es S (length es - 1) = foldl xor_step_m (XF es S k) (drop k (tl es))\<close>
    unfolding XF_def by (metis foldl_append length_tl take_all_iff order_refl)
  then show ?thesis using pre_xor_fold[OF pre_refl, of \<open>XF es S k\<close> \<open>drop k (tl es)\<close>] by simp
qed

lemma XF_facts:
  assumes \<open>abnd S SmtOp_Xor (map encm es)\<close> \<open>1 \<le> m\<close> \<open>m < length es\<close>
  shows \<open>bnd (fst (XF (map encm es) S (m - Suc 0)))\<close> \<open>st_next (fst (XF (map encm es) S (m - Suc 0))) < 18446744073709551615\<close>
    \<open>fst (snd (XF (map encm es) S (m - Suc 0))) < 18446744073709551616\<close>
proof -
  let ?es = \<open>map encm es\<close>
  have ne: \<open>?es \<noteq> []\<close> using assms(3) by auto
  have bF: \<open>bnd (fst (XF ?es S (length ?es - 1)))\<close> using assms(1) XF_final[OF ne] by (simp add: abnd_def)
  have pm: \<open>pre (fst (XF ?es S m)) (fst (XF ?es S (length ?es - 1)))\<close> using XF_pre[of m ?es S] assms(3) by simp
  have bm: \<open>bnd (fst (XF ?es S m))\<close> by (rule bnd_pre[OF pm bF])
  have st: \<open>XF ?es S m = gate_xor_m (fst (XF ?es S (m - 1))) (snd (XF ?es S (m - 1))) (enc_lit_m (?es ! m))\<close>
    using XF_step[of m ?es S] assms(2,3) by simp
  obtain a pa b pb where l: \<open>snd (XF ?es S (m - 1)) = (a, pa)\<close> \<open>enc_lit_m (?es ! m) = (b, pb)\<close> by (metis prod.exhaust)
  have n: \<open>st_next (fst (XF ?es S m)) = Suc (st_next (fst (XF ?es S (m - 1))))\<close> unfolding st l by (simp add: gate_xor_eq)
  have p1: \<open>pre (fst (XF ?es S (m - 1))) (fst (XF ?es S m))\<close> unfolding st l by (intro pre_gate_xor pre_refl)
  have b1: \<open>bnd (fst (XF ?es S (m - 1)))\<close> by (rule bnd_pre[OF p1 bm])
  then show \<open>bnd (fst (XF ?es S (m - Suc 0)))\<close> by simp
  show \<open>st_next (fst (XF ?es S (m - Suc 0))) < 18446744073709551615\<close> using bm n by (simp add: bnd_def)
  have \<open>fst (snd (XF ?es S (m - 1))) = fst (enc_lit_m (?es ! 0)) \<or>
        fst (snd (XF ?es S (m - 1))) < length (st_atoms (fst (XF ?es S (m - 1))))\<close>
    using xor_fold_idx[of \<open>(S, enc_lit_m (?es ! 0))\<close> \<open>take (m - 1) (tl ?es)\<close>] unfolding XF_def by simp
  moreover have \<open>?es ! 0 = encm (es ! 0)\<close> using assms(3) by (intro nth_map) auto
  ultimately show \<open>fst (snd (XF ?es S (m - Suc 0))) < 18446744073709551616\<close>
    using b1 enc_lit_encm_lt[of \<open>es ! 0\<close>] by (auto simp: bnd_def)
qed

lemma implies_take_Suc: \<open>i < length es \<Longrightarrow> take (Suc i) (implies_lits_m es) =
  take i (implies_lits_m es) @ [(fst (enc_lit_m (es ! i)), if Suc i < length es then \<not> snd (enc_lit_m (es ! i)) else snd (enc_lit_m (es ! i)))]\<close>
  by (simp add: implies_lits_m_def take_Suc_conv_app_nth)

lemma implies_take_all: \<open>take (length es) (implies_lits_m es) = implies_lits_m es\<close>
  by (simp add: implies_lits_m_def)

lemma gate_ite_next: \<open>st_next (fst (gate_ite_m S c x y)) = Suc (st_next S)\<close>
  by (cases c; cases x; cases y) (simp add: gate_ite_eq)

lemma gate_andor_next: \<open>st_next (fst (gate_andor_m S ls cj)) = Suc (st_next S)\<close>
  by (simp add: gate_andor_eq)

lemma ite_term_facts:
  assumes \<open>bnd (fst (ite_term_m S es))\<close>
  shows \<open>st_next S < 18446744073709551615\<close> \<open>bnd (fst (enc_term_m (fst (new_const_m S)) (es ! 1)))\<close>
    \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst (new_const_m S)) (es ! 1))) (es ! 2)))\<close>
proof -
  let ?Y1 = \<open>fst (enc_term_m (fst (new_const_m S)) (es ! 1))\<close>
  let ?Y2 = \<open>fst (enc_term_m ?Y1 (es ! 2))\<close>
  have p2: \<open>pre ?Y2 (fst (ite_term_m S es))\<close> unfolding ite_term_m_def Let_def
    by (simp, intro pre_add_clause pre_add_atom pre_refl)
  show b2: \<open>bnd ?Y2\<close> by (rule bnd_pre[OF p2 assms])
  have p1: \<open>pre ?Y1 ?Y2\<close> by (intro pre_enc_term pre_refl)
  show b1: \<open>bnd ?Y1\<close> by (rule bnd_pre[OF p1 b2])
  have p0: \<open>pre (fst (new_const_m S)) ?Y1\<close> by (intro pre_enc_term pre_refl)
  have \<open>bnd (fst (new_const_m S))\<close> by (rule bnd_pre[OF p0 b1])
  then show \<open>st_next S < 18446744073709551615\<close> by (simp add: new_const_eq bnd_def)
qed


lemma abnd_andor:
  \<open>abnd (st_of s) SmtOp_And es \<Longrightarrow> unat (Tr_next_fun s) < 18446744073709551615\<close>
  \<open>abnd (st_of s) SmtOp_Or es \<Longrightarrow> unat (Tr_next_fun s) < 18446744073709551615\<close>
  \<open>abnd (st_of s) SmtOp_Implies es \<Longrightarrow> unat (Tr_next_fun s) < 18446744073709551615\<close>
  by (simp_all add: abnd_def bnd_def gate_andor_next st_of_def)

lemma gate_andor_lmlw': \<open>gate_andor_m S (map (\<lambda>x. lm (lw x)) ls) cj = gate_andor_m S ls cj\<close>
  using gate_andor_lmlw[of S ls cj] by (simp add: comp_def)

lemma nth_map1: \<open>Suc 0 \<le> length es \<Longrightarrow> map f es ! 0 = f (es ! 0)\<close>
  by (rule nth_map, linarith)

lemma length_implies: \<open>length (implies_lits_m es) = length es\<close>
  by (simp add: implies_lits_m_def)

lemma map_ne1: \<open>Suc 0 \<le> length es \<Longrightarrow> map f es \<noteq> []\<close>
  by auto

lemma upt_last_lt: \<open>\<not> Suc i < n \<Longrightarrow> i < n \<Longrightarrow> [0..<n] = [0..<i] @ [i]\<close>
  by (metis less_SucE not_less_eq upt_Suc_append zero_le)

lemma ne1: \<open>Suc 0 \<le> length es \<Longrightarrow> es \<noteq> []\<close>
  by auto

lemma take_Suc_map_upt: \<open>Suc i < n \<Longrightarrow> take (Suc i) (map g [0..<n]) = take i (map g [0..<n]) @ [g i]\<close>
  by (simp add: take_Suc_conv_app_nth)

lemma nth_map_Suc: \<open>Suc i < length es \<Longrightarrow> map f es ! i = f (es ! i)\<close>
  by simp

lemma nth_map3: \<open>3 \<le> length es \<Longrightarrow> map f es ! 0 = f (es ! 0)\<close> \<open>3 \<le> length es \<Longrightarrow> map f es ! Suc 0 = f (es ! Suc 0)\<close>
  \<open>3 \<le> length es \<Longrightarrow> map f es ! 2 = f (es ! 2)\<close>
  by (rule nth_map, linarith)+

lemma lm_wn_enc: \<open>lm (word_of_nat (fst (enc_lit_m (encm e))), snd (enc_lit_m (encm e)), TNil) = enc_lit_m (encm e)\<close>
  using lm_lw_enc[of e] by (simp add: lw_def)

lemma abnd_ite_r: \<open>abnd (st_of s) SmtOp_Ite (map encm es) \<Longrightarrow> is_lit_m (encm (es ! Suc 0)) \<Longrightarrow> 3 \<le> length es \<Longrightarrow>
  unat (Tr_next_fun s) < 18446744073709551615\<close>
  using nth_map3(2)[of es encm] by (simp add: abnd_def bnd_def gate_ite_next st_of_def)

lemma ite_R:
  assumes \<open>abnd (st_of s) SmtOp_Ite (map encm es)\<close> \<open>\<not> is_lit_m (encm (es ! Suc 0))\<close> \<open>3 \<le> length es\<close>
  shows \<open>unat (Tr_next_fun s) < 18446744073709551615\<close>
    \<open>st_of (make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []]) (Tr_atoms s) (Tr_clauses s) (Tr_next_fun s + 1)) =
       fst (new_const_m (st_of s))\<close>
    \<open>bnd (fst (enc_term_m (fst (new_const_m (st_of s))) (encm (es ! Suc 0))))\<close>
    \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst (new_const_m (st_of s))) (encm (es ! Suc 0)))) (encm (es ! 2))))\<close>
proof -
  have n1: \<open>map encm es ! Suc 0 = encm (es ! Suc 0)\<close> \<open>map encm es ! 2 = encm (es ! 2)\<close> using assms(3) by simp_all
  have b: \<open>bnd (fst (ite_term_m (st_of s) (map encm es)))\<close>
    using assms(1,2) n1 by (simp add: abnd_def)
  note F = ite_term_facts[OF b]
  show u: \<open>unat (Tr_next_fun s) < 18446744073709551615\<close> using F(1) by (simp add: st_of_def)
  show \<open>st_of (make_Tr (Tr_terms s @ [make_Term (Tr_next_fun s) []]) (Tr_atoms s) (Tr_clauses s) (Tr_next_fun s + 1)) =
       fst (new_const_m (st_of s))\<close> using u by (simp add: st_of_def new_const_eq unat_r1)
  show \<open>bnd (fst (enc_term_m (fst (new_const_m (st_of s))) (encm (es ! Suc 0))))\<close> using F(2) n1 by simp
  show \<open>bnd (fst (enc_term_m (fst (enc_term_m (fst (new_const_m (st_of s))) (encm (es ! Suc 0)))) (encm (es ! 2))))\<close>
    using F(3) n1 by simp
qed

lemma ares_andor:
  \<open>ares S SmtOp_And es = (tr_of (fst (gate_andor_m S (map enc_lit_m es) True)), enc_of (snd (gate_andor_m S (map enc_lit_m es) True)), TNil)\<close>
  \<open>ares S SmtOp_Or es = (tr_of (fst (gate_andor_m S (map enc_lit_m es) False)), enc_of (snd (gate_andor_m S (map enc_lit_m es) False)), TNil)\<close>
  \<open>ares S SmtOp_Implies es = (tr_of (fst (gate_andor_m S (implies_lits_m es) False)), enc_of (snd (gate_andor_m S (implies_lits_m es) False)), TNil)\<close>
  by (simp_all add: ares_def)

lemma ares_eq:
  \<open>ares S SmtOp_Eq es = (tr_of (fst (enc_eq_m S es False)), enc_of (snd (enc_eq_m S es False)), TNil)\<close>
  \<open>ares S SmtOp_Distinct es = (tr_of (fst (enc_eq_m S es True)), enc_of (snd (enc_eq_m S es True)), TNil)\<close>
  \<open>abnd S SmtOp_Eq es = bnd (fst (enc_eq_m S es False))\<close>
  \<open>abnd S SmtOp_Distinct es = bnd (fst (enc_eq_m S es True))\<close>
  by (simp_all add: ares_def abnd_def)

lemma ares_not: \<open>ares S SmtOp_Not es = (tr_of S, enc_of (ELit (fst (enc_lit_m (es ! 0))) (\<not> snd (enc_lit_m (es ! 0)))), TNil)\<close>
  by (simp add: ares_def)

lemma ares_xor: \<open>es \<noteq> [] \<Longrightarrow> ares S SmtOp_Xor es =
  (tr_of (fst (XF es S (length es - 1))), enc_of (ELit (fst (snd (XF es S (length es - 1)))) (snd (snd (XF es S (length es - 1))))), TNil)\<close>
  by (simp add: ares_def XF_def Let_def)

lemma abnd_xor: \<open>abnd S SmtOp_Xor es = bnd (fst (enc_app_m S SmtOp_Xor es))\<close>
  by (simp add: abnd_def)

lemma ares_ite:
  \<open>ares S SmtOp_Ite es =
     (if is_lit_m (es ! 1)
      then (tr_of (fst (gate_ite_m S (enc_lit_m (es ! 0)) (enc_lit_m (es ! 1)) (enc_lit_m (es ! 2)))),
            enc_of (snd (gate_ite_m S (enc_lit_m (es ! 0)) (enc_lit_m (es ! 1)) (enc_lit_m (es ! 2)))), TNil)
      else (tr_of (fst (ite_term_m S es)), enc_of (snd (ite_term_m S es)), TNil))\<close>
  by (simp add: ares_def)

lemma abnd_ite:
  \<open>abnd S SmtOp_Ite es \<Longrightarrow> is_lit_m (es ! 1) \<Longrightarrow> st_next S < 18446744073709551615\<close>
  \<open>abnd S SmtOp_Ite es \<Longrightarrow> \<not> is_lit_m (es ! 1) \<Longrightarrow> bnd (fst (ite_term_m S es))\<close>
  by (simp_all add: abnd_def bnd_def gate_ite_next)

lemma ares_other: \<open>\<not> smt_core_op op \<Longrightarrow> ares S op es = (tr_of S, Enc_Lit 0 True, TNil)\<close>
  by (cases op) (simp_all add: ares_def)

definition enc_app_contract :: \<open>Tr \<Rightarrow> SmtOp \<Rightarrow> Enc list \<Rightarrow> ('s, Tr \<times> Enc \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>enc_app_contract s op es \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>min_ar op \<le> length es \<and> length es < 2 ^ 64 \<and> length es \<le> urust_fuel \<and> length es * length es \<le> urust_fuel \<and>
         abnd (st_of s) op (map encm es)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = ares (st_of s) op (map encm es)\<rangle>)\<close>

lemma enc_app_spec [crush_specs]:
  shows \<open>\<Gamma>; enc_app s op es \<Turnstile>\<^sub>F enc_app_contract s op es\<close>
  proof (cases \<open>smt_core_op op\<close>)
  case False
  then show ?thesis
    apply (cases op; simp)
    apply (crush_boot f: enc_app_def contract: enc_app_contract_def, crush_base simp add: ares_other tr_st_of)+
    done
next
  case True
  then show ?thesis
  proof (cases op)
    case SmtOp_Not
    show ?thesis unfolding SmtOp_Not
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base simp add: ares_not tr_st_of lw_def)
      apply (cases es; simp)+
      done
  next
    case SmtOp_And
    show ?thesis unfolding SmtOp_And
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base inline: len_def)
      subgoal for ls_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length es \<and> lv = map (\<lambda>e. lw (enc_lit_m (encm e))) (take (unat i) es) \<and> length es - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length es \<and> lv = map (\<lambda>e. lw (enc_lit_m (encm e))) (take (unat i) es) \<and> length es - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
            take_Suc_conv_app_nth ares_andor abnd_andor comp_def lm_lw_enc)
        done
      done
  next
    case SmtOp_Or
    show ?thesis unfolding SmtOp_Or
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base inline: len_def)
      subgoal for ls_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length es \<and> lv = map (\<lambda>e. lw (enc_lit_m (encm e))) (take (unat i) es) \<and> length es - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length es \<and> lv = map (\<lambda>e. lw (enc_lit_m (encm e))) (take (unat i) es) \<and> length es - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
            take_Suc_conv_app_nth ares_andor abnd_andor comp_def lm_lw_enc)
        done
      done
  next
    case SmtOp_Xor
    show ?thesis unfolding SmtOp_Xor
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base inline: len_def)
      subgoal for s_ref acc_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gs sv ga av gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>1 \<le> unat i \<and> unat i \<le> length es \<and> sv = tr_of (fst (XF (map encm es) (st_of s) (unat i - 1))) \<and>
                av = lw (snd (XF (map encm es) (st_of s) (unat i - 1))) \<and> length es - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gs sv ga av gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> acc_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               can_alloc_reference \<star>
               \<langle>1 \<le> unat i \<and> unat i < length es \<and> sv = tr_of (fst (XF (map encm es) (st_of s) (unat i - 1))) \<and>
                av = lw (snd (XF (map encm es) (st_of s) (unat i - 1))) \<and> length es - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound XF_0 nth_map1 tr_st_of)
        apply (simp_all add: unat_plus_one_of_less_bound[where n=\<open>length es\<close>] XF_step XF_facts st_tr_of_bnd lm_lw lm_lw_enc
            unat_next_tr_of bnd_next ares_xor map_ne1)
        apply (simp add: ares_xor ne1 lw_def)
        done
      done
  next
    case SmtOp_Implies
    show ?thesis unfolding SmtOp_Implies
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base inline: len_def)
      subgoal for ls_ref i_ref
        apply (ucincl_discharge\<open>rule_tac
          INV=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length es \<and> lv = map lw (take (unat i) (implies_lits_m (map encm es))) \<and> length es - unat i \<le> c\<rangle>\<close> and
          INV'=\<open>\<lambda>c. \<Squnion>gl lv gi i. ls_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>lv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length es \<and> lv = map lw (take (unat i) (implies_lits_m (map encm es))) \<and> length es - unat i \<le> Suc c\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
            implies_take_Suc ares_andor abnd_andor length_implies gate_andor_lmlw)
        apply (simp_all add: unat_plus_one_of_less_bound[where n=\<open>length es\<close>] implies_lits_m_def upt_last_lt lw_def)
        apply (simp add: take_Suc_map_upt nth_map_Suc lw_def)
        done
      done
  next
    case SmtOp_Eq
    show ?thesis unfolding SmtOp_Eq
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base simp add: ares_eq)
      done
  next
    case SmtOp_Distinct
    show ?thesis unfolding SmtOp_Distinct
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base simp add: ares_eq)
      done
  next
    case SmtOp_Ite
    show ?thesis unfolding SmtOp_Ite
      apply (crush_boot f: enc_app_def contract: enc_app_contract_def)
      apply (crush_base simp add: ares_ite)
      apply (simp_all add: ite_R abnd_ite_r nth_map3 st_tr_of_bnd bnd_next unat_next_tr_of tr_of_sel lw_def lm_wn_enc)
      apply (simp_all add: ite_term_m_def Let_def new_const_eq st_of_def nth_map3 add_atom_m_def add_clause_m_def
          tr_of_def lit_m_def)
      done
  qed (use True in simp_all)
qed

subsection \<open>The recursion of \<^verbatim>\<open>enc\<close> in closed form\<close>

text \<open>The bound and the results of \<^verbatim>\<open>enc\<close> and \<^verbatim>\<open>enc_args\<close> as constants, so that the simplifier
  does not unfold \<^const>\<open>tr_term_m\<close> in the contracts.\<close>
definition tbnd :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>tbnd p dm env n S t \<equiv> bnd (fst (tr_term_m p dm env n S t))\<close>

definition sbnd :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm list \<Rightarrow> bool\<close> where
  \<open>sbnd p dm env n S ts \<equiv> bnd (fst (tr_args_m p dm env n S ts))\<close>

definition tres :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm \<Rightarrow> Tr \<times> Enc \<times> tnil\<close> where
  \<open>tres p dm env n S t \<equiv> (tr_of (fst (tr_term_m p dm env n S t)), enc_of (snd (tr_term_m p dm env n S t)), TNil)\<close>

definition sres :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm list \<Rightarrow> Tr \<times> Enc list \<times> tnil\<close> where
  \<open>sres p dm env n S ts \<equiv> (tr_of (fst (tr_args_m p dm env n S ts)), map enc_of (snd (tr_args_m p dm env n S ts)), TNil)\<close>

lemma tr_args_append:
  \<open>tr_args_m p dm env n S (xs @ ys) =
     (fst (tr_args_m p dm env n (fst (tr_args_m p dm env n S xs)) ys),
      snd (tr_args_m p dm env n S xs) @ snd (tr_args_m p dm env n (fst (tr_args_m p dm env n S xs)) ys))\<close>
  by (induction xs arbitrary: S) (simp_all add: Let_def)

lemma tr_args_take_Suc: \<open>i < length ts \<Longrightarrow> tr_args_m p dm env n S (take (Suc i) ts) =
  (fst (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)),
   snd (tr_args_m p dm env n S (take i ts)) @ [snd (tr_term_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i))])\<close>
  by (simp add: take_Suc_conv_app_nth tr_args_append Let_def)

lemma tr_args_len: \<open>length (snd (tr_args_m p dm env n S ts)) = length ts\<close>
  using tr_pre(2)[of p dm env n S ts] by (cases \<open>tr_args_m p dm env n S ts\<close>) simp

lemma tr_args_pre_take: \<open>pre (fst (tr_args_m p dm env n S (take i ts))) (fst (tr_args_m p dm env n S ts))\<close>
proof -
  have e: \<open>fst (tr_args_m p dm env n S ts) = fst (tr_args_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (drop i ts))\<close>
    using tr_args_append[of p dm env n S \<open>take i ts\<close> \<open>drop i ts\<close>] by simp
  show ?thesis unfolding e
    using tr_pre(2)[of p dm env n \<open>fst (tr_args_m p dm env n S (take i ts))\<close> \<open>drop i ts\<close>]
    by (cases \<open>tr_args_m p dm env n (fst (tr_args_m p dm env n S (take i ts))) (drop i ts)\<close>) simp
qed

lemma args_bnd:
  \<open>sbnd p dm env n S ts \<Longrightarrow> bnd (fst (tr_args_m p dm env n S (take i ts)))\<close>
  \<open>sbnd p dm env n S ts \<Longrightarrow> i < length ts \<Longrightarrow> tbnd p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)\<close>
proof -
  show \<open>sbnd p dm env n S ts \<Longrightarrow> bnd (fst (tr_args_m p dm env n S (take i ts)))\<close>
    unfolding sbnd_def by (rule bnd_pre[OF tr_args_pre_take])
  assume a: \<open>sbnd p dm env n S ts\<close> \<open>i < length ts\<close>
  have \<open>bnd (fst (tr_args_m p dm env n S (take (Suc i) ts)))\<close> using a(1) unfolding sbnd_def by (rule bnd_pre[OF tr_args_pre_take])
  then show \<open>tbnd p dm env n (fst (tr_args_m p dm env n S (take i ts))) (ts ! i)\<close>
    using a(2) by (simp add: tbnd_def tr_args_take_Suc)
qed

lemma sres_take: \<open>i < length ts \<Longrightarrow> bnd (fst (tr_args_m p dm env n S (take i ts))) \<Longrightarrow>
  sres p dm env n S (take (Suc i) ts) =
  (fst (tres p dm env n (st_of (tr_of (fst (tr_args_m p dm env n S (take i ts))))) (ts ! i)),
   map enc_of (snd (tr_args_m p dm env n S (take i ts))) @ [fst (snd (tres p dm env n (st_of (tr_of (fst (tr_args_m p dm env n S (take i ts))))) (ts ! i)))],
   TNil)\<close>
  by (simp add: sres_def tres_def tr_args_take_Suc st_tr_of_bnd)

definition ET :: \<open>st \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<times> nat list\<close> where
  \<open>ET S es i \<equiv> foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (S, []) (take i es)\<close>

lemma ET_0: \<open>ET S es 0 = (S, [])\<close>
  by (simp add: ET_def)

lemma ET_Suc: \<open>i < length es \<Longrightarrow> ET S es (Suc i) =
  (fst (enc_term_m (fst (ET S es i)) (es ! i)), snd (ET S es i) @ [snd (enc_term_m (fst (ET S es i)) (es ! i))])\<close>
  by (simp add: ET_def take_Suc_conv_app_nth split_def Let_def)

lemma ET_all: \<open>n = length es \<Longrightarrow> ET S es n = enc_terms_m S es\<close>
  by (simp add: ET_def enc_terms_m_def)

lemma ET_pre: \<open>pre (fst (ET S es i)) (fst (enc_terms_m S es))\<close>
proof -
  have \<open>enc_terms_m S es = foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (ET S es i) (drop i es)\<close>
    unfolding ET_def enc_terms_m_def by (metis append_take_drop_id foldl_append)
  then show ?thesis using pre_enc_terms[OF pre_refl, of \<open>ET S es i\<close> \<open>drop i es\<close>] by simp
qed

lemma ET_len: \<open>i \<le> length es \<Longrightarrow> length (snd (ET S es i)) = i\<close>
proof (induction i)
  case 0
  then show ?case by (simp add: ET_0)
next
  case (Suc i)
  then show ?case by (simp add: ET_Suc)
qed

text \<open>The facts the Rust function uses for an application of a declared symbol.\<close>
lemma fun_facts:
  assumes \<open>tbnd p dm env n S (SmtTerm_Fun f args)\<close>
  shows \<open>sbnd p dm env n S args\<close>
    \<open>i \<le> length args \<Longrightarrow> bnd (fst (ET (fst (tr_args_m p dm env n S args)) (snd (tr_args_m p dm env n S args)) i))\<close>
    \<open>i < length args \<Longrightarrow> bnd (fst (ET (fst (tr_args_m p dm env n S args)) (snd (tr_args_m p dm env n S args)) i))\<close>
    \<open>i < length args \<Longrightarrow> st_next (fst (enc_term_m (fst (ET (fst (tr_args_m p dm env n S args)) (snd (tr_args_m p dm env n S args)) i))
        (snd (tr_args_m p dm env n S args) ! i))) < 18446744073709551616\<close>
proof -
  let ?A = \<open>tr_args_m p dm env n S args\<close>
  let ?E = \<open>enc_terms_m (fst ?A) (snd ?A)\<close>
  let ?T = \<open>add_term_m (fst ?E) (unat f) (snd ?E)\<close>
  have pE: \<open>pre (fst ?E) (fst (tr_term_m p dm env n S (SmtTerm_Fun f args)))\<close>
    by (auto simp: Let_def intro: pre_add_atom pre_add_term pre_refl)
  have bE: \<open>bnd (fst ?E)\<close> using bnd_pre[OF pE] assms by (simp add: tbnd_def)
  have pA: \<open>pre (fst ?A) (fst ?E)\<close> using pre_enc_terms[OF pre_refl, of \<open>(fst ?A, [])\<close> \<open>snd ?A\<close>] by (simp add: enc_terms_m_def)
  show \<open>sbnd p dm env n S args\<close> using bnd_pre[OF pA bE] by (simp add: sbnd_def)
  have l: \<open>length (snd ?A) = length args\<close> by (rule tr_args_len)
  show \<open>bnd (fst (ET (fst ?A) (snd ?A) i))\<close> if \<open>i \<le> length args\<close> for i
    using bnd_pre[OF ET_pre bE] .
  show \<open>bnd (fst (ET (fst ?A) (snd ?A) i))\<close> if \<open>i < length args\<close> for i
    using bnd_pre[OF ET_pre bE] .
  show \<open>st_next (fst (enc_term_m (fst (ET (fst ?A) (snd ?A) i)) (snd ?A ! i))) < 18446744073709551616\<close> if \<open>i < length args\<close> for i
  proof -
    have \<open>bnd (fst (ET (fst ?A) (snd ?A) (Suc i)))\<close> using bnd_pre[OF ET_pre bE] .
    then show ?thesis using that l by (simp add: ET_Suc bnd_def)
  qed
qed

lemma fun_ib:
  assumes \<open>toks p F dl el n args\<close> \<open>length env = el\<close> \<open>\<forall>e \<in> set env. ib e\<close> \<open>dl \<le> length dm\<close> \<open>\<forall>e \<in> set dm. ib e\<close>
    \<open>sbnd p dm env n S args\<close> \<open>i < length args\<close>
  shows \<open>encm (enc_of (snd (tr_args_m p dm env n S args) ! i)) = snd (tr_args_m p dm env n S args) ! i\<close>
proof -
  have \<open>\<forall>e \<in> set (snd (tr_args_m p dm env n S args)). ib e\<close>
    using tr_ib(2)[OF assms(1-5)] assms(6) by (simp add: sbnd_def)
  moreover have \<open>i < length (snd (tr_args_m p dm env n S args))\<close> using assms(7) tr_args_len by metis
  ultimately show ?thesis by (simp add: encm_enc_of)
qed

lemma tres_fun:
  \<open>tres p dm env n S (SmtTerm_Fun f args) =
     (let A = tr_args_m p dm env n S args; E = ET (fst A) (snd A) (length args); T = add_term_m (fst E) (unat f) (snd E) in
      if SmtFun_ret (SmtProblem_funs p ! unat f) = SmtSort_Bool
      then (tr_of (fst (add_atom_m (fst T) (snd T) 0)), Enc_Lit (word_of_nat (snd (add_atom_m (fst T) (snd T) 0))) True, TNil)
      else (tr_of (fst T), Enc_Term (word_of_nat (snd T)), TNil))\<close>
  by (simp add: tres_def Let_def ET_all tr_args_len)

lemma tres_simple:
  \<open>tres p dm env n S (SmtTerm_BoolConst b) = (tr_of S, Enc_Lit 0 b, TNil)\<close>
  \<open>tres p dm env n S (SmtTerm_BvConst bs) = (tr_of S, Enc_Lit 0 True, TNil)\<close>
  \<open>tres p dm env n S (SmtTerm_Param k) = (tr_of S, enc_of (env ! unat k), TNil)\<close>
  by (simp_all add: tres_def)

lemma tres_app:
  \<open>tres p dm env n S (SmtTerm_App op args) =
     ares (fst (tr_args_m p dm env n S args)) op (snd (tr_args_m p dm env n S args))\<close>
  by (simp add: tres_def ares_def Let_def)

lemma tbnd_app:
  \<open>tbnd p dm env n S (SmtTerm_App op args) = abnd (fst (tr_args_m p dm env n S args)) op (snd (tr_args_m p dm env n S args))\<close>
  by (simp add: tbnd_def abnd_def Let_def)

lemma sbnd_app: \<open>tbnd p dm env n S (SmtTerm_App op args) \<Longrightarrow> sbnd p dm env n S args\<close>
  unfolding tbnd_def sbnd_def using bnd_pre[OF pre_enc_app[OF pre_refl]] by (simp add: Let_def)

lemma tres_def0:
  \<open>SmtDef_params (SmtProblem_defs p ! unat d) = [] \<Longrightarrow> tres p dm env n S (SmtTerm_Def d args) = (tr_of S, enc_of (dm ! unat d), TNil)\<close>
  by (simp add: tres_def)

lemma tres_def1:
  \<open>SmtDef_params (SmtProblem_defs p ! unat d) \<noteq> [] \<Longrightarrow> unat d < n \<Longrightarrow> tres p dm env n S (SmtTerm_Def d args) =
     tres p dm (snd (tr_args_m p dm env n S args)) (unat d) (fst (tr_args_m p dm env n S args)) (SmtDef_body (SmtProblem_defs p ! unat d))\<close>
  by (simp add: tres_def Let_def)

lemma tbnd_def1:
  \<open>SmtDef_params (SmtProblem_defs p ! unat d) \<noteq> [] \<Longrightarrow> unat d < n \<Longrightarrow> tbnd p dm env n S (SmtTerm_Def d args) =
     tbnd p dm (snd (tr_args_m p dm env n S args)) (unat d) (fst (tr_args_m p dm env n S args)) (SmtDef_body (SmtProblem_defs p ! unat d))\<close>
  by (simp add: tbnd_def Let_def)

lemma sbnd_def1:
  \<open>SmtDef_params (SmtProblem_defs p ! unat d) \<noteq> [] \<Longrightarrow> unat d < n \<Longrightarrow> tbnd p dm env n S (SmtTerm_Def d args) \<Longrightarrow>
     sbnd p dm env n S args\<close>
proof -
  assume a: \<open>SmtDef_params (SmtProblem_defs p ! unat d) \<noteq> []\<close> \<open>unat d < n\<close> \<open>tbnd p dm env n S (SmtTerm_Def d args)\<close>
  let ?A = \<open>tr_args_m p dm env n S args\<close>
  let ?b = \<open>SmtDef_body (SmtProblem_defs p ! unat d)\<close>
  have \<open>pre (fst ?A) (fst (tr_term_m p dm (snd ?A) (unat d) (fst ?A) ?b))\<close>
    using tr_pre(1)[of p dm \<open>snd ?A\<close> \<open>unat d\<close> \<open>fst ?A\<close> ?b] by (cases \<open>tr_term_m p dm (snd ?A) (unat d) (fst ?A) ?b\<close>) simp
  then show ?thesis using a bnd_pre by (simp add: tbnd_def sbnd_def Let_def)
qed

lemma wn_len_0: \<open>length xs < 2 ^ 64 \<Longrightarrow> ((word_of_nat (length xs) :: 64 word) = 0) = (xs = [])\<close>
  by (auto simp: word_of_nat_eq_0_iff dest: nat_dvd_not_less)


subsection \<open>\<^verbatim>\<open>enc_args\<close> and \<^verbatim>\<open>enc\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of the mutual recursion. Definitions are expanded below the number of
  definitions of \<open>p\<close>; the tables \<^verbatim>\<open>dm\<close> and \<^verbatim>\<open>env\<close> are read through \<^const>\<open>encm\<close>.\<close>
definition enc_args_contract ::
  \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> Enc list \<Rightarrow> Enc list \<Rightarrow> Tr \<Rightarrow> SmtTerm list \<Rightarrow> ('s, Tr \<times> Enc list \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>enc_args_contract k p dm env s ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (deps p (length (SmtProblem_defs p)) ts) \<le> k \<and> length ts < 2 ^ 64 \<and> length ts \<le> urust_fuel \<and>
         toks p urust_fuel (length dm) (length env) (length (SmtProblem_defs p)) ts \<and>
         sbnd p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) ts\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = sres p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) ts\<rangle>)\<close>

definition enc_contract ::
  \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> Enc list \<Rightarrow> Enc list \<Rightarrow> Tr \<Rightarrow> SmtTerm \<Rightarrow> ('s, Tr \<times> Enc \<times> tnil, 'abort) function_contract\<close>
  where
  [crush_contracts]: \<open>enc_contract k p dm env s t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (dep p (length (SmtProblem_defs p)) t) \<le> k \<and>
         tok p urust_fuel (length dm) (length env) (length (SmtProblem_defs p)) t \<and>
         tbnd p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = tres p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) t\<rangle>)\<close>

lemma enc_args_step_spec:
  assumes IH2: \<open>\<And>p dm env s t. \<Gamma>; g p dm env s t \<Turnstile>\<^sub>F enc_contract k p dm env s t\<close>
  shows \<open>\<Gamma>; fst (enc_args_rec_step (f, g)) p dm env s ts \<Turnstile>\<^sub>F enc_args_contract (Suc k) p dm env s ts\<close>
  apply (crush_boot f: enc_args_rec_step_def contract: enc_args_contract_def)
  apply (crush_base inline: len_def)
  subgoal for s_ref es_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gs sv ge ev gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> es_ref \<mapsto>\<langle>\<top>\<rangle> ge\<down>ev \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i \<le> length ts \<and>
            sv = tr_of (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) (take (unat i) ts))) \<and>
            ev = map enc_of (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) (take (unat i) ts))) \<and>
            length ts - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gs sv ge ev gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> es_ref \<mapsto>\<langle>\<top>\<rangle> ge\<down>ev \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           can_alloc_reference \<star>
           \<langle>unat i < length ts \<and>
            sv = tr_of (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) (take (unat i) ts))) \<and>
            ev = map enc_of (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) (take (unat i) ts))) \<and>
            length ts - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def specs add: IH2 contracts add: enc_contract_def
        simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound deps_nth toks_nth tr_st_of)
    apply (simp_all add: st_tr_of_bnd args_bnd sres_def tres_def tr_args_take_Suc)
    done
  done

lemma sbnd_bnd: \<open>sbnd p dm env n S ts \<Longrightarrow> bnd (fst (tr_args_m p dm env n S ts))\<close>
  by (simp add: sbnd_def)

lemma map_encm_args:
  \<open>toks p F dl el n args \<Longrightarrow> length env = el \<Longrightarrow> \<forall>e \<in> set env. ib e \<Longrightarrow> dl \<le> length dm \<Longrightarrow> \<forall>e \<in> set dm. ib e \<Longrightarrow>
   sbnd p dm env n S args \<Longrightarrow> map encm (map enc_of (snd (tr_args_m p dm env n S args))) = snd (tr_args_m p dm env n S args)\<close>
  using tr_ib(2)[of p F dl el n args env dm S] map_encm_enc_of[of \<open>snd (tr_args_m p dm env n S args)\<close>]
  by (simp add: sbnd_def)

lemma sres_sel: \<open>fst (sres p dm env n S ts) = tr_of (fst (tr_args_m p dm env n S ts))\<close>
  \<open>fst (snd (sres p dm env n S ts)) = map enc_of (snd (tr_args_m p dm env n S ts))\<close>
  by (simp_all add: sres_def)

lemma map_encm_args':
  \<open>toks p F dl el n args \<Longrightarrow> length env = el \<Longrightarrow> \<forall>e \<in> set env. ib e \<Longrightarrow> dl \<le> length dm \<Longrightarrow> \<forall>e \<in> set dm. ib e \<Longrightarrow>
   bnd (fst (tr_args_m p dm env n S args)) \<Longrightarrow> map (encm \<circ> enc_of) (snd (tr_args_m p dm env n S args)) = snd (tr_args_m p dm env n S args)\<close>
  using map_encm_args[of p F dl el n args env dm S] by (simp add: sbnd_def)

lemma bnd_args_app: \<open>abnd (fst (tr_args_m p dm env n S args)) op (snd (tr_args_m p dm env n S args)) \<Longrightarrow>
  bnd (fst (tr_args_m p dm env n S args))\<close>
  using bnd_pre[OF pre_enc_app[OF pre_refl]] by (simp add: abnd_def)

lemma bnd_args_def1: \<open>tbnd p dm (snd (tr_args_m p dm env n S args)) m (fst (tr_args_m p dm env n S args)) b \<Longrightarrow>
  bnd (fst (tr_args_m p dm env n S args))\<close>
proof -
  let ?A = \<open>tr_args_m p dm env n S args\<close>
  assume a: \<open>tbnd p dm (snd ?A) m (fst ?A) b\<close>
  have \<open>pre (fst ?A) (fst (tr_term_m p dm (snd ?A) m (fst ?A) b))\<close>
    using tr_pre(1)[of p dm \<open>snd ?A\<close> m \<open>fst ?A\<close> b] by (cases \<open>tr_term_m p dm (snd ?A) m (fst ?A) b\<close>) simp
  then show ?thesis using a bnd_pre by (simp add: tbnd_def)
qed

lemma enc_step_spec:
  assumes IH1: \<open>\<And>p dm env s ts. \<Gamma>; f p dm env s ts \<Turnstile>\<^sub>F enc_args_contract k p dm env s ts\<close>
      and IH2: \<open>\<And>p dm env s t. \<Gamma>; g p dm env s t \<Turnstile>\<^sub>F enc_contract k p dm env s t\<close>
  shows \<open>\<Gamma>; snd (enc_args_rec_step (f, g)) p dm env s t \<Turnstile>\<^sub>F enc_contract (Suc k) p dm env s t\<close>
  proof (cases t)
  case (SmtTerm_BoolConst b)
  show ?thesis unfolding SmtTerm_BoolConst
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base simp add: tres_simple tr_st_of)
    done
next
  case (SmtTerm_BvConst bs)
  show ?thesis unfolding SmtTerm_BvConst
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base simp add: tres_simple tr_st_of)
    done
next
  case (SmtTerm_Param i)
  show ?thesis unfolding SmtTerm_Param
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base simp add: tres_simple tr_st_of enc_of_encm)
    done
next
  case (SmtTerm_Def d args)
  let ?b = \<open>SmtDef_body (SmtProblem_defs p ! unat d)\<close>
  let ?L = \<open>length (SmtProblem_defs p)\<close>
  have E: \<open>tres p dm' env' ?L S' ?b = tres p dm' env' (unat d) S' ?b\<close>
    \<open>tbnd p dm' env' ?L S' ?b = tbnd p dm' env' (unat d) S' ?b\<close>
    \<open>dep p ?L ?b = dep p (unat d) ?b\<close>
    \<open>tok p urust_fuel dl (length args) ?L ?b\<close>
    if \<open>tok p urust_fuel dl (length args) (unat d) ?b\<close> \<open>unat d < ?L\<close> for dm' env' S' dl
    using tok_n_indep(1)[OF that(1), of ?L dm' env' S'] that(2) by (simp_all add: tres_def tbnd_def)
  show ?thesis unfolding SmtTerm_Def
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base specs add: IH1 IH2 contracts add: enc_contract_def enc_args_contract_def
        simp add: wn_len_0 tres_def0 tres_def1 tbnd_def1 sbnd_def1 tr_st_of enc_of_encm)
    apply (simp_all add: sres_sel st_tr_of_bnd bnd_args_def1 map_encm_args' ib_encm tr_args_len E)
    done
next
  case (SmtTerm_App op args)
  show ?thesis unfolding SmtTerm_App
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base specs add: IH1 IH2 contracts add: enc_contract_def enc_args_contract_def
        simp add: tres_app tbnd_app sbnd_app)
    apply (simp_all add: sres_sel st_tr_of_bnd bnd_args_app map_encm_args' ib_encm tr_args_len)
    done
next
  case (SmtTerm_Fun fn args)
  show ?thesis unfolding SmtTerm_Fun
    apply (crush_boot f: enc_args_rec_step_def contract: enc_contract_def)
    apply (crush_base specs add: IH1 IH2 contracts add: enc_contract_def enc_args_contract_def
        simp add: fun_facts(1) sres_sel tr_args_len)
    subgoal for s_ref ts_ref i_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gs sv gt tv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ts_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>tv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             can_alloc_reference \<star>
             \<langle>unat i \<le> length args \<and> sv = tr_of (fst (ET (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (unat i))) \<and>
              tv = map word_of_nat (snd (ET (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (unat i))) \<and> length args - unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gs sv gt tv gi i. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> ts_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>tv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             can_alloc_reference \<star>
             \<langle>unat i < length args \<and> sv = tr_of (fst (ET (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (unat i))) \<and>
              tv = map word_of_nat (snd (ET (fst (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (snd (tr_args_m p (map encm dm) (map encm env) (length (SmtProblem_defs p)) (st_of s) args)) (unat i))) \<and> length args - unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def
          simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound ET_0 ET_Suc sres_sel tr_args_len
          split: SmtSort.splits)
      apply (simp_all add: st_tr_of_bnd fun_facts fun_ib ib_encm)
      apply (simp_all add: tres_fun Let_def add_term_m_def add_atom_m_def tr_of_sel)
      apply (simp_all add: tr_of_def)
      done
    done
qed

lemma enc_rec_spec:
  shows \<open>(\<forall>p dm env s ts. \<Gamma>; fst ((enc_args_rec_step ^^ k) h) p dm env s ts \<Turnstile>\<^sub>F enc_args_contract k p dm env s ts) \<and>
         (\<forall>p dm env s t. \<Gamma>; snd ((enc_args_rec_step ^^ k) h) p dm env s t \<Turnstile>\<^sub>F enc_contract k p dm env s t)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: enc_args_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: enc_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(enc_args_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(enc_args_rec_step ^^ k) h\<close>)
  have I1: \<open>\<And>p dm env s ts. \<Gamma>; f p dm env s ts \<Turnstile>\<^sub>F enc_args_contract k p dm env s ts\<close>
    and I2: \<open>\<And>p dm env s t. \<Gamma>; g p dm env s t \<Turnstile>\<^sub>F enc_contract k p dm env s t\<close>
    using Suc.IH fg by simp_all
  show ?case
    using enc_args_step_spec[OF I2] enc_step_spec[OF I1 I2] unfolding funpow.simps(2) comp_def fg by simp
qed

lemma enc_args_spec [crush_specs]:
  shows \<open>\<Gamma>; enc_args p dm env s ts \<Turnstile>\<^sub>F enc_args_contract urust_fuel p dm env s ts\<close>
  unfolding enc_args_def using enc_rec_spec by blast

lemma enc_spec [crush_specs]:
  shows \<open>\<Gamma>; enc p dm env s t \<Turnstile>\<^sub>F enc_contract urust_fuel p dm env s t\<close>
  unfolding enc_def using enc_rec_spec by blast

subsection \<open>\<^verbatim>\<open>tr_problem\<close>\<close>

text \<open>What \<^verbatim>\<open>tr_problem\<close> needs, for the fuel \<open>F\<close>.\<close>
definition tr_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> bool\<close> where
  \<open>tr_pre F p \<equiv>
     let ds = SmtProblem_defs p; L = length ds in
     length (SmtProblem_funs p) < 2 ^ 63 \<and> L < 2 ^ 64 \<and> L \<le> F \<and>
     length (SmtProblem_asserts p) < 2 ^ 64 \<and> length (SmtProblem_asserts p) \<le> F \<and>
     (\<forall>d < L. length (SmtDef_params (ds ! d)) < 2 ^ 64 \<and>
        (SmtDef_params (ds ! d) = [] \<longrightarrow> tok p F d 0 d (SmtDef_body (ds ! d)) \<and> Suc (dep p d (SmtDef_body (ds ! d))) \<le> F)) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). tok p F L 0 L t \<and> Suc (dep p L t) \<le> F) \<and>
     bnd (tr_state_m p)\<close>

definition TD :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> st \<times> enc_m list\<close> where
  \<open>TD p j \<equiv> foldl (tr_defs_step p) (tr_init_m p, []) [0..<j]\<close>

lemma TD_0: \<open>TD p 0 = (tr_init_m p, [])\<close>
  by (simp add: TD_def)

lemma TD_Suc: \<open>TD p (Suc j) = tr_defs_step p (TD p j) j\<close>
  by (simp add: TD_def)

lemma TD_len: \<open>length (snd (TD p j)) = j\<close>
  by (induction j) (simp_all add: TD_0 TD_Suc tr_defs_step_def split_def Let_def)

lemma TD_final: \<open>TD p (length (SmtProblem_defs p)) = tr_defs_m p\<close>
  by (simp add: TD_def tr_defs_m_def)

definition TA :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> st\<close> where
  \<open>TA p j \<equiv> foldl (tr_asserts_step p (snd (tr_defs_m p))) (fst (tr_defs_m p)) (take j (SmtProblem_asserts p))\<close>

lemma TA_0: \<open>TA p 0 = fst (tr_defs_m p)\<close>
  by (simp add: TA_def)

lemma TA_Suc: \<open>j < length (SmtProblem_asserts p) \<Longrightarrow> TA p (Suc j) = tr_asserts_step p (snd (tr_defs_m p)) (TA p j) (SmtProblem_asserts p ! j)\<close>
  by (simp add: TA_def take_Suc_conv_app_nth)

lemma TA_final: \<open>n = length (SmtProblem_asserts p) \<Longrightarrow> TA p n = tr_state_m p\<close>
  by (simp add: TA_def tr_state_m_def tr_asserts_m_def)

lemma pre_TA: \<open>pre (TA p j) (tr_state_m p)\<close>
proof -
  have \<open>tr_state_m p = foldl (tr_asserts_step p (snd (tr_defs_m p))) (TA p j) (drop j (SmtProblem_asserts p))\<close>
    unfolding TA_def tr_state_m_def tr_asserts_m_def by (metis append_take_drop_id foldl_append)
  then show ?thesis using pre_asserts by metis
qed

lemma pre_TD: \<open>j \<le> length (SmtProblem_defs p) \<Longrightarrow> pre (fst (TD p j)) (tr_state_m p)\<close>
proof -
  assume j: \<open>j \<le> length (SmtProblem_defs p)\<close>
  have \<open>tr_defs_m p = foldl (tr_defs_step p) (TD p j) [j..<length (SmtProblem_defs p)]\<close>
    unfolding TD_def tr_defs_m_def using j by (metis foldl_append upt_add_eq_append' zero_le)
  then have \<open>pre (fst (TD p j)) (fst (tr_defs_m p))\<close> using pre_defs by metis
  moreover have \<open>pre (fst (tr_defs_m p)) (tr_state_m p)\<close> using pre_TA[of p 0] by (simp add: TA_0)
  ultimately show ?thesis by (rule pre_trans)
qed

lemma TD_facts:
  assumes P: \<open>tr_pre F p\<close> and j: \<open>j \<le> length (SmtProblem_defs p)\<close>
  shows \<open>bnd (fst (TD p j)) \<and> (\<forall>e \<in> set (snd (TD p j)). ib e)\<close>
  using j
proof (induction j)
  case 0
  have \<open>bnd (tr_state_m p)\<close> using P by (simp add: tr_pre_def Let_def)
  then have \<open>bnd (fst (TD p 0))\<close> using bnd_pre[OF pre_TD[of 0 p]] by simp
  then show ?case by (simp add: TD_0)
next
  case (Suc j)
  let ?D = \<open>SmtProblem_defs p ! j\<close>
  have bS: \<open>bnd (fst (TD p (Suc j)))\<close> using bnd_pre[OF pre_TD[OF Suc.prems]] P by (simp add: tr_pre_def Let_def)
  have I: \<open>\<forall>e \<in> set (snd (TD p j)). ib e\<close> using Suc by simp
  have \<open>\<forall>e \<in> set (snd (TD p (Suc j))). ib e\<close>
  proof (cases \<open>SmtDef_params ?D = []\<close>)
    case True
    have t: \<open>tok p F j 0 j (SmtDef_body ?D)\<close> using P Suc.prems True by (simp add: tr_pre_def Let_def)
    let ?r = \<open>tr_term_m p (snd (TD p j)) [] j (fst (TD p j)) (SmtDef_body ?D)\<close>
    have e: \<open>TD p (Suc j) = (fst ?r, snd (TD p j) @ [snd ?r])\<close> using True by (simp add: TD_Suc tr_defs_step_def split_def Let_def)
    have \<open>ib (snd ?r)\<close> using tr_ib(1)[OF t _ _ _ I, of \<open>[]\<close> \<open>fst (TD p j)\<close>] bS e by (simp add: TD_len)
    then show ?thesis using e I by simp
  next
    case False
    then show ?thesis using I by (simp add: TD_Suc tr_defs_step_def split_def)
  qed
  then show ?case using bS by simp
qed

lemma tr_pre_facts:
  assumes P: \<open>tr_pre F p\<close>
  shows \<open>length (SmtProblem_funs p) < 2 ^ 63\<close> \<open>length (SmtProblem_defs p) < 2 ^ 64\<close> \<open>length (SmtProblem_defs p) \<le> F\<close>
    \<open>length (SmtProblem_asserts p) < 2 ^ 64\<close> \<open>length (SmtProblem_asserts p) \<le> F\<close>
    \<open>\<And>d. d < length (SmtProblem_defs p) \<Longrightarrow> length (SmtDef_params (SmtProblem_defs p ! d)) < 2 ^ 64\<close>
    \<open>\<And>d. d < length (SmtProblem_defs p) \<Longrightarrow> SmtDef_params (SmtProblem_defs p ! d) = [] \<Longrightarrow>
        tok p F d 0 (length (SmtProblem_defs p)) (SmtDef_body (SmtProblem_defs p ! d))\<close>
    \<open>\<And>d. d < length (SmtProblem_defs p) \<Longrightarrow> SmtDef_params (SmtProblem_defs p ! d) = [] \<Longrightarrow>
        Suc (dep p (length (SmtProblem_defs p)) (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close>
    \<open>\<And>d dm S. d < length (SmtProblem_defs p) \<Longrightarrow> SmtDef_params (SmtProblem_defs p ! d) = [] \<Longrightarrow>
        tr_term_m p dm [] (length (SmtProblem_defs p)) S (SmtDef_body (SmtProblem_defs p ! d)) =
        tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d))\<close>
    \<open>\<And>j. j < length (SmtProblem_asserts p) \<Longrightarrow>
        tok p F (length (SmtProblem_defs p)) 0 (length (SmtProblem_defs p)) (SmtProblem_asserts p ! j)\<close>
    \<open>\<And>j. j < length (SmtProblem_asserts p) \<Longrightarrow> Suc (dep p (length (SmtProblem_defs p)) (SmtProblem_asserts p ! j)) \<le> F\<close>
proof -
  note Q = P[unfolded tr_pre_def Let_def]
  show \<open>length (SmtProblem_funs p) < 2 ^ 63\<close> \<open>length (SmtProblem_defs p) < 2 ^ 64\<close> \<open>length (SmtProblem_defs p) \<le> F\<close>
    \<open>length (SmtProblem_asserts p) < 2 ^ 64\<close> \<open>length (SmtProblem_asserts p) \<le> F\<close>
    using Q by simp_all
  show \<open>length (SmtDef_params (SmtProblem_defs p ! d)) < 2 ^ 64\<close> if \<open>d < length (SmtProblem_defs p)\<close> for d
    using Q that by blast
  fix d dm S
  assume d: \<open>d < length (SmtProblem_defs p)\<close> and e: \<open>SmtDef_params (SmtProblem_defs p ! d) = []\<close>
  have t: \<open>tok p F d 0 d (SmtDef_body (SmtProblem_defs p ! d))\<close> and u: \<open>Suc (dep p d (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close>
    using Q d e by blast+
  note I = tok_n_indep(1)[OF t, where n'=\<open>length (SmtProblem_defs p)\<close> and dm=dm and env=\<open>[]\<close> and S=S]
  show \<open>tok p F d 0 (length (SmtProblem_defs p)) (SmtDef_body (SmtProblem_defs p ! d))\<close>
    \<open>Suc (dep p (length (SmtProblem_defs p)) (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close>
    \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) S (SmtDef_body (SmtProblem_defs p ! d)) =
        tr_term_m p dm [] d S (SmtDef_body (SmtProblem_defs p ! d))\<close>
    using I d u by simp_all
next
  note Q = P[unfolded tr_pre_def Let_def]
  fix j assume j: \<open>j < length (SmtProblem_asserts p)\<close>
  show \<open>tok p F (length (SmtProblem_defs p)) 0 (length (SmtProblem_defs p)) (SmtProblem_asserts p ! j)\<close>
    \<open>Suc (dep p (length (SmtProblem_defs p)) (SmtProblem_asserts p ! j)) \<le> F\<close>
    using Q nth_mem[OF j] by blast+
qed


lemma lw_enc_lit_enc_of: \<open>lw (enc_lit_m (encm (enc_of x))) = lw (enc_lit_m x)\<close>
  by (cases x) (simp_all add: lw_def)

lemma tr_init_tr: \<open>tr_of (fst (TD p 0)) =
  make_Tr [make_Term (word_of_nat (length (SmtProblem_funs p))) [], make_Term (word_of_nat (length (SmtProblem_funs p)) + 1) []]
    [make_Atom 0 0, make_Atom 0 1] [make_Clause [make_Lit 1 False]] (word_of_nat (length (SmtProblem_funs p)) + 2)\<close>
  by (simp add: TD_0 init_eq tr_of_def lit_m_def)

lemma TD_step:
  assumes \<open>tr_pre F p\<close> \<open>d < length (SmtProblem_defs p)\<close>
  shows \<open>bnd (fst (TD p d))\<close> \<open>map (encm \<circ> enc_of) (snd (TD p d)) = snd (TD p d)\<close>
    \<open>SmtDef_params (SmtProblem_defs p ! d) = [] \<Longrightarrow>
       tbnd p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d))\<close>
    \<open>SmtDef_params (SmtProblem_defs p ! d) = [] \<Longrightarrow> TD p (Suc d) =
       (fst (tr_term_m p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d))),
        snd (TD p d) @ [snd (tr_term_m p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d)))])\<close>
    \<open>SmtDef_params (SmtProblem_defs p ! d) \<noteq> [] \<Longrightarrow> TD p (Suc d) = (fst (TD p d), snd (TD p d) @ [ELit 0 True])\<close>
proof -
  have F: \<open>bnd (fst (TD p d)) \<and> (\<forall>e \<in> set (snd (TD p d)). ib e)\<close> using TD_facts[OF assms(1) less_imp_le[OF assms(2)]] .
  show \<open>bnd (fst (TD p d))\<close> using F by simp
  show \<open>map (encm \<circ> enc_of) (snd (TD p d)) = snd (TD p d)\<close> using F map_encm_enc_of[of \<open>snd (TD p d)\<close>] by simp
  show e: \<open>TD p (Suc d) =
       (fst (tr_term_m p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d))),
        snd (TD p d) @ [snd (tr_term_m p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d)))])\<close>
    if \<open>SmtDef_params (SmtProblem_defs p ! d) = []\<close>
    using that tr_pre_facts(9)[OF assms(1) assms(2) that] by (simp add: TD_Suc tr_defs_step_def split_def Let_def)
  show \<open>tbnd p (snd (TD p d)) [] (length (SmtProblem_defs p)) (fst (TD p d)) (SmtDef_body (SmtProblem_defs p ! d))\<close>
    if \<open>SmtDef_params (SmtProblem_defs p ! d) = []\<close>
  proof -
    have \<open>bnd (fst (TD p (Suc d)))\<close> using TD_facts[OF assms(1), of \<open>Suc d\<close>] assms(2) Suc_leI by blast
    then show ?thesis using e[OF that] by (simp add: tbnd_def)
  qed
  show \<open>SmtDef_params (SmtProblem_defs p ! d) \<noteq> [] \<Longrightarrow> TD p (Suc d) = (fst (TD p d), snd (TD p d) @ [ELit 0 True])\<close>
    by (simp add: TD_Suc tr_defs_step_def split_def)
qed

lemma TA_step:
  assumes \<open>tr_pre F p\<close> \<open>j < length (SmtProblem_asserts p)\<close>
  shows \<open>bnd (TA p j)\<close> \<open>map (encm \<circ> enc_of) (snd (tr_defs_m p)) = snd (tr_defs_m p)\<close>
    \<open>tbnd p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)\<close>
    \<open>TA p (Suc j) = add_clause_m (fst (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))
       [lit_m (fst (enc_lit_m (snd (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))))
              (snd (enc_lit_m (snd (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))))]\<close>
proof -
  have bq: \<open>bnd (tr_state_m p)\<close> using assms(1) by (simp add: tr_pre_def Let_def)
  show \<open>bnd (TA p j)\<close> by (rule bnd_pre[OF pre_TA bq])
  have F: \<open>bnd (fst (TD p (length (SmtProblem_defs p)))) \<and> (\<forall>e \<in> set (snd (TD p (length (SmtProblem_defs p)))). ib e)\<close>
    using TD_facts[OF assms(1) order_refl] .
  show \<open>map (encm \<circ> enc_of) (snd (tr_defs_m p)) = snd (tr_defs_m p)\<close>
    using F map_encm_enc_of[of \<open>snd (tr_defs_m p)\<close>] by (simp add: TD_final)
  show e: \<open>TA p (Suc j) = add_clause_m (fst (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))
       [lit_m (fst (enc_lit_m (snd (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))))
              (snd (enc_lit_m (snd (tr_term_m p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)))))]\<close>
    using assms(2) by (simp add: TA_Suc tr_asserts_step_def Let_def)
  have \<open>bnd (TA p (Suc j))\<close> by (rule bnd_pre[OF pre_TA bq])
  then show \<open>tbnd p (snd (tr_defs_m p)) [] (length (SmtProblem_defs p)) (TA p j) (SmtProblem_asserts p ! j)\<close>
    unfolding e tbnd_def using bnd_pre[OF pre_add_clause[OF pre_refl]] by blast
qed

lemma tr_pre_params: \<open>tr_pre F p \<Longrightarrow> d < length (SmtProblem_defs p) \<Longrightarrow>
  ((word_of_nat (length (SmtDef_params (SmtProblem_defs p ! d))) :: 64 word) = 0) = (SmtDef_params (SmtProblem_defs p ! d) = [])\<close>
  using tr_pre_facts(6)[of F p d] wn_len_0 by blast

lemma tr_pre_lt: \<open>tr_pre F p \<Longrightarrow> unat (r :: 64 word) < length (SmtProblem_defs p) \<Longrightarrow> unat r < 18446744073709551615\<close>
  using tr_pre_facts(2)[of F p] by simp

lemma tr_pre_inc: \<open>tr_pre F p \<Longrightarrow> unat (r :: 64 word) < length (SmtProblem_defs p) \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
  using tr_pre_lt[of F p r] unat_r1 by blast

lemma tr_pre_lt_a: \<open>tr_pre F p \<Longrightarrow> unat (r :: 64 word) < length (SmtProblem_asserts p) \<Longrightarrow> unat r < 18446744073709551615\<close>
  using tr_pre_facts(4)[of F p] by simp

lemma tr_pre_inc_a: \<open>tr_pre F p \<Longrightarrow> unat (r :: 64 word) < length (SmtProblem_asserts p) \<Longrightarrow> unat (r + 1) = Suc (unat r)\<close>
  using tr_pre_lt_a[of F p r] unat_r1 by blast

lemma tr_pre_unatL: \<open>tr_pre F p \<Longrightarrow> unat (word_of_nat (length (SmtProblem_defs p)) :: 64 word) = length (SmtProblem_defs p)\<close>
  using tr_pre_facts(2)[of F p] by (simp add: unat_of_nat_eq)

lemma tr_pre_unatA: \<open>tr_pre F p \<Longrightarrow> unat (word_of_nat (length (SmtProblem_asserts p)) :: 64 word) = length (SmtProblem_asserts p)\<close>
  using tr_pre_facts(4)[of F p] by (simp add: unat_of_nat_eq)

lemma len_defs_m: \<open>length (snd (tr_defs_m p)) = length (SmtProblem_defs p)\<close>
  using TD_len[of p \<open>length (SmtProblem_defs p)\<close>] by (simp add: TD_final)

definition tr_problem_contract :: \<open>SmtProblem \<Rightarrow> ('s, Problem, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_problem_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>tr_pre urust_fuel p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = tr_problem_m p\<rangle>)\<close>

lemma tr_problem_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_problem p \<Turnstile>\<^sub>F tr_problem_contract p\<close>
  apply (crush_boot f: tr_problem_def contract: tr_problem_contract_def)
  apply (crush_base inline: len_def vec_push_def simp add: tr_pre_facts(1) unat_of_nat_eq)
  subgoal for s_ref dm_ref d_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gs sv gm mv gd d. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
           can_alloc_reference \<star>
           \<langle>unat d \<le> length (SmtProblem_defs p) \<and> sv = tr_of (fst (TD p (unat d))) \<and> mv = map enc_of (snd (TD p (unat d))) \<and>
            length (SmtProblem_defs p) - unat d \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gs sv gm mv gd d. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>mv \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
           can_alloc_reference \<star>
           \<langle>unat d < length (SmtProblem_defs p) \<and> sv = tr_of (fst (TD p (unat d))) \<and> mv = map enc_of (snd (TD p (unat d))) \<and>
            length (SmtProblem_defs p) - unat d \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound tr_init_tr
        tr_pre_facts)
    apply (simp_all add: tr_pre_params tr_pre_inc[of urust_fuel p] tr_pre_lt[of urust_fuel p]
        TD_step st_tr_of_bnd TD_len tres_def)
    apply (simp_all add: tr_pre_facts(7)[of urust_fuel p] tr_pre_facts(8)[of urust_fuel p] tr_pre_unatL[of urust_fuel p])
    subgoal for gs gm gd d j_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gs sv gm gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>(map enc_of (snd (TD p (length (SmtProblem_defs p))))) \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>unat j \<le> length (SmtProblem_asserts p) \<and> sv = tr_of (TA p (unat j)) \<and> length (SmtProblem_asserts p) - unat j \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gs sv gm gj j. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>sv \<star> dm_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>(map enc_of (snd (TD p (length (SmtProblem_defs p))))) \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>unat j < length (SmtProblem_asserts p) \<and> sv = tr_of (TA p (unat j)) \<and> length (SmtProblem_asserts p) - unat j \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: word_less_nat_alt tr_pre_inc_a[of urust_fuel p] tr_pre_lt_a[of urust_fuel p]
          tr_pre_unatA[of urust_fuel p] TD_final TD_len len_defs_m TA_0 TA_final TA_step[of urust_fuel p]
          tr_pre_facts(10,11)[of urust_fuel p] tres_def st_tr_of_bnd lw_enc_lit_enc_of)
      apply (simp_all add: tr_of_def add_clause_m_def lw_def lit_m_def tr_problem_m_def Let_def tr_pre_facts(5)[of urust_fuel p])
      done
    apply (simp add: TD_0)
    done
  apply (simp_all add: unat_of_nat_eq tr_pre_facts(1)[of urust_fuel p] less_trans[OF tr_pre_facts(1)[of urust_fuel p]])
  done


subsection \<open>\<^verbatim>\<open>tr_model\<close>\<close>

lemma find_first: \<open>i < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow> \<forall>j < i. \<not> P (xs ! j) \<Longrightarrow> List.find P xs = Some (xs ! i)\<close>
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases i) fastforce+
qed

lemma find_none: \<open>\<forall>j < length xs. \<not> P (xs ! j) \<Longrightarrow> List.find P xs = None\<close>
  by (simp add: find_None_iff in_set_conv_nth) blast

lemma word_eq_unat: \<open>((a :: 64 word) = b) = (unat a = unat b)\<close>
  by (rule word_unat_eq_iff)

lemma wn_len_eq: \<open>length xs < 2 ^ 64 \<Longrightarrow> length ys < 2 ^ 64 \<Longrightarrow>
  ((word_of_nat (length xs) :: 64 word) = word_of_nat (length ys)) = (length xs = length ys)\<close>
  apply (rule iffI)
   apply (drule arg_cong[where f=unat])
   apply (simp add: unat_of_nat_eq)
  apply simp
  done

lemma wn0_iff: \<open>n < 2 ^ 64 \<Longrightarrow> ((word_of_nat n :: 64 word) = 0) = (n = 0)\<close>
  apply (rule iffI)
   apply (drule arg_cong[where f=unat])
   apply (simp add: unat_of_nat_eq)
  apply simp
  done

lemma cv_some:
  \<open>i < length (Model_entries m) \<Longrightarrow> Entry_fun (Model_entries m ! i) = f \<Longrightarrow> Entry_args (Model_entries m ! i) = [] \<Longrightarrow>
   \<forall>j < i. Entry_fun (Model_entries m ! j) = f \<longrightarrow> Entry_args (Model_entries m ! j) \<noteq> [] \<Longrightarrow>
   const_value_m m (unat f) = unat (Entry_val (Model_entries m ! i))\<close>
  unfolding const_value_m_def
  by (subst find_first[of i]) (auto simp: word_unat_eq_iff[symmetric])

lemma cv_none:
  \<open>\<forall>j < length (Model_entries m). Entry_fun (Model_entries m ! j) = f \<longrightarrow> Entry_args (Model_entries m ! j) \<noteq> [] \<Longrightarrow>
   const_value_m m (unat f) = 0\<close>
  unfolding const_value_m_def
  by (subst find_none) (auto simp: word_unat_eq_iff[symmetric])

definition const_value_contract :: \<open>Model \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>const_value_contract m f \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>length (Model_entries m) < 2 ^ 64 \<and> length (Model_entries m) \<le> urust_fuel \<and>
         (\<forall>e \<in> set (Model_entries m). length (Entry_args e) < 2 ^ 64)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = const_value_m m (unat f)\<rangle>)\<close>

lemma const_value_spec [crush_specs]:
  shows \<open>\<Gamma>; const_value m f \<Turnstile>\<^sub>F const_value_contract m f\<close>
  apply (crush_boot f: const_value_def contract: const_value_contract_def)
  apply (crush_base inline: len_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> length (Model_entries m) \<and>
            (\<forall>j < unat i. \<not> (unat (Entry_fun (Model_entries m ! j)) = unat f \<and> Entry_args (Model_entries m ! j) = [])) \<and>
            length (Model_entries m) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < length (Model_entries m) \<and>
            (\<forall>j < unat i. \<not> (unat (Entry_fun (Model_entries m ! j)) = unat f \<and> Entry_args (Model_entries m ! j) = [])) \<and>
            length (Model_entries m) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>r. (\<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i) \<star> can_alloc_reference \<star> \<langle>unat r = const_value_m m (unat f)\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt)
    apply (auto simp: unat_of_nat_eq wn0_iff unat_plus_one_of_less_bound[where n=\<open>length (Model_entries m)\<close>] less_Suc_eq intro: cv_some cv_none)
    apply (rule cv_some[symmetric]; simp)
    done
  done

definition DS :: \<open>Entry list \<Rightarrow> nat\<close> where
  \<open>DS es \<equiv> foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) 1 es\<close>

lemma DS_0: \<open>DS [] = 1\<close>
  by (simp add: DS_def)

lemma DS_snoc: \<open>DS (es @ [e]) = foldl dsize_step (dsize_step (DS es) (Entry_val e)) (Entry_args e)\<close>
  by (simp add: DS_def)

lemma domain_size_DS: \<open>domain_size_m m = DS (Model_entries m)\<close>
  by (simp add: domain_size_m_def DS_def)

lemma unat_inc63: \<open>unat (x :: 64 word) < 2 ^ 63 \<Longrightarrow> unat (x + 1) = Suc (unat x)\<close>
  using unat_plus_one_of_less_bound[of x \<open>2 ^ 63\<close>] by simp

definition domain_size_contract :: \<open>Model \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>domain_size_contract m \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>length (Model_entries m) < 2 ^ 64 \<and> length (Model_entries m) \<le> urust_fuel \<and>
         (\<forall>e \<in> set (Model_entries m). length (Entry_args e) < 2 ^ 64 \<and> length (Entry_args e) \<le> urust_fuel \<and>
            unat (Entry_val e) < 2 ^ 63 \<and> (\<forall>x \<in> set (Entry_args e). unat x < 2 ^ 63))\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = domain_size_m m\<rangle>)\<close>

lemma domain_size_spec [crush_specs]:
  shows \<open>\<Gamma>; domain_size m \<Turnstile>\<^sub>F domain_size_contract m\<close>
  apply (crush_boot f: domain_size_def contract: domain_size_contract_def)
  apply (crush_base inline: len_def)
  subgoal for n_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> length (Model_entries m) \<and> unat n = DS (take (unat i) (Model_entries m)) \<and>
            length (Model_entries m) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < length (Model_entries m) \<and> unat n = DS (take (unat i) (Model_entries m)) \<and>
            length (Model_entries m) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound DS_0)
    subgoal for k gn gi r ra x
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gn n gi gk kk. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>r \<star> x \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
           \<langle>unat kk \<le> length (Entry_args (Model_entries m ! unat r)) \<and>
            unat n = foldl dsize_step (dsize_step (DS (take (unat r) (Model_entries m))) (Entry_val (Model_entries m ! unat r)))
              (take (unat kk) (Entry_args (Model_entries m ! unat r))) \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gn n gi gk kk. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>r \<star> x \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
           \<langle>unat kk < length (Entry_args (Model_entries m ! unat r)) \<and>
            unat n = foldl dsize_step (dsize_step (DS (take (unat r) (Model_entries m))) (Entry_val (Model_entries m ! unat r)))
              (take (unat kk) (Entry_args (Model_entries m ! unat r))) \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
          dsize_step_def take_Suc_conv_app_nth DS_snoc)
      subgoal using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] by (fastforce intro: unat_inc63 nth_mem)
      subgoal using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] by (fastforce intro: unat_inc63 nth_mem)
      subgoal using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] by (fastforce intro: unat_inc63 nth_mem)
      subgoal for ka gna gia gk raa rb using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] nth_mem[of \<open>unat rb\<close> \<open>Entry_args (Model_entries m ! unat r)\<close>] by fastforce
      done
    subgoal for k gn gi ra r x
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gn n gi gk kk. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>r \<star> x \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
           \<langle>unat kk \<le> length (Entry_args (Model_entries m ! unat r)) \<and>
            unat n = foldl dsize_step (dsize_step (DS (take (unat r) (Model_entries m))) (Entry_val (Model_entries m ! unat r)))
              (take (unat kk) (Entry_args (Model_entries m ! unat r))) \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gn n gi gk kk. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>r \<star> x \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
           \<langle>unat kk < length (Entry_args (Model_entries m ! unat r)) \<and>
            unat n = foldl dsize_step (dsize_step (DS (take (unat r) (Model_entries m))) (Entry_val (Model_entries m ! unat r)))
              (take (unat kk) (Entry_args (Model_entries m ! unat r))) \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base simp add: word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound
          dsize_step_def take_Suc_conv_app_nth DS_snoc)
      subgoal for ka gna gia gk raa rb using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] nth_mem[of \<open>unat rb\<close> \<open>Entry_args (Model_entries m ! unat r)\<close>] by (fastforce intro: unat_inc63)
      subgoal for ka gna gia gk raa rb using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] nth_mem[of \<open>unat rb\<close> \<open>Entry_args (Model_entries m ! unat r)\<close>] by (fastforce intro: unat_inc63)
      subgoal for ka gna gia gk raa rb using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] nth_mem[of \<open>unat rb\<close> \<open>Entry_args (Model_entries m ! unat r)\<close>] by (fastforce intro: unat_inc63)
      subgoal for ka gna gia gk raa rb using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] nth_mem[of \<open>unat rb\<close> \<open>Entry_args (Model_entries m ! unat r)\<close>] by (fastforce intro: unat_inc63)
      subgoal using nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>] by (fastforce intro: unat_inc63)
      done
    subgoal for k gn gi ra rb using nth_mem[of \<open>unat rb\<close> \<open>Model_entries m\<close>] by fastforce
    by (simp add: domain_size_DS)
  done

definition value_of_contract :: \<open>SmtSort \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, SmtValue, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>value_of_contract s v t \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = value_of_m s (unat v) (unat t)\<rangle>)\<close>

lemma value_of_spec [crush_specs]:
  shows \<open>\<Gamma>; value_of s v t \<Turnstile>\<^sub>F value_of_contract s v t\<close>
  apply (crush_boot f: value_of_def contract: value_of_contract_def)
  apply (crush_base split: SmtSort.splits)
  done

definition tr_interp_contract :: \<open>SmtProblem \<Rightarrow> Model \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, SmtInterp, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_interp_contract p m f t u \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>unat f < length (SmtProblem_funs p) \<and> length (SmtFun_args (SmtProblem_funs p ! unat f)) < 2 ^ 64 \<and>
         length (Model_entries m) < 2 ^ 64 \<and> length (Model_entries m) \<le> urust_fuel \<and>
         (\<forall>e \<in> set (Model_entries m). length (Entry_args e) < 2 ^ 64 \<and> length (Entry_args e) \<le> urust_fuel)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = tr_interp_m p m (unat f) (unat t) (unat u)\<rangle>)\<close>

lemma tr_interp_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_interp p m f t u \<Turnstile>\<^sub>F tr_interp_contract p m f t u\<close>
  apply (crush_boot f: tr_interp_def contract: tr_interp_contract_def)
  apply (crush_base inline: len_def vec_push_def)
  subgoal for es_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>ge ev gi i. es_ref \<mapsto>\<langle>\<top>\<rangle> ge\<down>ev \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> length (Model_entries m) \<and>
            ev = map (tr_entry_m (SmtProblem_funs p ! unat f) (unat t)) (filter (entry_ok_m (SmtProblem_funs p ! unat f) (unat f) (unat t) (unat u)) (take (unat i) (Model_entries m))) \<and>
            length (Model_entries m) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>ge ev gi i. es_ref \<mapsto>\<langle>\<top>\<rangle> ge\<down>ev \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < length (Model_entries m) \<and>
            ev = map (tr_entry_m (SmtProblem_funs p ! unat f) (unat t)) (filter (entry_ok_m (SmtProblem_funs p ! unat f) (unat f) (unat t) (unat u)) (take (unat i) (Model_entries m))) \<and>
            length (Model_entries m) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt)
    prefer 7
    subgoal for k ge gi r ok_ref as_ref k_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gk kk go ok ga av. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> ok_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>ok \<star> as_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star>
           can_alloc_reference \<star>
           \<langle>unat kk \<le> length (Entry_args (Model_entries m ! unat r)) \<and>
            length (Entry_args (Model_entries m ! unat r)) =
              length (SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r)))) \<and>
            ok = (\<forall>j < unat kk. SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r))) ! j = SmtSort_Bool \<longrightarrow>
                    Entry_args (Model_entries m ! unat r) ! j = t \<or> Entry_args (Model_entries m ! unat r) ! j = u) \<and>
            av = map (\<lambda>j. value_of_m (SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r))) ! j)
                    (unat (Entry_args (Model_entries m ! unat r) ! j)) (unat t)) [0..<unat kk] \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gk kk go ok ga av. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> ok_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>ok \<star> as_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>av \<star>
           can_alloc_reference \<star>
           \<langle>unat kk < length (Entry_args (Model_entries m ! unat r)) \<and>
            length (Entry_args (Model_entries m ! unat r)) =
              length (SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r)))) \<and>
            ok = (\<forall>j < unat kk. SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r))) ! j = SmtSort_Bool \<longrightarrow>
                    Entry_args (Model_entries m ! unat r) ! j = t \<or> Entry_args (Model_entries m ! unat r) ! j = u) \<and>
            av = map (\<lambda>j. value_of_m (SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r))) ! j)
                    (unat (Entry_args (Model_entries m ! unat r) ! j)) (unat t)) [0..<unat kk] \<and>
            length (Entry_args (Model_entries m ! unat r)) - unat kk \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def SmtEntry_mk_def simp add: word_less_nat_alt split: SmtSort.splits)
      apply (insert nth_mem[of \<open>unat r\<close> \<open>Model_entries m\<close>])
      apply (auto simp: unat_plus_one_of_less_bound[where n=\<open>length (SmtFun_args (SmtProblem_funs p ! unat (Entry_fun (Model_entries m ! unat r))))\<close>]
          unat_plus_one_of_less_bound[where n=\<open>length (Model_entries m)\<close>] less_Suc_eq word_unat.Rep_inverse unat_of_nat_eq
          take_Suc_conv_app_nth entry_ok_m_def tr_entry_m_def word_unat_eq_iff[symmetric] wn_len_eq)
      done
    apply (auto simp: unat_plus_one_of_less_bound[where n=\<open>length (Model_entries m)\<close>] take_Suc_conv_app_nth entry_ok_m_def
        word_unat_eq_iff[symmetric] tr_interp_m_def Let_def unat_of_nat_eq)
    done
  done

lemma unat_wn_inc63: \<open>n < 2 ^ 63 \<Longrightarrow> unat (word_of_nat n + (1 :: 64 word)) = Suc n\<close>
  using unat_inc63[of \<open>word_of_nat n\<close>] by (simp add: unat_of_nat_eq)

lemma wn_of_unat: \<open>unat (w :: 64 word) = n \<Longrightarrow> word_of_nat n = w\<close>
  by auto

text \<open>What \<^verbatim>\<open>tr_model\<close> needs, for the fuel \<open>F\<close>.\<close>
definition tm_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> Model \<Rightarrow> bool\<close> where
  \<open>tm_pre F p m \<equiv>
     length (SmtProblem_funs p) < 2 ^ 63 \<and> length (SmtProblem_funs p) \<le> F \<and> unat (SmtProblem_num_sorts p) \<le> F \<and>
     (\<forall>g \<in> set (SmtProblem_funs p). length (SmtFun_args g) < 2 ^ 64) \<and>
     length (Model_entries m) < 2 ^ 64 \<and> length (Model_entries m) \<le> F \<and>
     (\<forall>e \<in> set (Model_entries m). length (Entry_args e) < 2 ^ 64 \<and> length (Entry_args e) \<le> F \<and>
        unat (Entry_val e) < 2 ^ 63 \<and> (\<forall>x \<in> set (Entry_args e). unat x < 2 ^ 63))\<close>

definition tr_model_contract :: \<open>SmtProblem \<Rightarrow> Model \<Rightarrow> ('s, SmtModel, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tr_model_contract p m \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>tm_pre urust_fuel p m\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = tr_model_m p m\<rangle>)\<close>

lemma tr_model_spec [crush_specs]:
  shows \<open>\<Gamma>; tr_model p m \<Turnstile>\<^sub>F tr_model_contract p m\<close>
  apply (crush_boot f: tr_model_def contract: tr_model_contract_def)
  apply (crush_base inline: len_def vec_push_def simp add: tm_pre_def unat_of_nat_eq)
  subgoal for t u n ds_ref i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gd dv gi i. ds_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i \<le> unat (SmtProblem_num_sorts p) \<and> dv = replicate (unat i) n \<and>
            unat (SmtProblem_num_sorts p) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gd dv gi i. ds_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>dv \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
           \<langle>unat i < unat (SmtProblem_num_sorts p) \<and> dv = replicate (unat i) n \<and>
            unat (SmtProblem_num_sorts p) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def simp add: word_less_nat_alt unat_of_nat_eq)
    prefer 5
    subgoal for gd gi fs_ref f_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gf fv gi i. fs_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fv \<star> f_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i \<le> length (SmtProblem_funs p) \<and> fv = map (\<lambda>f. tr_interp_m p m f (unat t) (unat u)) [0..<unat i] \<and>
              length (SmtProblem_funs p) - unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gf fv gi i. fs_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fv \<star> f_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i < length (SmtProblem_funs p) \<and> fv = map (\<lambda>f. tr_interp_m p m f (unat t) (unat u)) [0..<unat i] \<and>
              length (SmtProblem_funs p) - unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base inline: vec_push_def SmtModel_mk_def simp add: word_less_nat_alt unat_of_nat_eq)
      apply (auto simp: unat_plus_one_of_less_bound[where n=\<open>length (SmtProblem_funs p)\<close>] unat_wn_inc63 tr_model_m_def Let_def)
      apply (metis wn_of_unat)
      done
    apply (insert More_Word.unat_lt2p[of \<open>SmtProblem_num_sorts p\<close>])
    apply (auto simp: unat_plus_one_of_less_bound[where n=\<open>unat (SmtProblem_num_sorts p)\<close>] replicate_append_same)
    done
  done

text \<open>A fuel bound for \<^verbatim>\<open>tr_model\<close> computed from \<open>p\<close> and \<open>m\<close>.\<close>
definition tm_fuel :: \<open>SmtProblem \<Rightarrow> Model \<Rightarrow> nat\<close> where
  \<open>tm_fuel p m \<equiv> length (SmtProblem_funs p) + unat (SmtProblem_num_sorts p) + length (Model_entries m) +
     sum_list (map (\<lambda>e. length (Entry_args e)) (Model_entries m))\<close>

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>tr_model\<close>.\<close>
lemma tr_model_pre_vals:
  assumes R: \<open>smt_repr_ok p\<close> and V: \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms (tr_problem_m p)) \<and>
              (\<forall>a \<in> set (Entry_args e). unat a < length (Problem_terms (tr_problem_m p)))\<close>
    and T: \<open>length (Problem_terms (tr_problem_m p)) < 2 ^ 63\<close>
    and E: \<open>length (Model_entries m) < 2 ^ 63\<close>
    and A: \<open>\<forall>e \<in> set (Model_entries m). length (Entry_args e) < 2 ^ 64\<close>
    and NF: \<open>tm_fuel p m \<le> F\<close>
  shows \<open>tm_pre F p m\<close>
proof -
  have e: \<open>length (Entry_args e) \<le> F\<close> if \<open>e \<in> set (Model_entries m)\<close> for e
    using member_le_sum_list[of \<open>length (Entry_args e)\<close> \<open>map (\<lambda>e. length (Entry_args e)) (Model_entries m)\<close>] that NF by (simp add: tm_fuel_def)
  show ?thesis unfolding tm_pre_def using e E A T V NF R
    by (fastforce simp: smt_repr_ok_def tm_fuel_def)
qed


subsection \<open>\<^verbatim>\<open>in_fragment\<close>\<close>

text \<open>Every argument list of a term is shorter than \<open>2^64\<close> and has at most \<open>F\<close> elements.\<close>
fun fok :: \<open>nat \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>fok F (SmtTerm_Fun f args) = (length args < 2 ^ 64 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. fok F a))\<close>
| \<open>fok F (SmtTerm_Def d args) = (length args < 2 ^ 64 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. fok F a))\<close>
| \<open>fok F (SmtTerm_App op args) = (length args < 2 ^ 64 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. fok F a))\<close>
| \<open>fok F _ = True\<close>

lemma rf_nth_size_le: \<open>i < length ts \<Longrightarrow> size_list size ts \<le> k \<Longrightarrow> Suc (size (ts ! i)) \<le> k\<close>
proof (induction ts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case by (cases i) fastforce+
qed

definition sort_in_fragment_contract :: \<open>SmtSort \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sort_in_fragment_contract s \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>r = smt_sort_no_bv s\<rangle>)\<close>

lemma sort_in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; sort_in_fragment s \<Turnstile>\<^sub>F sort_in_fragment_contract s\<close>
  apply (crush_boot f: sort_in_fragment_def contract: sort_in_fragment_contract_def)
  apply (crush_base split: SmtSort.splits)
  done

definition sorts_in_fragment_contract :: \<open>SmtSort list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sorts_in_fragment_contract ss \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>length ss < 2 ^ 64 \<and> length ss \<le> urust_fuel\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (\<forall>s \<in> set ss. smt_sort_no_bv s)\<rangle>)\<close>

lemma sorts_in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; sorts_in_fragment ss \<Turnstile>\<^sub>F sorts_in_fragment_contract ss\<close>
  apply (crush_boot f: sorts_in_fragment_def contract: sorts_in_fragment_contract_def)
  apply (crush_base inline: len_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> length ss \<and> (\<forall>j < unat i. smt_sort_no_bv (ss ! j)) \<and> length ss - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < length ss \<and> (\<forall>j < unat i. smt_sort_no_bv (ss ! j)) \<and> length ss - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>r. (\<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i) \<star> can_alloc_reference \<star> \<langle>r = (\<forall>s \<in> set ss. smt_sort_no_bv s)\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound)
    apply (auto simp: less_Suc_eq in_set_conv_nth)
    apply (metis nth_mem)+
    done
  done

definition tif_contract :: \<open>nat \<Rightarrow> SmtTerm \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tif_contract k t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> fok urust_fuel t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = smt_term_no_bv t\<rangle>)\<close>

definition tsif_contract :: \<open>nat \<Rightarrow> SmtTerm list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>tsif_contract k ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size_list size ts) \<le> k \<and> length ts < 2 ^ 64 \<and> length ts \<le> urust_fuel \<and> (\<forall>a \<in> set ts. fok urust_fuel a)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = (\<forall>a \<in> set ts. smt_term_no_bv a)\<rangle>)\<close>

lemma tif_step_spec:
  assumes IH1: \<open>\<And>t. \<Gamma>; f t \<Turnstile>\<^sub>F tif_contract k t\<close>
      and IH2: \<open>\<And>ts. \<Gamma>; g ts \<Turnstile>\<^sub>F tsif_contract k ts\<close>
  shows \<open>\<Gamma>; fst (term_in_fragment_rec_step (f, g)) t \<Turnstile>\<^sub>F tif_contract (Suc k) t\<close>
    and \<open>\<Gamma>; snd (term_in_fragment_rec_step (f, g)) ts \<Turnstile>\<^sub>F tsif_contract (Suc k) ts\<close>
proof -
  show \<open>\<Gamma>; fst (term_in_fragment_rec_step (f, g)) t \<Turnstile>\<^sub>F tif_contract (Suc k) t\<close>
    apply (crush_boot f: term_in_fragment_rec_step_def contract: tif_contract_def)
    apply (crush_base specs add: IH2 contracts add: tsif_contract_def split: SmtTerm.splits SmtOp.splits)
    done
  show \<open>\<Gamma>; snd (term_in_fragment_rec_step (f, g)) ts \<Turnstile>\<^sub>F tsif_contract (Suc k) ts\<close>
    apply (crush_boot f: term_in_fragment_rec_step_def contract: tsif_contract_def)
    apply (crush_base inline: len_def)
    subgoal for i_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i \<le> length ts \<and> (\<forall>j < unat i. smt_term_no_bv (ts ! j)) \<and> length ts - unat i \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
             \<langle>unat i < length ts \<and> (\<forall>j < unat i. smt_term_no_bv (ts ! j)) \<and> length ts - unat i \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. (\<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i) \<star> can_alloc_reference \<star> \<langle>r = (\<forall>a \<in> set ts. smt_term_no_bv a)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base specs add: IH1 contracts add: tif_contract_def
          simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound rf_nth_size_le)
      apply (auto simp: less_Suc_eq in_set_conv_nth)
      apply (metis nth_mem)+
      done
    done
qed

lemma tif_rec_spec:
  shows \<open>(\<forall>t. \<Gamma>; fst ((term_in_fragment_rec_step ^^ k) h) t \<Turnstile>\<^sub>F tif_contract k t) \<and>
         (\<forall>ts. \<Gamma>; snd ((term_in_fragment_rec_step ^^ k) h) ts \<Turnstile>\<^sub>F tsif_contract k ts)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tif_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: tsif_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(term_in_fragment_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(term_in_fragment_rec_step ^^ k) h\<close>)
  show ?case
    using tif_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma term_in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; term_in_fragment t \<Turnstile>\<^sub>F tif_contract urust_fuel t\<close>
  unfolding term_in_fragment_def using tif_rec_spec by blast

lemma terms_in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; terms_in_fragment ts \<Turnstile>\<^sub>F tsif_contract urust_fuel ts\<close>
  unfolding terms_in_fragment_def using tif_rec_spec by blast

lemma frag_fun: \<open>smt_fragment p \<Longrightarrow> j < length (SmtProblem_funs p) \<Longrightarrow>
  smt_sort_no_bv (SmtFun_ret (SmtProblem_funs p ! j)) \<and> (\<forall>s \<in> set (SmtFun_args (SmtProblem_funs p ! j)). smt_sort_no_bv s)\<close>
  by (auto simp: smt_fragment_def dest!: nth_mem)

lemma frag_def: \<open>smt_fragment p \<Longrightarrow> j < length (SmtProblem_defs p) \<Longrightarrow>
  smt_sort_no_bv (SmtDef_ret (SmtProblem_defs p ! j)) \<and> smt_term_no_bv (SmtDef_body (SmtProblem_defs p ! j)) \<and>
  (\<forall>s \<in> set (SmtDef_params (SmtProblem_defs p ! j)). smt_sort_no_bv s)\<close>
  by (auto simp: smt_fragment_def dest!: nth_mem)

text \<open>The fragment from the three parts \<^verbatim>\<open>in_fragment\<close> checks in turn.\<close>
lemma frag_iff:
  assumes \<open>\<forall>j < length (SmtProblem_funs p). (\<forall>s \<in> set (SmtFun_args (SmtProblem_funs p ! j)). smt_sort_no_bv s) \<and>
             smt_sort_no_bv (SmtFun_ret (SmtProblem_funs p ! j))\<close>
    \<open>\<forall>j < length (SmtProblem_defs p). (\<forall>s \<in> set (SmtDef_params (SmtProblem_defs p ! j)). smt_sort_no_bv s) \<and>
             smt_sort_no_bv (SmtDef_ret (SmtProblem_defs p ! j)) \<and> smt_term_no_bv (SmtDef_body (SmtProblem_defs p ! j))\<close>
  shows \<open>smt_fragment p = (\<forall>a \<in> set (SmtProblem_asserts p). smt_term_no_bv a)\<close>
  using assms by (auto simp: smt_fragment_def all_set_conv_all_nth)

text \<open>What \<^verbatim>\<open>in_fragment\<close> needs, for the fuel \<open>F\<close>.\<close>
definition if_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> bool\<close> where
  \<open>if_pre F p \<equiv>
     length (SmtProblem_funs p) < 2 ^ 64 \<and> length (SmtProblem_funs p) \<le> F \<and>
     (\<forall>g \<in> set (SmtProblem_funs p). length (SmtFun_args g) < 2 ^ 64 \<and> length (SmtFun_args g) \<le> F) \<and>
     length (SmtProblem_defs p) < 2 ^ 64 \<and> length (SmtProblem_defs p) \<le> F \<and>
     (\<forall>e \<in> set (SmtProblem_defs p). length (SmtDef_params e) < 2 ^ 64 \<and> length (SmtDef_params e) \<le> F \<and>
        fok F (SmtDef_body e) \<and> Suc (size (SmtDef_body e)) \<le> F) \<and>
     length (SmtProblem_asserts p) < 2 ^ 64 \<and> length (SmtProblem_asserts p) \<le> F \<and>
     Suc (size_list size (SmtProblem_asserts p)) \<le> F \<and> (\<forall>t \<in> set (SmtProblem_asserts p). fok F t)\<close>

definition in_fragment_contract :: \<open>SmtProblem \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>in_fragment_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>if_pre urust_fuel p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = smt_fragment p\<rangle>)\<close>

lemma in_fragment_spec [crush_specs]:
  shows \<open>\<Gamma>; in_fragment p \<Turnstile>\<^sub>F in_fragment_contract p\<close>
  apply (crush_boot f: in_fragment_def contract: in_fragment_contract_def)
  apply (crush_base inline: len_def simp add: if_pre_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>rule_tac
      INV=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i \<le> length (SmtProblem_funs p) \<and>
            (\<forall>j < unat i. (\<forall>s \<in> set (SmtFun_args (SmtProblem_funs p ! j)). smt_sort_no_bv s) \<and>
               smt_sort_no_bv (SmtFun_ret (SmtProblem_funs p ! j))) \<and> length (SmtProblem_funs p) - unat i \<le> c\<rangle>\<close> and
      INV'=\<open>\<lambda>c. \<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
           \<langle>unat i < length (SmtProblem_funs p) \<and>
            (\<forall>j < unat i. (\<forall>s \<in> set (SmtFun_args (SmtProblem_funs p ! j)). smt_sort_no_bv s) \<and>
               smt_sort_no_bv (SmtFun_ret (SmtProblem_funs p ! j))) \<and> length (SmtProblem_funs p) - unat i \<le> Suc c\<rangle>\<close> and
      \<tau>=\<open>\<lambda>r. (\<Squnion>gi i. i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i) \<star> can_alloc_reference \<star> \<langle>r = smt_fragment p\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound)
    prefer 5
    subgoal for gi i d_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>c. \<Squnion>gd d. d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
             \<langle>unat d \<le> length (SmtProblem_defs p) \<and>
              (\<forall>j < unat d. (\<forall>s \<in> set (SmtDef_params (SmtProblem_defs p ! j)). smt_sort_no_bv s) \<and>
                 smt_sort_no_bv (SmtDef_ret (SmtProblem_defs p ! j)) \<and> smt_term_no_bv (SmtDef_body (SmtProblem_defs p ! j))) \<and>
              length (SmtProblem_defs p) - unat d \<le> c\<rangle>\<close> and
        INV'=\<open>\<lambda>c. \<Squnion>gd d. d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star> can_alloc_reference \<star>
             \<langle>unat d < length (SmtProblem_defs p) \<and>
              (\<forall>j < unat d. (\<forall>s \<in> set (SmtDef_params (SmtProblem_defs p ! j)). smt_sort_no_bv s) \<and>
                 smt_sort_no_bv (SmtDef_ret (SmtProblem_defs p ! j)) \<and> smt_term_no_bv (SmtDef_body (SmtProblem_defs p ! j))) \<and>
              length (SmtProblem_defs p) - unat d \<le> Suc c\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. (\<Squnion>gd d. d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d) \<star> can_alloc_reference \<star> \<langle>r = smt_fragment p\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base contracts add: tsif_contract_def simp add: word_less_nat_alt unat_of_nat_eq unat_plus_one_of_less_bound)
      apply (auto simp: less_Suc_eq frag_iff dest: frag_def)
      done
    apply (auto simp: less_Suc_eq dest: frag_fun)
    done
  done


subsection \<open>The preconditions follow from the facts of the top-level proof\<close>

lemma min_ar_sort: \<open>smt_op_sort op ss \<noteq> None \<Longrightarrow> min_ar op \<le> length ss\<close>
  by (cases op) (auto split: list.splits if_splits)

text \<open>The largest number of arguments of a node of a term.\<close>
fun margs :: \<open>SmtTerm \<Rightarrow> nat\<close> and margss :: \<open>SmtTerm list \<Rightarrow> nat\<close> where
  \<open>margs (SmtTerm_Fun f args) = max (length args) (margss args)\<close>
| \<open>margs (SmtTerm_Def d args) = max (length args) (margss args)\<close>
| \<open>margs (SmtTerm_App op args) = max (length args) (margss args)\<close>
| \<open>margs _ = 0\<close>
| \<open>margss [] = 0\<close>
| \<open>margss (a # rest) = max (margs a) (margss rest)\<close>

lemma margss_ge: \<open>a \<in> set ts \<Longrightarrow> margs a \<le> margss ts\<close>
  by (induction ts) auto

text \<open>The bound on the fuel: the lengths of the lists of \<open>p\<close>, the numbers of arguments (and their
  squares), the sizes of the terms, the depths of the recursion of \<^verbatim>\<open>enc\<close>, and the number of terms
  and of their arguments in the translation (for the loops of \<^verbatim>\<open>tr_model\<close> over the model).\<close>
definition tr_fuel :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>tr_fuel p \<equiv>
     let fs = SmtProblem_funs p; ds = SmtProblem_defs p; ts = SmtProblem_asserts p; q = tr_problem_m p in
     length fs + length ds + length ts + unat (SmtProblem_num_sorts p) +
     sum_list (map (\<lambda>g. length (SmtFun_args g)) fs) + sum_list (map (\<lambda>e. length (SmtDef_params e)) ds) +
     sum_list (map (\<lambda>e. margs (SmtDef_body e) * margs (SmtDef_body e) + margs (SmtDef_body e) + Suc (size (SmtDef_body e))) ds) +
     sum_list (map (\<lambda>t. margs t * margs t + margs t) ts) + Suc (size_list size ts) +
     sum_list (map (\<lambda>d. Suc (dep p d (SmtDef_body (ds ! d)))) [0..<length ds]) +
     sum_list (map (\<lambda>t. Suc (dep p (length ds) t)) ts) +
     length (Problem_terms q) + sum_list (map (\<lambda>t. length (Term_args t)) (Problem_terms q))\<close>

lemma le_sum_list: \<open>x \<in> set xs \<Longrightarrow> (f :: 'a \<Rightarrow> nat) x \<le> sum_list (map f xs)\<close>
  by (induction xs) auto

lemma tr_fuel_ge:
  \<open>length (SmtProblem_funs p) \<le> tr_fuel p\<close> \<open>length (SmtProblem_defs p) \<le> tr_fuel p\<close>
  \<open>length (SmtProblem_asserts p) \<le> tr_fuel p\<close> \<open>unat (SmtProblem_num_sorts p) \<le> tr_fuel p\<close>
  \<open>g \<in> set (SmtProblem_funs p) \<Longrightarrow> length (SmtFun_args g) \<le> tr_fuel p\<close>
  \<open>e \<in> set (SmtProblem_defs p) \<Longrightarrow> length (SmtDef_params e) \<le> tr_fuel p\<close>
  \<open>e \<in> set (SmtProblem_defs p) \<Longrightarrow> margs (SmtDef_body e) * margs (SmtDef_body e) + margs (SmtDef_body e) + Suc (size (SmtDef_body e)) \<le> tr_fuel p\<close>
  \<open>t \<in> set (SmtProblem_asserts p) \<Longrightarrow> margs t * margs t + margs t \<le> tr_fuel p\<close>
  \<open>Suc (size_list size (SmtProblem_asserts p)) \<le> tr_fuel p\<close>
  \<open>d < length (SmtProblem_defs p) \<Longrightarrow> Suc (dep p d (SmtDef_body (SmtProblem_defs p ! d))) \<le> tr_fuel p\<close>
  \<open>t \<in> set (SmtProblem_asserts p) \<Longrightarrow> Suc (dep p (length (SmtProblem_defs p)) t) \<le> tr_fuel p\<close>
  \<open>length (Problem_terms (tr_problem_m p)) \<le> tr_fuel p\<close>
  \<open>x \<in> set (Problem_terms (tr_problem_m p)) \<Longrightarrow> length (Term_args x) \<le> tr_fuel p\<close>
proof -
  note L = le_sum_list
  show \<open>length (SmtProblem_funs p) \<le> tr_fuel p\<close> \<open>length (SmtProblem_defs p) \<le> tr_fuel p\<close>
    \<open>length (SmtProblem_asserts p) \<le> tr_fuel p\<close> \<open>unat (SmtProblem_num_sorts p) \<le> tr_fuel p\<close>
    \<open>Suc (size_list size (SmtProblem_asserts p)) \<le> tr_fuel p\<close> \<open>length (Problem_terms (tr_problem_m p)) \<le> tr_fuel p\<close>
    by (simp_all add: tr_fuel_def Let_def)
  show \<open>g \<in> set (SmtProblem_funs p) \<Longrightarrow> length (SmtFun_args g) \<le> tr_fuel p\<close>
    using L[of g \<open>SmtProblem_funs p\<close> \<open>\<lambda>g. length (SmtFun_args g)\<close>] by (simp add: tr_fuel_def Let_def)
  show \<open>e \<in> set (SmtProblem_defs p) \<Longrightarrow> length (SmtDef_params e) \<le> tr_fuel p\<close>
    using L[of e \<open>SmtProblem_defs p\<close> \<open>\<lambda>e. length (SmtDef_params e)\<close>] by (simp add: tr_fuel_def Let_def)
  show \<open>e \<in> set (SmtProblem_defs p) \<Longrightarrow> margs (SmtDef_body e) * margs (SmtDef_body e) + margs (SmtDef_body e) + Suc (size (SmtDef_body e)) \<le> tr_fuel p\<close>
    using L[of e \<open>SmtProblem_defs p\<close> \<open>\<lambda>e. margs (SmtDef_body e) * margs (SmtDef_body e) + margs (SmtDef_body e) + Suc (size (SmtDef_body e))\<close>]
    by (simp add: tr_fuel_def Let_def)
  show \<open>t \<in> set (SmtProblem_asserts p) \<Longrightarrow> margs t * margs t + margs t \<le> tr_fuel p\<close>
    using L[of t \<open>SmtProblem_asserts p\<close> \<open>\<lambda>t. margs t * margs t + margs t\<close>] by (simp add: tr_fuel_def Let_def)
  show \<open>d < length (SmtProblem_defs p) \<Longrightarrow> Suc (dep p d (SmtDef_body (SmtProblem_defs p ! d))) \<le> tr_fuel p\<close>
    using L[of d \<open>[0..<length (SmtProblem_defs p)]\<close> \<open>\<lambda>d. Suc (dep p d (SmtDef_body (SmtProblem_defs p ! d)))\<close>]
    by (simp add: tr_fuel_def Let_def)
  show \<open>t \<in> set (SmtProblem_asserts p) \<Longrightarrow> Suc (dep p (length (SmtProblem_defs p)) t) \<le> tr_fuel p\<close>
    using L[of t \<open>SmtProblem_asserts p\<close> \<open>\<lambda>t. Suc (dep p (length (SmtProblem_defs p)) t)\<close>] by (simp add: tr_fuel_def Let_def)
  show \<open>x \<in> set (Problem_terms (tr_problem_m p)) \<Longrightarrow> length (Term_args x) \<le> tr_fuel p\<close>
    using L[of x \<open>Problem_terms (tr_problem_m p)\<close> \<open>\<lambda>t. length (Term_args t)\<close>] by (simp add: tr_fuel_def Let_def)
qed

text \<open>What a well-sorted problem whose lists are within the bounds gives for each definition.\<close>
definition defs_ok :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>defs_ok p F \<equiv> \<forall>d < length (SmtProblem_defs p).
      smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p)) (SmtDef_params (SmtProblem_defs p ! d))
        (SmtDef_body (SmtProblem_defs p ! d)) \<noteq> None \<and>
      smt_term_repr (SmtDef_body (SmtProblem_defs p ! d)) \<and> margs (SmtDef_body (SmtProblem_defs p ! d)) \<le> F \<and>
      margs (SmtDef_body (SmtProblem_defs p ! d)) * margs (SmtDef_body (SmtProblem_defs p ! d)) \<le> F \<and>
      length (SmtDef_params (SmtProblem_defs p ! d)) < 2 ^ 64\<close>

lemma sq_le: \<open>a \<le> b \<Longrightarrow> b * b \<le> (F :: nat) \<Longrightarrow> a * a \<le> F\<close>
  by (meson mult_le_mono order_trans)

lemma tok_of_wf:
  shows \<open>defs_ok p F \<Longrightarrow> smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t \<noteq> None \<Longrightarrow> smt_term_repr t \<Longrightarrow>
           margs t \<le> F \<Longrightarrow> margs t * margs t \<le> F \<Longrightarrow> n \<le> length (SmtProblem_defs p) \<Longrightarrow> n \<le> dl \<Longrightarrow> el = length ps \<Longrightarrow>
           tok p F dl el n t\<close>
    and \<open>defs_ok p F \<Longrightarrow> \<forall>a \<in> set ts. smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps a \<noteq> None \<and> smt_term_repr a \<Longrightarrow>
           margss ts \<le> F \<Longrightarrow> margss ts * margss ts \<le> F \<Longrightarrow> n \<le> length (SmtProblem_defs p) \<Longrightarrow> n \<le> dl \<Longrightarrow> el = length ps \<Longrightarrow>
           toks p F dl el n ts\<close>
proof (induction p F dl el n t and p F dl el n ts arbitrary: ps and ps rule: tok_toks.induct)
  case (2 p F dl el n f args)
  note P = 2(2-9)
  have M: \<open>map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) args = map Some (SmtFun_args (SmtProblem_funs p ! unat f))\<close>
    and f: \<open>unat f < length (SmtProblem_funs p)\<close> using P(2) by (auto split: if_splits)
  have A: \<open>\<forall>a \<in> set args. smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps a \<noteq> None \<and> smt_term_repr a\<close>
    using map_Some_ex[OF M] P(3) by fastforce
  have T: \<open>toks p F dl el n args\<close> using 2(1)[OF P(1) A] P(4-8) sq_le[of \<open>margss args\<close> \<open>margs (SmtTerm_Fun f args)\<close> F] by simp
  show ?case using f T P(3) P(4) by simp
next
  case (3 p F dl el n d args)
  note P = 3(3-10)
  let ?ds = \<open>SmtProblem_defs p\<close>
  let ?D = \<open>?ds ! unat d\<close>
  have d: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close>
    and M: \<open>map (smt_tsort (SmtProblem_funs p) (take n ?ds) ps) args = map Some (SmtDef_params ?D)\<close>
    using P(2) P(6) by (auto split: if_splits)
  have A: \<open>\<forall>a \<in> set args. smt_tsort (SmtProblem_funs p) (take n ?ds) ps a \<noteq> None \<and> smt_term_repr a\<close>
    using map_Some_ex[OF M] P(3) by fastforce
  have len: \<open>length args = length (SmtDef_params ?D)\<close> using M map_eq_imp_length_eq by fastforce
  have Wd: \<open>smt_tsort (SmtProblem_funs p) (take (unat d) ?ds) (SmtDef_params ?D) (SmtDef_body ?D) \<noteq> None\<close>
    \<open>smt_term_repr (SmtDef_body ?D)\<close> \<open>margs (SmtDef_body ?D) \<le> F\<close> \<open>margs (SmtDef_body ?D) * margs (SmtDef_body ?D) \<le> F\<close>
    \<open>length (SmtDef_params ?D) < 2 ^ 64\<close>
    using P(1) d(2) by (simp_all add: defs_ok_def)
  show ?case
  proof (cases \<open>SmtDef_params ?D = []\<close>)
    case True
    then show ?thesis using d P(7) Wd by simp
  next
    case False
    have T: \<open>toks p F dl el n args\<close>
      using 3(1)[OF False d(1) P(1) A] P(4-8) sq_le[of \<open>margss args\<close> \<open>margs (SmtTerm_Def d args)\<close> F] by simp
    have B: \<open>tok p F dl (length args) (unat d) (SmtDef_body ?D)\<close>
      using 3(2)[OF False d(1) P(1) Wd(1-4)] len d P(6,7) by simp
    show ?thesis using d T B Wd False P(3) P(4) by simp
  qed
next
  case (4 p F dl el n op args)
  note P = 4(2-9)
  have A: \<open>\<forall>a \<in> set args. smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps a \<noteq> None \<and> smt_term_repr a\<close>
    using P(2) P(3) by (auto split: if_splits) (metis image_eqI option.exhaust)
  have S: \<open>smt_op_sort op (map (the \<circ> smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) args) \<noteq> None\<close>
    using P(2) by (auto split: if_splits)
  have T: \<open>toks p F dl el n args\<close> using 4(1)[OF P(1) A] P(4-8) sq_le[of \<open>margss args\<close> \<open>margs (SmtTerm_App op args)\<close> F] by simp
  have Q: \<open>length args * length args \<le> F\<close> using sq_le[of \<open>length args\<close> \<open>margs (SmtTerm_App op args)\<close> F] P(5) by simp
  show ?case using min_ar_sort[OF S] T P(3) P(4) Q by simp
next
  case (7 p F dl el n a rest)
  note P = 7(3-9)
  have m: \<open>margs a \<le> margss (a # rest)\<close> \<open>margss rest \<le> margss (a # rest)\<close> by simp_all
  show ?case using 7(1)[OF P(1)] 7(2)[OF P(1)] P(2-7) sq_le[OF m(1) P(4)] sq_le[OF m(2) P(4)] by auto
qed (auto split: if_splits)

lemma fok_of_repr:
  \<open>smt_term_repr t \<Longrightarrow> margs t \<le> F \<Longrightarrow> fok F t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  then show ?case using margss_ge[of _ args] by (auto intro: order_trans)
next
  case (SmtTerm_Def d args)
  then show ?case using margss_ge[of _ args] by (auto intro: order_trans)
next
  case (SmtTerm_App op args)
  then show ?case using margss_ge[of _ args] by (auto intro: order_trans)
qed auto

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>tr_problem\<close>.\<close>
lemma tr_problem_pre:
  assumes W: \<open>smt_wf p\<close> and Fr: \<open>smt_fragment p\<close> and R: \<open>smt_repr_ok p\<close> and B: \<open>tr_bounded p\<close>
    and NF: \<open>tr_fuel p \<le> F\<close>
  shows \<open>tr_pre F p\<close>
proof -
  let ?ds = \<open>SmtProblem_defs p\<close>
  have mb: \<open>margs (SmtDef_body e) * margs (SmtDef_body e) \<le> F \<and> margs (SmtDef_body e) \<le> F\<close> if \<open>e \<in> set ?ds\<close> for e
    using tr_fuel_ge(7)[OF that] NF by simp
  have D: \<open>defs_ok p F\<close>
    unfolding defs_ok_def
  proof (intro allI impI conjI)
    fix d assume d: \<open>d < length ?ds\<close>
    show \<open>smt_tsort (SmtProblem_funs p) (take d ?ds) (SmtDef_params (?ds ! d)) (SmtDef_body (?ds ! d)) \<noteq> None\<close>
      using W d by (simp add: smt_wf_def Let_def)
    have r: \<open>length (SmtDef_params (?ds ! d)) < 2 ^ 63 \<and> smt_term_repr (SmtDef_body (?ds ! d))\<close>
      using R nth_mem[OF d] unfolding smt_repr_ok_def by blast
    then show \<open>smt_term_repr (SmtDef_body (?ds ! d))\<close> \<open>length (SmtDef_params (?ds ! d)) < 2 ^ 64\<close> by simp_all
    show \<open>margs (SmtDef_body (?ds ! d)) \<le> F\<close> \<open>margs (SmtDef_body (?ds ! d)) * margs (SmtDef_body (?ds ! d)) \<le> F\<close>
      using mb[OF nth_mem[OF d]] by simp_all
  qed
  have defs: \<open>tok p F d 0 d (SmtDef_body (?ds ! d)) \<and> Suc (dep p d (SmtDef_body (?ds ! d))) \<le> F\<close>
    if d: \<open>d < length ?ds\<close> and e: \<open>SmtDef_params (?ds ! d) = []\<close> for d
  proof
    have \<open>smt_tsort (SmtProblem_funs p) (take d ?ds) (SmtDef_params (?ds ! d)) (SmtDef_body (?ds ! d)) =
            Some (SmtDef_ret (?ds ! d))\<close>
      using W d unfolding smt_wf_def Let_def by blast
    then have t: \<open>smt_tsort (SmtProblem_funs p) (take d ?ds) [] (SmtDef_body (?ds ! d)) \<noteq> None\<close>
      using e by simp
    show \<open>tok p F d 0 d (SmtDef_body (?ds ! d))\<close>
      using tok_of_wf(1)[OF D t] D d by (simp add: defs_ok_def)
    show \<open>Suc (dep p d (SmtDef_body (?ds ! d))) \<le> F\<close> using tr_fuel_ge(10)[OF d] NF by simp
  qed
  have asserts: \<open>tok p F (length ?ds) 0 (length ?ds) t \<and> Suc (dep p (length ?ds) t) \<le> F\<close>
    if t: \<open>t \<in> set (SmtProblem_asserts p)\<close> for t
  proof
    have s: \<open>smt_tsort (SmtProblem_funs p) (take (length ?ds) ?ds) [] t \<noteq> None\<close>
      using W t by (simp add: smt_wf_def Let_def)
    have m: \<open>margs t * margs t \<le> F\<close> \<open>margs t \<le> F\<close> using tr_fuel_ge(8)[OF t] NF by simp_all
    show \<open>tok p F (length ?ds) 0 (length ?ds) t\<close>
      using tok_of_wf(1)[OF D s] R t m by (simp add: smt_repr_ok_def)
    show \<open>Suc (dep p (length ?ds) t) \<le> F\<close> using tr_fuel_ge(11)[OF t] NF by simp
  qed
  have bq: \<open>bnd (tr_state_m p)\<close> using tr_main(3)[OF W Fr B] .
  show ?thesis
    unfolding tr_pre_def Let_def
    using defs asserts R tr_fuel_ge(2,3)[of p] NF D bq by (auto simp: smt_repr_ok_def defs_ok_def)
qed

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>in_fragment\<close>.\<close>
lemma in_fragment_pre:
  assumes R: \<open>smt_repr_ok p\<close> and NF: \<open>tr_fuel p \<le> F\<close>
  shows \<open>if_pre F p\<close>
proof -
  have d: \<open>length (SmtDef_params e) < 2 ^ 64 \<and> length (SmtDef_params e) \<le> F \<and> fok F (SmtDef_body e) \<and> Suc (size (SmtDef_body e)) \<le> F\<close>
    if e: \<open>e \<in> set (SmtProblem_defs p)\<close> for e
    using tr_fuel_ge(6,7)[OF e] NF R e fok_of_repr[of \<open>SmtDef_body e\<close> F] by (auto simp: smt_repr_ok_def)
  have a: \<open>fok F t\<close> if t: \<open>t \<in> set (SmtProblem_asserts p)\<close> for t
    using tr_fuel_ge(8)[OF t] NF R t fok_of_repr[of t F] by (auto simp: smt_repr_ok_def)
  have g: \<open>length (SmtFun_args g) < 2 ^ 64 \<and> length (SmtFun_args g) \<le> F\<close> if g: \<open>g \<in> set (SmtProblem_funs p)\<close> for g
    using tr_fuel_ge(5)[OF g] NF R g by (auto simp: smt_repr_ok_def)
  show ?thesis unfolding if_pre_def using d a g R NF tr_fuel_ge(1-3,9)[of p] by (auto simp: smt_repr_ok_def)
qed

text \<open>The facts the top-level proof supplies imply the precondition of \<^verbatim>\<open>tr_model\<close>. The model \<open>m\<close>
  of the translation must have at most as many entries as the translation has terms, each with
  at most as many arguments as some term (\<^verbatim>\<open>build_model\<close> makes one entry per term with the
  arguments of the term), and its values must be term indices.\<close>
lemma tr_model_pre:
  assumes S: \<open>sizes_ok (tr_problem_m p)\<close> and R: \<open>smt_repr_ok p\<close> and NF: \<open>tr_fuel p \<le> F\<close>
    and V: \<open>\<forall>e \<in> set (Model_entries m). unat (Entry_val e) < length (Problem_terms (tr_problem_m p)) \<and>
              (\<forall>x \<in> set (Entry_args e). unat x < length (Problem_terms (tr_problem_m p)))\<close>
    and E: \<open>length (Model_entries m) \<le> length (Problem_terms (tr_problem_m p))\<close>
    and A: \<open>\<forall>e \<in> set (Model_entries m). \<exists>t \<in> set (Problem_terms (tr_problem_m p)). length (Entry_args e) \<le> length (Term_args t)\<close>
  shows \<open>tm_pre F p m\<close>
proof -
  let ?T = \<open>Problem_terms (tr_problem_m p)\<close>
  have T: \<open>length ?T < 2 ^ 63\<close> \<open>\<forall>t \<in> set ?T. length (Term_args t) < 2 ^ 63\<close> using S by (simp_all add: sizes_ok_def)
  have e: \<open>length (Entry_args e) < 2 ^ 64 \<and> length (Entry_args e) \<le> F \<and>
        unat (Entry_val e) < 2 ^ 63 \<and> (\<forall>x \<in> set (Entry_args e). unat x < 2 ^ 63)\<close> if e: \<open>e \<in> set (Model_entries m)\<close> for e
  proof -
    obtain t where t: \<open>t \<in> set ?T\<close> \<open>length (Entry_args e) \<le> length (Term_args t)\<close> using A e by blast
    show ?thesis using t T tr_fuel_ge(13)[OF t(1)] NF V e by fastforce
  qed
  show ?thesis unfolding tm_pre_def using e E T(1) tr_fuel_ge(1,4,12)[of p] NF R by (auto simp: smt_repr_ok_def)
qed


end

end

