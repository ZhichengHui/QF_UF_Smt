theory QFUF_SmtModel
  imports "QFUF_CoreSpec.QFUF_CoreSpec"
begin

section \<open>The translation of general problems: functional model\<close>

text \<open>HOL functions that compute what the Rust functions of the translation (\<^verbatim>\<open>tr_problem\<close>,
  \<^verbatim>\<open>tr_model\<close> and their callees in \<^verbatim>\<open>core/src/lib.rs\<close>) compute. Indices and the next unused
  function symbol (\<^verbatim>\<open>usize\<close> in Rust) are natural numbers; the terms, atoms and clauses are the
  records of the translation, whose fields are words.\<close>

text \<open>\<^verbatim>\<open>Enc\<close>: a term index or a literal (atom index and polarity).\<close>
datatype enc_m = ETerm nat | ELit nat bool

text \<open>\<^verbatim>\<open>Tr\<close>: terms, atoms, clauses built so far, and the next unused function symbol.\<close>
datatype st = St (st_terms: \<open>Term list\<close>) (st_atoms: \<open>Atom list\<close>) (st_clauses: \<open>Clause list\<close>) (st_next: nat)

definition add_term_m :: \<open>st \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> st \<times> nat\<close> where
  \<open>add_term_m s f args \<equiv>
     (St (st_terms s @ [make_Term (word_of_nat f) (map word_of_nat args)]) (st_atoms s) (st_clauses s) (st_next s),
      length (st_terms s))\<close>

definition add_atom_m :: \<open>st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> st \<times> nat\<close> where
  \<open>add_atom_m s l r \<equiv>
     (St (st_terms s) (st_atoms s @ [make_Atom (word_of_nat l) (word_of_nat r)]) (st_clauses s) (st_next s),
      length (st_atoms s))\<close>

definition add_clause_m :: \<open>st \<Rightarrow> Lit list \<Rightarrow> st\<close> where
  \<open>add_clause_m s ls \<equiv> St (st_terms s) (st_atoms s) (st_clauses s @ [make_Clause ls]) (st_next s)\<close>

definition new_const_m :: \<open>st \<Rightarrow> st \<times> nat\<close> where
  \<open>new_const_m s \<equiv> add_term_m (St (st_terms s) (st_atoms s) (st_clauses s) (Suc (st_next s))) (st_next s) []\<close>

definition new_lit_m :: \<open>st \<Rightarrow> st \<times> nat\<close> where
  \<open>new_lit_m s \<equiv> (let r = new_const_m s in add_atom_m (fst r) (snd r) 0)\<close>

definition lit_m :: \<open>nat \<Rightarrow> bool \<Rightarrow> Lit\<close> where
  \<open>lit_m a pos \<equiv> make_Lit (word_of_nat a) pos\<close>

fun enc_lit_m :: \<open>enc_m \<Rightarrow> nat \<times> bool\<close> where
  \<open>enc_lit_m (ELit a pos) = (a, pos)\<close>
| \<open>enc_lit_m (ETerm i) = (0, True)\<close>

fun is_lit_m :: \<open>enc_m \<Rightarrow> bool\<close> where
  \<open>is_lit_m (ELit a pos) = True\<close>
| \<open>is_lit_m (ETerm i) = False\<close>

fun enc_term_m :: \<open>st \<Rightarrow> enc_m \<Rightarrow> st \<times> nat\<close> where
  \<open>enc_term_m s (ETerm i) = (s, i)\<close>
| \<open>enc_term_m s (ELit a pos) =
     (let r = new_const_m s; c = snd r; r1 = add_atom_m (fst r) c 0; r2 = add_atom_m (fst r1) c 1;
          s1 = add_clause_m (fst r2) [lit_m a (\<not> pos), lit_m (snd r1) True];
          s2 = add_clause_m s1 [lit_m a pos, lit_m (snd r2) True]
      in (s2, c))\<close>

text \<open>The clause of \<^verbatim>\<open>gate_andor\<close> for the literal \<open>l\<close> of the loop.\<close>
definition andor_cl_m :: \<open>nat \<Rightarrow> bool \<Rightarrow> nat \<times> bool \<Rightarrow> Lit list\<close> where
  \<open>andor_cl_m v cj l \<equiv>
     if cj then [lit_m v False, lit_m (fst l) (snd l)] else [lit_m v True, lit_m (fst l) (\<not> snd l)]\<close>

definition gate_andor_m :: \<open>st \<Rightarrow> (nat \<times> bool) list \<Rightarrow> bool \<Rightarrow> st \<times> enc_m\<close> where
  \<open>gate_andor_m s ls cj \<equiv>
     (let r = new_lit_m s; v = snd r;
          s1 = foldl (\<lambda>s l. add_clause_m s (andor_cl_m v cj l)) (fst r) ls;
          big = lit_m v cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) ls
      in (add_clause_m s1 big, ELit v True))\<close>

definition gate_xor_m :: \<open>st \<Rightarrow> nat \<times> bool \<Rightarrow> nat \<times> bool \<Rightarrow> st \<times> (nat \<times> bool)\<close> where
  \<open>gate_xor_m s x y \<equiv>
     (let r = new_lit_m s; v = snd r; a = fst x; pa = snd x; b = fst y; pb = snd y;
          s1 = add_clause_m (fst r) [lit_m v False, lit_m a pa, lit_m b pb];
          s2 = add_clause_m s1 [lit_m v False, lit_m a (\<not> pa), lit_m b (\<not> pb)];
          s3 = add_clause_m s2 [lit_m v True, lit_m a (\<not> pa), lit_m b pb];
          s4 = add_clause_m s3 [lit_m v True, lit_m a pa, lit_m b (\<not> pb)]
      in (s4, (v, True)))\<close>

definition gate_ite_m :: \<open>st \<Rightarrow> nat \<times> bool \<Rightarrow> nat \<times> bool \<Rightarrow> nat \<times> bool \<Rightarrow> st \<times> enc_m\<close> where
  \<open>gate_ite_m s c x y \<equiv>
     (let r = new_lit_m s; v = snd r; kc = fst c; pc = snd c; a = fst x; pa = snd x; b = fst y; pb = snd y;
          s1 = add_clause_m (fst r) [lit_m kc (\<not> pc), lit_m a (\<not> pa), lit_m v True];
          s2 = add_clause_m s1 [lit_m kc (\<not> pc), lit_m a pa, lit_m v False];
          s3 = add_clause_m s2 [lit_m kc pc, lit_m b (\<not> pb), lit_m v True];
          s4 = add_clause_m s3 [lit_m kc pc, lit_m b pb, lit_m v False]
      in (s4, ELit v True))\<close>

text \<open>The pairs \<open>(i, j)\<close>, \<open>i < j < n\<close>, visited by the two loops of \<^verbatim>\<open>enc_eq\<close>, in order: all of them
  for \<open>distinct\<close>, the neighbours \<open>j = i + 1\<close> for \<open>=\<close>.\<close>
definition eq_pairs_m :: \<open>nat \<Rightarrow> bool \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>eq_pairs_m n dist \<equiv>
     filter (\<lambda>(i, j). dist \<or> j = Suc i) (concat (map (\<lambda>i. map (\<lambda>j. (i, j)) [Suc i..<n]) [0..<n]))\<close>

definition eq_step_m :: \<open>enc_m list \<Rightarrow> bool \<Rightarrow> st \<times> (nat \<times> bool) list \<Rightarrow> nat \<times> nat \<Rightarrow> st \<times> (nat \<times> bool) list\<close> where
  \<open>eq_step_m es dist \<equiv> \<lambda>(s, ls) (i, j).
     if is_lit_m (es ! i) then
       (let r = gate_xor_m s (enc_lit_m (es ! i)) (enc_lit_m (es ! j))
        in (fst r, ls @ [(fst (snd r), if dist then snd (snd r) else \<not> snd (snd r))]))
     else
       (let r1 = enc_term_m s (es ! i); r2 = enc_term_m (fst r1) (es ! j); r3 = add_atom_m (fst r2) (snd r1) (snd r2)
        in (fst r3, ls @ [(snd r3, \<not> dist)]))\<close>

definition enc_eq_m :: \<open>st \<Rightarrow> enc_m list \<Rightarrow> bool \<Rightarrow> st \<times> enc_m\<close> where
  \<open>enc_eq_m s es dist \<equiv>
     (let r = foldl (eq_step_m es dist) (s, []) (eq_pairs_m (length es) dist) in gate_andor_m (fst r) (snd r) True)\<close>

definition xor_step_m :: \<open>st \<times> (nat \<times> bool) \<Rightarrow> enc_m \<Rightarrow> st \<times> (nat \<times> bool)\<close> where
  \<open>xor_step_m \<equiv> \<lambda>(s, acc) e. gate_xor_m s acc (enc_lit_m e)\<close>

definition implies_lits_m :: \<open>enc_m list \<Rightarrow> (nat \<times> bool) list\<close> where
  \<open>implies_lits_m es \<equiv>
     map (\<lambda>i. (fst (enc_lit_m (es ! i)), if i + 1 < length es then \<not> snd (enc_lit_m (es ! i)) else snd (enc_lit_m (es ! i))))
       [0..<length es]\<close>

definition ite_term_m :: \<open>st \<Rightarrow> enc_m list \<Rightarrow> st \<times> enc_m\<close> where
  \<open>ite_term_m s es \<equiv>
     (let kc = fst (enc_lit_m (es ! 0)); pc = snd (enc_lit_m (es ! 0));
          r = new_const_m s; c = snd r; ra = enc_term_m (fst r) (es ! 1); rb = enc_term_m (fst ra) (es ! 2);
          rka = add_atom_m (fst rb) c (snd ra); rkb = add_atom_m (fst rka) c (snd rb);
          s1 = add_clause_m (fst rkb) [lit_m kc (\<not> pc), lit_m (snd rka) True];
          s2 = add_clause_m s1 [lit_m kc pc, lit_m (snd rkb) True]
      in (s2, ETerm c))\<close>

definition enc_app_m :: \<open>st \<Rightarrow> SmtOp \<Rightarrow> enc_m list \<Rightarrow> st \<times> enc_m\<close> where
  \<open>enc_app_m s op es \<equiv>
     (case op of
        SmtOp_Not \<Rightarrow> (s, ELit (fst (enc_lit_m (es ! 0))) (\<not> snd (enc_lit_m (es ! 0))))
      | SmtOp_And \<Rightarrow> (gate_andor_m s (map enc_lit_m es) True)
      | SmtOp_Or \<Rightarrow> (gate_andor_m s (map enc_lit_m es) False)
      | SmtOp_Xor \<Rightarrow> (let r = foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es) in (fst r, ELit (fst (snd r)) (snd (snd r))))
      | SmtOp_Implies \<Rightarrow> (gate_andor_m s (implies_lits_m es) False)
      | SmtOp_Eq \<Rightarrow> (enc_eq_m s es False)
      | SmtOp_Distinct \<Rightarrow> (enc_eq_m s es True)
      | SmtOp_Ite \<Rightarrow> (if is_lit_m (es ! 1) then gate_ite_m s (enc_lit_m (es ! 0)) (enc_lit_m (es ! 1)) (enc_lit_m (es ! 2))
                else ite_term_m s es)
      | _ \<Rightarrow> (s, ELit 0 True))\<close>

lemma enc_app_m_simps [simp]:
  \<open>enc_app_m s SmtOp_Not es = (s, ELit (fst (enc_lit_m (es ! 0))) (\<not> snd (enc_lit_m (es ! 0))))\<close>
  \<open>enc_app_m s SmtOp_And es = gate_andor_m s (map enc_lit_m es) True\<close>
  \<open>enc_app_m s SmtOp_Or es = gate_andor_m s (map enc_lit_m es) False\<close>
  \<open>enc_app_m s SmtOp_Xor es =
       (let r = foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es) in (fst r, ELit (fst (snd r)) (snd (snd r))))\<close>
  \<open>enc_app_m s SmtOp_Implies es = gate_andor_m s (implies_lits_m es) False\<close>
  \<open>enc_app_m s SmtOp_Eq es = enc_eq_m s es False\<close>
  \<open>enc_app_m s SmtOp_Distinct es = enc_eq_m s es True\<close>
  \<open>enc_app_m s SmtOp_Ite es =
       (if is_lit_m (es ! 1) then gate_ite_m s (enc_lit_m (es ! 0)) (enc_lit_m (es ! 1)) (enc_lit_m (es ! 2))
        else ite_term_m s es)\<close>
  \<open>enc_app_m s SmtOp_Concat es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_Extract a0 a1) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvnot es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvand es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvor es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvneg es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvadd es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvmul es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvudiv es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvurem es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvshl es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvlshr es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvult es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvnand es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvnor es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvxor es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvxnor es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvcomp es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsub es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsdiv es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsrem es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsmod es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvashr es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_Repeat a0) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_ZeroExtend a0) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_SignExtend a0) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_RotateLeft a0) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s (SmtOp_RotateRight a0) es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvule es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvugt es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvuge es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvslt es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsle es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsgt es = (s, ELit 0 True)\<close>
  \<open>enc_app_m s SmtOp_Bvsge es = (s, ELit 0 True)\<close>
  by (simp_all add: enc_app_m_def)

text \<open>The loop of \<^verbatim>\<open>enc\<close> that turns the translated arguments of a declared symbol into terms.\<close>
definition enc_terms_m :: \<open>st \<Rightarrow> enc_m list \<Rightarrow> st \<times> nat list\<close> where
  \<open>enc_terms_m s es \<equiv> foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s, []) es\<close>

text \<open>\<^verbatim>\<open>enc\<close> and \<^verbatim>\<open>enc_args\<close>. \<open>dm\<close>: the translation of each definition without parameters;
  \<open>env\<close>: the translations of the parameters in scope; \<open>n\<close>: only definitions below \<open>n\<close> are expanded
  (the Rust function has no such bound; in a well-sorted problem a definition refers only to earlier
  ones, so the bound is never reached).\<close>
function (sequential) tr_term_m :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm \<Rightarrow> st \<times> enc_m\<close>
  and tr_args_m :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> enc_m list \<Rightarrow> nat \<Rightarrow> st \<Rightarrow> SmtTerm list \<Rightarrow> st \<times> enc_m list\<close>
  where
  \<open>tr_term_m p dm env n s (SmtTerm_BoolConst b) = (s, ELit 0 b)\<close>
| \<open>tr_term_m p dm env n s (SmtTerm_BvConst bs) = (s, ELit 0 True)\<close>
| \<open>tr_term_m p dm env n s (SmtTerm_Param k) = (s, env ! unat k)\<close>
| \<open>tr_term_m p dm env n s (SmtTerm_Fun f args) =
     (let r = tr_args_m p dm env n s args; r2 = enc_terms_m (fst r) (snd r); r3 = add_term_m (fst r2) (unat f) (snd r2) in
      if SmtFun_ret (SmtProblem_funs p ! unat f) = SmtSort_Bool
      then (let r4 = add_atom_m (fst r3) (snd r3) 0 in (fst r4, ELit (snd r4) True))
      else (fst r3, ETerm (snd r3)))\<close>
| \<open>tr_term_m p dm env n s (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then (s, dm ! unat d)
      else if unat d < n then
        (let r = tr_args_m p dm env n s args in
         tr_term_m p dm (snd r) (unat d) (fst r) (SmtDef_body (SmtProblem_defs p ! unat d)))
      else (s, ELit 0 True))\<close>
| \<open>tr_term_m p dm env n s (SmtTerm_App op args) =
     (let r = tr_args_m p dm env n s args in enc_app_m (fst r) op (snd r))\<close>
| \<open>tr_args_m p dm env n s [] = (s, [])\<close>
| \<open>tr_args_m p dm env n s (a # rest) =
     (let r1 = tr_term_m p dm env n s a; r2 = tr_args_m p dm env n (fst r1) rest in (fst r2, snd r1 # snd r2))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, _, _, n, _, _) \<Rightarrow> n | Inr (_, _, _, n, _, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, _, _, _, t) \<Rightarrow> size t | Inr (_, _, _, _, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

text \<open>The state after the first lines of \<^verbatim>\<open>tr_problem\<close>: TRUE and FALSE (terms 0 and 1), the atoms
  \<open>TRUE = TRUE\<close> and \<open>TRUE = FALSE\<close>, and the clause \<open>\<not> (TRUE = FALSE)\<close>.\<close>
definition tr_init_m :: \<open>SmtProblem \<Rightarrow> st\<close> where
  \<open>tr_init_m p \<equiv>
     (let nf = length (SmtProblem_funs p);
          s0 = St [] [] [] (nf + 2);
          s1 = fst (add_term_m s0 nf []); s2 = fst (add_term_m s1 (nf + 1) []);
          s3 = fst (add_atom_m s2 0 0); s4 = fst (add_atom_m s3 0 1)
      in add_clause_m s4 [lit_m 1 False])\<close>

definition tr_defs_step :: \<open>SmtProblem \<Rightarrow> st \<times> enc_m list \<Rightarrow> nat \<Rightarrow> st \<times> enc_m list\<close> where
  \<open>tr_defs_step p \<equiv> \<lambda>(s, dm) d.
     if SmtDef_params (SmtProblem_defs p ! d) = [] then
       (let r = tr_term_m p dm [] d s (SmtDef_body (SmtProblem_defs p ! d)) in (fst r, dm @ [snd r]))
     else (s, dm @ [ELit 0 True])\<close>

definition tr_defs_m :: \<open>SmtProblem \<Rightarrow> st \<times> enc_m list\<close> where
  \<open>tr_defs_m p \<equiv> foldl (tr_defs_step p) (tr_init_m p, []) [0..<length (SmtProblem_defs p)]\<close>

definition tr_asserts_step :: \<open>SmtProblem \<Rightarrow> enc_m list \<Rightarrow> st \<Rightarrow> SmtTerm \<Rightarrow> st\<close> where
  \<open>tr_asserts_step p dm \<equiv> \<lambda>s t.
     (let r = tr_term_m p dm [] (length (SmtProblem_defs p)) s t; l = enc_lit_m (snd r)
      in add_clause_m (fst r) [lit_m (fst l) (snd l)])\<close>

definition tr_asserts_m :: \<open>SmtProblem \<Rightarrow> st \<times> enc_m list \<Rightarrow> st\<close> where
  \<open>tr_asserts_m p sd \<equiv> foldl (tr_asserts_step p (snd sd)) (fst sd) (SmtProblem_asserts p)\<close>

definition tr_state_m :: \<open>SmtProblem \<Rightarrow> st\<close> where
  \<open>tr_state_m p \<equiv> tr_asserts_m p (tr_defs_m p)\<close>

definition tr_problem_m :: \<open>SmtProblem \<Rightarrow> Problem\<close> where
  \<open>tr_problem_m p \<equiv> (let s = tr_state_m p in make_Problem (st_terms s) (st_atoms s) (st_clauses s))\<close>

subsection \<open>Models\<close>

definition const_value_m :: \<open>Model \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>const_value_m m f \<equiv>
     (case List.find (\<lambda>e. unat (Entry_fun e) = f \<and> Entry_args e = []) (Model_entries m) of
        Some e \<Rightarrow> unat (Entry_val e) | None \<Rightarrow> 0)\<close>

definition dsize_step :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> nat\<close> where
  \<open>dsize_step n x \<equiv> if n \<le> unat x then unat x + 1 else n\<close>

definition domain_size_m :: \<open>Model \<Rightarrow> nat\<close> where
  \<open>domain_size_m m \<equiv> foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) 1 (Model_entries m)\<close>

definition value_of_m :: \<open>SmtSort \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtValue\<close> where
  \<open>value_of_m srt v t \<equiv>
     (case srt of
        SmtSort_Bool \<Rightarrow> (SmtValue_Bool (v = t))
      | _ \<Rightarrow> (SmtValue_Elem (word_of_nat v)))\<close>

lemma value_of_m_simps [simp]:
  \<open>value_of_m SmtSort_Bool v t = SmtValue_Bool (v = t)\<close>
  \<open>value_of_m (SmtSort_BitVec a0) v t = SmtValue_Elem (word_of_nat v)\<close>
  \<open>value_of_m (SmtSort_Uninterpreted a0) v t = SmtValue_Elem (word_of_nat v)\<close>
  by (simp_all add: value_of_m_def)

text \<open>The entry \<open>e\<close> passes the test of \<^verbatim>\<open>tr_interp\<close> for the symbol with signature \<open>sg\<close>.\<close>
definition entry_ok_m :: \<open>SmtFun \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Entry \<Rightarrow> bool\<close> where
  \<open>entry_ok_m sg f t u e \<equiv>
     unat (Entry_fun e) = f \<and> length (Entry_args e) = length (SmtFun_args sg) \<and>
     (\<forall>k < length (Entry_args e). SmtFun_args sg ! k = SmtSort_Bool \<longrightarrow>
        unat (Entry_args e ! k) = t \<or> unat (Entry_args e ! k) = u)\<close>

definition tr_entry_m :: \<open>SmtFun \<Rightarrow> nat \<Rightarrow> Entry \<Rightarrow> SmtEntry\<close> where
  \<open>tr_entry_m sg t e \<equiv>
     make_SmtEntry (map (\<lambda>k. value_of_m (SmtFun_args sg ! k) (unat (Entry_args e ! k)) t) [0..<length (Entry_args e)])
       (value_of_m (SmtFun_ret sg) (unat (Entry_val e)) t)\<close>

definition tr_interp_m :: \<open>SmtProblem \<Rightarrow> Model \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SmtInterp\<close> where
  \<open>tr_interp_m p m f t u \<equiv>
     (let sg = SmtProblem_funs p ! f in
      make_SmtInterp (map (tr_entry_m sg t) (filter (entry_ok_m sg f t u) (Model_entries m)))
        (value_of_m (SmtFun_ret sg) 0 t))\<close>

definition tr_model_m :: \<open>SmtProblem \<Rightarrow> Model \<Rightarrow> SmtModel\<close> where
  \<open>tr_model_m p m \<equiv>
     (let nf = length (SmtProblem_funs p); t = const_value_m m nf; u = const_value_m m (nf + 1);
          n = domain_size_m m
      in make_SmtModel (replicate (unat (SmtProblem_num_sorts p)) (word_of_nat n))
           (map (\<lambda>f. tr_interp_m p m f t u) [0..<nf]))\<close>

section \<open>Structure of the translation\<close>

definition st_prob :: \<open>st \<Rightarrow> Problem\<close> where
  \<open>st_prob s \<equiv> make_Problem (st_terms s) (st_atoms s) (st_clauses s)\<close>

text \<open>\<open>s'\<close> extends \<open>s\<close>.\<close>
definition pre :: \<open>st \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>pre s s' \<equiv> (\<exists>E. st_terms s' = st_terms s @ E) \<and> (\<exists>E. st_atoms s' = st_atoms s @ E) \<and>
     (\<exists>E. st_clauses s' = st_clauses s @ E) \<and> st_next s \<le> st_next s' \<and>
     st_next s' + length (st_terms s) \<le> st_next s + length (st_terms s')\<close>

lemma pre_refl: \<open>pre s s\<close>
  by (auto simp: pre_def)

lemma pre_trans: \<open>pre s1 s2 \<Longrightarrow> pre s2 s3 \<Longrightarrow> pre s1 s3\<close>
  unfolding pre_def by (elim conjE exE) (intro conjI exI; simp)

definition bnd :: \<open>st \<Rightarrow> bool\<close> where
  \<open>bnd s \<equiv> length (st_terms s) < 2 ^ 64 \<and> length (st_atoms s) < 2 ^ 64 \<and> st_next s < 2 ^ 64\<close>

lemma bnd_pre: \<open>pre s s' \<Longrightarrow> bnd s' \<Longrightarrow> bnd s\<close>
  unfolding pre_def bnd_def by auto

lemma unat_wn: \<open>x < 2 ^ 64 \<Longrightarrow> unat (word_of_nat x :: 64 word) = x\<close>
  by (simp add: unat_of_nat_eq)

subsection \<open>The primitive operations\<close>

lemma new_const_eq:
  \<open>new_const_m s = (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []]) (st_atoms s) (st_clauses s) (Suc (st_next s)),
     length (st_terms s))\<close>
  by (simp add: new_const_m_def add_term_m_def)

lemma new_lit_eq:
  \<open>new_lit_m s = (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
     (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) 0]) (st_clauses s) (Suc (st_next s)), length (st_atoms s))\<close>
  by (simp add: new_lit_m_def new_const_eq add_atom_m_def)

lemma fold_clauses:
  \<open>foldl (\<lambda>s l. add_clause_m s (h l)) s ls = St (st_terms s) (st_atoms s) (st_clauses s @ map (\<lambda>l. make_Clause (h l)) ls) (st_next s)\<close>
  by (induction ls arbitrary: s) (simp_all add: add_clause_m_def)

lemma enc_term_lit_eq:
  \<open>enc_term_m s (ELit a pos) =
     (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) 0, make_Atom (word_of_nat (length (st_terms s))) 1])
       (st_clauses s @ [make_Clause [lit_m a (\<not> pos), lit_m (length (st_atoms s)) True],
                        make_Clause [lit_m a pos, lit_m (Suc (length (st_atoms s))) True]]) (Suc (st_next s)),
      length (st_terms s))\<close>
  by (simp add: new_const_eq add_atom_m_def add_clause_m_def Let_def)

lemma gate_andor_eq:
  \<open>gate_andor_m s ls cj =
     (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) 0])
       (st_clauses s @ map (\<lambda>l. make_Clause (andor_cl_m (length (st_atoms s)) cj l)) ls @
          [make_Clause (lit_m (length (st_atoms s)) cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) ls)])
       (Suc (st_next s)), ELit (length (st_atoms s)) True)\<close>
  by (simp add: gate_andor_m_def new_lit_eq fold_clauses Let_def) (simp add: add_clause_m_def)

lemma gate_xor_eq:
  \<open>gate_xor_m s (a, pa) (b, pb) =
     (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) 0])
       (st_clauses s @ [make_Clause [lit_m (length (st_atoms s)) False, lit_m a pa, lit_m b pb],
          make_Clause [lit_m (length (st_atoms s)) False, lit_m a (\<not> pa), lit_m b (\<not> pb)],
          make_Clause [lit_m (length (st_atoms s)) True, lit_m a (\<not> pa), lit_m b pb],
          make_Clause [lit_m (length (st_atoms s)) True, lit_m a pa, lit_m b (\<not> pb)]])
       (Suc (st_next s)), (length (st_atoms s), True))\<close>
  by (simp add: gate_xor_m_def new_lit_eq add_clause_m_def Let_def)

lemma gate_ite_eq:
  \<open>gate_ite_m s (kc, pc) (a, pa) (b, pb) =
     (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) 0])
       (st_clauses s @ [make_Clause [lit_m kc (\<not> pc), lit_m a (\<not> pa), lit_m (length (st_atoms s)) True],
          make_Clause [lit_m kc (\<not> pc), lit_m a pa, lit_m (length (st_atoms s)) False],
          make_Clause [lit_m kc pc, lit_m b (\<not> pb), lit_m (length (st_atoms s)) True],
          make_Clause [lit_m kc pc, lit_m b pb, lit_m (length (st_atoms s)) False]])
       (Suc (st_next s)), ELit (length (st_atoms s)) True)\<close>
  by (simp add: gate_ite_m_def new_lit_eq add_clause_m_def Let_def)

lemma ite_term_eq:
  \<open>es ! 1 = ETerm k1 \<Longrightarrow> es ! 2 = ETerm k2 \<Longrightarrow> enc_lit_m (es ! 0) = (kc, pc) \<Longrightarrow>
   ite_term_m s es =
     (St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat (length (st_terms s))) (word_of_nat k1),
                      make_Atom (word_of_nat (length (st_terms s))) (word_of_nat k2)])
       (st_clauses s @ [make_Clause [lit_m kc (\<not> pc), lit_m (length (st_atoms s)) True],
          make_Clause [lit_m kc pc, lit_m (Suc (length (st_atoms s))) True]])
       (Suc (st_next s)), ETerm (length (st_terms s)))\<close>
  by (simp add: ite_term_m_def new_const_eq add_atom_m_def add_clause_m_def Let_def)

subsection \<open>Well-formed states\<close>

text \<open>The terms form a DAG in index order and use function symbols below the next unused one; the
  indices of atoms and literals are in bounds; terms 0 and 1 and atom 0 exist; the declared symbols
  are below \<open>nf\<close>, and every new symbol has a term.\<close>
definition st_wf :: \<open>nat \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>st_wf nf s \<equiv>
     (\<forall>i < length (st_terms s). unat (Term_fun (st_terms s ! i)) < st_next s \<and>
        (\<forall>x \<in> set (Term_args (st_terms s ! i)). unat x < i)) \<and>
     (\<forall>at \<in> set (st_atoms s). unat (Atom_lhs at) < length (st_terms s) \<and> unat (Atom_rhs at) < length (st_terms s)) \<and>
     (\<forall>c \<in> set (st_clauses s). \<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (st_atoms s)) \<and>
     2 \<le> length (st_terms s) \<and> 1 \<le> length (st_atoms s) \<and> nf + 2 \<le> st_next s \<and> st_next s \<le> nf + length (st_terms s)\<close>

lemma wf_extend:
  assumes \<open>st_wf nf s\<close> \<open>s' = St (st_terms s @ T) (st_atoms s @ A) (st_clauses s @ C) n'\<close>
    \<open>\<forall>i < length T. unat (Term_fun (T ! i)) < n' \<and> (\<forall>x \<in> set (Term_args (T ! i)). unat x < length (st_terms s) + i)\<close>
    \<open>\<forall>at \<in> set A. unat (Atom_lhs at) < length (st_terms s) + length T \<and> unat (Atom_rhs at) < length (st_terms s) + length T\<close>
    \<open>\<forall>c \<in> set C. \<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (st_atoms s) + length A\<close>
    \<open>st_next s \<le> n'\<close> \<open>n' \<le> nf + length (st_terms s) + length T\<close>
  shows \<open>st_wf nf s'\<close>
proof -
  have t: \<open>\<forall>i < length (st_terms s'). unat (Term_fun (st_terms s' ! i)) < st_next s' \<and>
        (\<forall>x \<in> set (Term_args (st_terms s' ! i)). unat x < i)\<close>
  proof (intro allI impI)
    fix i assume i: \<open>i < length (st_terms s')\<close>
    show \<open>unat (Term_fun (st_terms s' ! i)) < st_next s' \<and> (\<forall>x \<in> set (Term_args (st_terms s' ! i)). unat x < i)\<close>
    proof (cases \<open>i < length (st_terms s)\<close>)
      case True
      then show ?thesis using assms(1,2,6) by (auto simp: st_wf_def nth_append)
    next
      case False
      then show ?thesis using assms(2,3) i
      proof -
        obtain j where j: \<open>i = length (st_terms s) + j\<close> \<open>j < length T\<close>
          using False i assms(2) by (auto dest!: le_Suc_ex simp: not_less)
        then show ?thesis using assms(2,3) by (auto simp: nth_append)
      qed
    qed
  qed
  show ?thesis using t assms(1,2,4,5,6,7) unfolding st_wf_def by fastforce
qed

definition enc_wf :: \<open>st \<Rightarrow> enc_m \<Rightarrow> bool\<close> where
  \<open>enc_wf s e \<equiv> (case e of ETerm k \<Rightarrow> k < length (st_terms s) | ELit a pos \<Rightarrow> a < length (st_atoms s))\<close>

definition lit_wf :: \<open>st \<Rightarrow> nat \<times> bool \<Rightarrow> bool\<close> where
  \<open>lit_wf s l \<equiv> fst l < length (st_atoms s)\<close>

lemma enc_wf_pre: \<open>pre s s' \<Longrightarrow> enc_wf s e \<Longrightarrow> enc_wf s' e\<close>
  by (cases e) (auto simp: pre_def enc_wf_def)

lemma lit_wf_pre: \<open>pre s s' \<Longrightarrow> lit_wf s l \<Longrightarrow> lit_wf s' l\<close>
  by (auto simp: pre_def lit_wf_def)

lemma enc_lit_wf: \<open>st_wf nf s \<Longrightarrow> enc_wf s e \<Longrightarrow> lit_wf s (enc_lit_m e)\<close>
  by (cases e) (auto simp: st_wf_def enc_wf_def lit_wf_def)

subsection \<open>Prefixes\<close>

lemma pre_St: \<open>st_next s \<le> n' \<Longrightarrow> n' \<le> st_next s + length T \<Longrightarrow> pre s (St (st_terms s @ T) (st_atoms s @ A) (st_clauses s @ C) n')\<close>
  by (auto simp: pre_def)

lemma pre_add_term: \<open>pre s s1 \<Longrightarrow> pre s (fst (add_term_m s1 f args))\<close>
  by (auto simp: add_term_m_def pre_def)

lemma pre_add_atom: \<open>pre s s1 \<Longrightarrow> pre s (fst (add_atom_m s1 l r))\<close>
  by (auto simp: add_atom_m_def pre_def)

lemma pre_add_clause: \<open>pre s s1 \<Longrightarrow> pre s (add_clause_m s1 c)\<close>
  by (auto simp: add_clause_m_def pre_def)

lemma pre_new_const: \<open>pre s s1 \<Longrightarrow> pre s (fst (new_const_m s1))\<close>
  by (auto simp: new_const_eq pre_def)

lemma pre_enc_term: \<open>pre s s1 \<Longrightarrow> pre s (fst (enc_term_m s1 e))\<close>
  by (cases e) (auto simp: pre_def enc_term_lit_eq simp del: enc_term_m.simps(2))

lemma pre_gate_andor: \<open>pre s s1 \<Longrightarrow> pre s (fst (gate_andor_m s1 ls cj))\<close>
  by (auto simp: gate_andor_eq pre_def)

lemma pre_gate_xor: \<open>pre s s1 \<Longrightarrow> pre s (fst (gate_xor_m s1 x y))\<close>
  by (cases x; cases y) (auto simp: gate_xor_eq pre_def)

lemma pre_gate_ite: \<open>pre s s1 \<Longrightarrow> pre s (fst (gate_ite_m s1 c x y))\<close>
  by (cases c; cases x; cases y) (auto simp: gate_ite_eq pre_def)

lemma pre_ite_term: \<open>pre s s1 \<Longrightarrow> pre s (fst (ite_term_m s1 es))\<close>
  unfolding ite_term_m_def Let_def
  by (simp, intro pre_add_clause pre_add_atom pre_enc_term pre_new_const)

lemma pre_eq_fold: \<open>pre s (fst sl) \<Longrightarrow> pre s (fst (foldl (eq_step_m es dst) sl prs))\<close>
proof (induction prs arbitrary: sl)
  case Nil
  then show ?case by simp
next
  case (Cons ij prs)
  have \<open>pre s (fst (eq_step_m es dst sl ij))\<close>
    using Cons.prems unfolding eq_step_m_def
    by (cases sl; cases ij) (auto simp: Let_def intro: pre_gate_xor pre_add_atom pre_enc_term)
  then show ?case using Cons.IH by simp
qed

lemma pre_xor_fold: \<open>pre s (fst sa) \<Longrightarrow> pre s (fst (foldl xor_step_m sa es))\<close>
proof (induction es arbitrary: sa)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have \<open>pre s (fst (xor_step_m sa e))\<close> using Cons.prems unfolding xor_step_m_def
    by (cases sa) (auto intro: pre_gate_xor)
  then show ?case using Cons.IH by simp
qed

lemma pre_enc_terms: \<open>pre s (fst st0) \<Longrightarrow>
    pre s (fst (foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) st0 es)) \<and>
    length (snd (foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) st0 es)) = length (snd st0) + length es\<close>
proof (induction es arbitrary: st0)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  show ?case using Cons.IH[of \<open>(fst (enc_term_m (fst st0) e), snd st0 @ [snd (enc_term_m (fst st0) e)])\<close>] Cons.prems
    by (cases st0) (auto simp: Let_def intro: pre_enc_term)
qed

lemma pre_enc_eq: \<open>pre s s1 \<Longrightarrow> pre s (fst (enc_eq_m s1 es dst))\<close>
  unfolding enc_eq_m_def Let_def by (intro pre_gate_andor pre_eq_fold) simp

lemma pre_enc_app: \<open>pre s s1 \<Longrightarrow> pre s (fst (enc_app_m s1 op es))\<close>
  by (cases op) (auto simp: Let_def intro: pre_gate_andor pre_gate_ite pre_ite_term pre_enc_eq pre_xor_fold)

lemma tr_pre:
  shows \<open>tr_term_m p dm env n s t = (s', e) \<Longrightarrow> pre s s'\<close>
    and \<open>tr_args_m p dm env n s ts = (s', es) \<Longrightarrow> pre s s' \<and> length es = length ts\<close>
proof (induction p dm env n s t and p dm env n s ts arbitrary: s' e and s' es rule: tr_term_m_tr_args_m.induct)
  case (4 p dm env n s f args)
  obtain s1 es1 where r: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  have \<open>pre s s1\<close> using 4(1)[OF r] by simp
  then have \<open>pre s (fst (enc_terms_m s1 es1))\<close> using pre_enc_terms[of s \<open>(s1, [])\<close> es1] by (simp add: enc_terms_m_def)
  then show ?case using 4(2) r by (auto simp: Let_def split: if_splits intro: pre_add_term pre_add_atom)
next
  case (5 p dm env n s d args)
  obtain s1 es1 where r: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  show ?case using 5 r by (auto simp: Let_def pre_refl split: if_splits intro: pre_trans)
next
  case (6 p dm env n s op args)
  obtain s1 es1 where r: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  show ?case using 6(2) r 6(1)[OF r] pre_enc_app[of s s1 op es1] by (auto simp: Let_def)
next
  case (8 p dm env n s a rest)
  obtain s1 e1 where r1: \<open>tr_term_m p dm env n s a = (s1, e1)\<close> by (cases \<open>tr_term_m p dm env n s a\<close>)
  obtain s2 es2 where r2: \<open>tr_args_m p dm env n s1 rest = (s2, es2)\<close> by (cases \<open>tr_args_m p dm env n s1 rest\<close>)
  have h2: \<open>pre s1 s2 \<and> length es2 = length rest\<close> using 8(2)[OF r1[symmetric]] r2 by simp
  show ?case using 8(1)[OF r1] h2 8(3) r1 r2 by (auto simp: Let_def intro: pre_trans)
qed (auto simp: pre_refl)

subsection \<open>Values in a final state\<close>

text \<open>The value of term \<open>k\<close> and the truth of literal \<open>(a, pos)\<close> of the final state \<open>q\<close> under \<open>I\<close>.\<close>
definition tv :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> 'd\<close> where
  \<open>tv I q k \<equiv> term_val I (st_terms q) k\<close>

definition lv :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>lv I q a pos \<equiv> ((tv I q (unat (Atom_lhs (st_atoms q ! a))) = tv I q (unat (Atom_rhs (st_atoms q ! a)))) = pos)\<close>

lemma lv_neg: \<open>lv I q a (\<not> pos) = (\<not> lv I q a pos)\<close>
  by (auto simp: lv_def)

lemma lv_False: \<open>lv I q a False = (\<not> lv I q a True)\<close>
  by (auto simp: lv_def)

lemma lit_true_lv: \<open>lit_true I (st_prob q) l = lv I q (unat (Lit_atom l)) (Lit_pos l)\<close>
  by (simp add: lit_true_def atom_true_def st_prob_def lv_def tv_def)

lemma lit_true_m: \<open>a < 2 ^ 64 \<Longrightarrow> lit_true I (st_prob q) (lit_m a pos) = lv I q a pos\<close>
  by (simp add: lit_true_lv lit_m_def unat_wn)

lemma clause_true_mk: \<open>clause_true I P (make_Clause ls) = (\<exists>l \<in> set ls. lit_true I P l)\<close>
  by (simp add: clause_true_def)

definition cls_true :: \<open>st \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>cls_true q I s \<equiv> \<forall>c \<in> set (st_clauses s). clause_true I (st_prob q) c\<close>

lemma cls_true_pre: \<open>pre s s' \<Longrightarrow> cls_true q I s' \<Longrightarrow> cls_true q I s\<close>
  by (auto simp: cls_true_def pre_def)

lemma pre_nth_terms: \<open>pre s q \<Longrightarrow> k < length (st_terms s) \<Longrightarrow> st_terms q ! k = st_terms s ! k\<close>
  by (auto simp: pre_def nth_append)

lemma pre_nth_atoms: \<open>pre s q \<Longrightarrow> k < length (st_atoms s) \<Longrightarrow> st_atoms q ! k = st_atoms s ! k\<close>
  by (auto simp: pre_def nth_append)

lemma tv_new:
  assumes \<open>pre s' q\<close> \<open>k < length (st_terms s')\<close> \<open>st_terms s' ! k = make_Term (word_of_nat f) (map word_of_nat args)\<close>
    \<open>f < 2 ^ 64\<close> \<open>\<forall>x \<in> set args. x < k\<close> \<open>k < 2 ^ 64\<close>
  shows \<open>tv I q k = I f (map (tv I q) args)\<close>
proof -
  have q: \<open>st_terms q ! k = make_Term (word_of_nat f) (map word_of_nat args)\<close> using pre_nth_terms[OF assms(1,2)] assms(3) by simp
  have u: \<open>\<forall>x \<in> set args. unat (word_of_nat x :: 64 word) = x\<close> using assms(5,6) by (auto simp: unat_wn)
  have \<open>map (\<lambda>x. if unat x < k then term_val I (st_terms q) (unat x) else undefined) (map (word_of_nat :: nat \<Rightarrow> 64 word) args) =
        map (tv I q) args\<close>
    using u assms(5) by (auto simp: tv_def)
  then show ?thesis unfolding tv_def by (subst term_val.simps) (metis (no_types) q unat_wn assms(4) Term.sel)
qed

lemma lv_new:
  assumes \<open>pre s' q\<close> \<open>a < length (st_atoms s')\<close> \<open>st_atoms s' ! a = make_Atom (word_of_nat l) (word_of_nat r)\<close>
    \<open>l < 2 ^ 64\<close> \<open>r < 2 ^ 64\<close>
  shows \<open>lv I q a pos = ((tv I q l = tv I q r) = pos)\<close>
  using pre_nth_atoms[OF assms(1,2)] assms(3,4,5) by (simp add: lv_def unat_wn)

definition agree :: \<open>nat \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> bool\<close> where
  \<open>agree n I I' \<equiv> \<forall>f < n. I' f = I f\<close>

lemma tv_agree:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close>
  shows \<open>k < length (st_terms s) \<Longrightarrow> tv I' q k = tv I q k\<close>
proof (induction k rule: less_induct)
  case (less k)
  have tk: \<open>st_terms q ! k = st_terms s ! k\<close> using pre_nth_terms[OF assms(2) less.prems] .
  have f: \<open>I' (unat (Term_fun (st_terms s ! k))) = I (unat (Term_fun (st_terms s ! k)))\<close>
    using assms(1,3) less.prems by (simp add: st_wf_def agree_def)
  have a: \<open>\<forall>x \<in> set (Term_args (st_terms s ! k)). unat x < k\<close> using assms(1) less.prems by (simp add: st_wf_def)
  have \<open>map (\<lambda>x. if unat x < k then term_val I' (st_terms q) (unat x) else undefined) (Term_args (st_terms s ! k)) =
        map (\<lambda>x. if unat x < k then term_val I (st_terms q) (unat x) else undefined) (Term_args (st_terms s ! k))\<close>
    using less.IH a less.prems by (auto simp: tv_def)
  then show ?case unfolding tv_def by (subst (1 2) term_val.simps) (simp only: tk f)
qed

lemma lv_agree:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close> \<open>a < length (st_atoms s)\<close>
  shows \<open>lv I' q a pos = lv I q a pos\<close>
proof -
  have \<open>st_atoms q ! a \<in> set (st_atoms s)\<close> using pre_nth_atoms[OF assms(2,4)] assms(4) by simp
  then show ?thesis using assms(1) tv_agree[OF assms(1,2,3)] by (simp add: lv_def st_wf_def)
qed

lemma cls_agree:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close>
  shows \<open>cls_true q I' s = cls_true q I s\<close>
  using assms(1) lv_agree[OF assms] unfolding cls_true_def clause_true_def lit_true_lv st_wf_def
  by (metis (no_types, lifting))

subsection \<open>Extending an interpretation to the new symbols\<close>

definition base :: \<open>st \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> bool\<close> where
  \<open>base q I \<equiv> tv I q 0 \<noteq> tv I q 1\<close>

text \<open>Every interpretation over \<^typ>\<open>nat\<close> that keeps TRUE and FALSE apart and makes the clauses
  of \<open>s\<close> true can be changed at the symbols from \<open>st_next s\<close> on so that it also makes the clauses of
  \<open>s'\<close> true.\<close>
definition ext :: \<open>st \<Rightarrow> st \<Rightarrow> st \<Rightarrow> bool\<close> where
  \<open>ext q s s' \<equiv> \<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. base q I \<and> cls_true q I s \<longrightarrow>
     (\<exists>I'. agree (st_next s) I I' \<and> base q I' \<and> cls_true q I' s')\<close>

lemma ext_trans: \<open>ext q s s1 \<Longrightarrow> ext q s1 s2 \<Longrightarrow> st_next s \<le> st_next s1 \<Longrightarrow> ext q s s2\<close>
  unfolding ext_def agree_def by (metis less_le_trans)

lemma ext_same: \<open>st_clauses s' = st_clauses s \<Longrightarrow> ext q s s'\<close>
  unfolding ext_def agree_def cls_true_def by auto

lemma ext_refl: \<open>ext q s s\<close>
  by (rule ext_same) simp

lemma ext_fresh:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>st_clauses s' = st_clauses s @ NC\<close>
    \<open>\<And>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. base q I \<Longrightarrow> \<exists>v. \<forall>c \<in> set NC. clause_true (I(st_next s := \<lambda>_. v)) (st_prob q) c\<close>
  shows \<open>ext q s s'\<close>
  unfolding ext_def
proof (intro allI impI)
  fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume h: \<open>base q I \<and> cls_true q I s\<close>
  obtain v where v: \<open>\<forall>c \<in> set NC. clause_true (I(st_next s := \<lambda>_. v)) (st_prob q) c\<close> using assms(4) h by blast
  let ?I = \<open>I(st_next s := \<lambda>_. v)\<close>
  have ag: \<open>agree (st_next s) I ?I\<close> by (simp add: agree_def)
  have l2: \<open>0 < length (st_terms s)\<close> \<open>1 < length (st_terms s)\<close> using assms(1) by (auto simp: st_wf_def)
  have b: \<open>base q ?I\<close> using h tv_agree[OF assms(1,2) ag l2(1)] tv_agree[OF assms(1,2) ag l2(2)] by (simp add: base_def)
  have c: \<open>cls_true q ?I s'\<close> using h cls_agree[OF assms(1,2) ag] v assms(3) by (auto simp: cls_true_def)
  show \<open>\<exists>I'. agree (st_next s) I I' \<and> base q I' \<and> cls_true q I' s'\<close> using ag b c by blast
qed

lemma pre_len: \<open>pre s q \<Longrightarrow> length (st_terms s) \<le> length (st_terms q) \<and> length (st_atoms s) \<le> length (st_atoms q) \<and>
    length (st_clauses s) \<le> length (st_clauses q) \<and> st_next s \<le> st_next q\<close>
  by (auto simp: pre_def)

text \<open>The values under the interpretation changed at the next unused symbol \<open>st_next s\<close>, where the
  state \<open>s'\<close> after \<open>s\<close> has a new constant with this symbol as term \<open>length (st_terms s)\<close>.\<close>
lemma fresh_vals:
  assumes \<open>st_wf nf s\<close> \<open>pre s s'\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
    \<open>length (st_terms s) < length (st_terms s')\<close>
    \<open>st_terms s' ! length (st_terms s) = make_Term (word_of_nat (st_next s)) []\<close>
  shows \<open>tv (I(st_next s := \<lambda>_. v)) q (length (st_terms s)) = v\<close>
    and \<open>k < length (st_terms s) \<Longrightarrow> tv (I(st_next s := \<lambda>_. v)) q k = tv I q k\<close>
    and \<open>a < length (st_atoms s) \<Longrightarrow> lv (I(st_next s := \<lambda>_. v)) q a pos = lv I q a pos\<close>
proof -
  have sq: \<open>pre s q\<close> using pre_trans[OF assms(2,3)] .
  have ag: \<open>agree (st_next s) I (I(st_next s := \<lambda>_. v))\<close> by (simp add: agree_def)
  have b: \<open>st_next s < 2 ^ 64\<close> \<open>length (st_terms s) < 2 ^ 64\<close>
    using pre_len[OF sq] pre_len[OF assms(3)] assms(4,5) by (auto simp: bnd_def)
  show \<open>tv (I(st_next s := \<lambda>_. v)) q (length (st_terms s)) = v\<close>
    using tv_new[where I=\<open>I(st_next s := \<lambda>_. v)\<close> and f=\<open>st_next s\<close> and args=\<open>[]\<close>, OF assms(3,5)] assms(6) b by simp
  show \<open>k < length (st_terms s) \<Longrightarrow> tv (I(st_next s := \<lambda>_. v)) q k = tv I q k\<close>
    using tv_agree[OF assms(1) sq ag] by simp
  show \<open>a < length (st_atoms s) \<Longrightarrow> lv (I(st_next s := \<lambda>_. v)) q a pos = lv I q a pos\<close>
    using lv_agree[OF assms(1) sq ag] by simp
qed

subsection \<open>The primitive operations keep the state well-formed and extendable\<close>

lemma enc_term_wb:
  assumes \<open>st_wf nf s\<close> \<open>enc_wf s e\<close> \<open>enc_term_m s e = (s', k)\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> k < length (st_terms s') \<and> ext q s s'\<close>
proof (cases e)
  case (ETerm i)
  then show ?thesis using assms by (auto simp: enc_wf_def ext_refl)
next
  case (ELit a pos)
  let ?T = \<open>length (st_terms s)\<close> and ?A = \<open>length (st_atoms s)\<close> and ?g = \<open>st_next s\<close>
  let ?NC = \<open>[make_Clause [lit_m a (\<not> pos), lit_m ?A True], make_Clause [lit_m a pos, lit_m (Suc ?A) True]]\<close>
  have r: \<open>enc_term_m s e = (St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0, make_Atom (word_of_nat ?T) 1])
       (st_clauses s @ ?NC) (Suc ?g), ?T)\<close>
    using ELit by (simp add: enc_term_lit_eq del: enc_term_m.simps)
  have s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0, make_Atom (word_of_nat ?T) 1])
       (st_clauses s @ ?NC) (Suc ?g) \<and> k = ?T\<close>
    using assms(3)[unfolded r, symmetric] by (simp only: prod.inject)
  then have k: \<open>k = ?T\<close> and s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0, make_Atom (word_of_nat ?T) 1])
       (st_clauses s @ ?NC) (Suc ?g)\<close> by simp_all
  have ss: \<open>pre s s'\<close> using s' by (simp add: pre_St)
  have b: \<open>Suc ?g < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> \<open>Suc (Suc ?A) < 2 ^ 64\<close>
    using pre_len[OF assms(4)] assms(5) s' by (auto simp: bnd_def)
  have a: \<open>a < ?A\<close> using assms(2) ELit by (simp add: enc_wf_def)
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1) b a by (simp add: st_wf_def unat_wn lit_m_def less_Suc_eq del: of_nat_Suc)
  have e: \<open>ext q s s'\<close>
  proof (rule ext_fresh[OF assms(1) pre_trans[OF ss assms(4)]])
    show \<open>st_clauses s' = st_clauses s @ ?NC\<close> using s' by simp
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume bI: \<open>base q I\<close>
    let ?v = \<open>if lv I q a pos then tv I q 0 else tv I q 1\<close>
    have nt: \<open>?T < length (st_terms s')\<close> \<open>st_terms s' ! ?T = make_Term (word_of_nat ?g) []\<close> using s' by simp_all
    note fv = fresh_vals[OF assms(1) ss assms(4,5) nt, where v=\<open>?v\<close> and I=I]
    have ba: \<open>a < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close> using a b by simp_all
    have l2: \<open>0 < ?T\<close> \<open>1 < ?T\<close> using assms(1) by (auto simp: st_wf_def)
    have at: \<open>lv J q ?A p1 = ((tv J q ?T = tv J q 0) = p1)\<close> \<open>lv J q (Suc ?A) p1 = ((tv J q ?T = tv J q 1) = p1)\<close>
      for J :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and p1
      using lv_new[OF assms(4), of ?A ?T 0] lv_new[OF assms(4), of \<open>Suc ?A\<close> ?T 1] s' b by (simp_all add: nth_append)
    show \<open>\<exists>v. \<forall>c \<in> set ?NC. clause_true (I(?g := \<lambda>_. v)) (st_prob q) c\<close>
      using bI fv l2 a ba s' at
      by (intro exI[of _ ?v]) (auto simp: clause_true_mk lit_true_m lv_neg base_def nth_append)
  qed
  show ?thesis using w e k s' by simp
qed

lemma add_term_wb:
  assumes \<open>st_wf nf s\<close> \<open>f < st_next s\<close> \<open>\<forall>x \<in> set args. x < length (st_terms s)\<close> \<open>add_term_m s f args = (s', k)\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> k < length (st_terms s') \<and> ext q s s' \<and> pre s s'\<close>
proof -
  have s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat f) (map word_of_nat args)]) (st_atoms s @ []) (st_clauses s @ []) (st_next s)\<close>
    and k: \<open>k = length (st_terms s)\<close> using assms(4) by (auto simp: add_term_m_def)
  have b: \<open>Suc (length (st_terms s)) < 2 ^ 64\<close> \<open>st_next s < 2 ^ 64\<close>
    using pre_len[OF assms(5)] assms(6) s' by (auto simp: bnd_def)
  have u: \<open>\<forall>x \<in> set args. unat (word_of_nat x :: 64 word) = x\<close> using assms(3) b by (auto simp: unat_wn)
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1,2,3) b u by (auto simp: st_wf_def unat_wn)
  show ?thesis using w k s' by (auto intro: ext_same simp: pre_def)
qed

lemma add_atom_wb:
  assumes \<open>st_wf nf s\<close> \<open>l < length (st_terms s)\<close> \<open>r < length (st_terms s)\<close> \<open>add_atom_m s l r = (s', k)\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> k < length (st_atoms s') \<and> ext q s s' \<and> pre s s'\<close>
proof -
  have s': \<open>s' = St (st_terms s @ []) (st_atoms s @ [make_Atom (word_of_nat l) (word_of_nat r)]) (st_clauses s @ []) (st_next s)\<close>
    and k: \<open>k = length (st_atoms s)\<close> using assms(4) by (auto simp: add_atom_m_def)
  have b: \<open>length (st_terms s) < 2 ^ 64\<close>
    using pre_len[OF assms(5)] assms(6) s' by (auto simp: bnd_def)
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1,2,3) b by (simp add: unat_wn) (auto simp: st_wf_def)
  show ?thesis using w k s' by (auto intro: ext_same simp: pre_def)
qed

lemma gate_xor_wb:
  assumes \<open>st_wf nf s\<close> \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> \<open>gate_xor_m s (a, pa) (b, pb) = (s', l)\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> lit_wf s' l \<and> ext q s s' \<and> pre s s'\<close>
proof -
  let ?T = \<open>length (st_terms s)\<close> and ?A = \<open>length (st_atoms s)\<close> and ?g = \<open>st_next s\<close>
  let ?NC = \<open>[make_Clause [lit_m ?A False, lit_m a pa, lit_m b pb],
          make_Clause [lit_m ?A False, lit_m a (\<not> pa), lit_m b (\<not> pb)],
          make_Clause [lit_m ?A True, lit_m a (\<not> pa), lit_m b pb],
          make_Clause [lit_m ?A True, lit_m a pa, lit_m b (\<not> pb)]]\<close>
  have r: \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []]) (st_atoms s @ [make_Atom (word_of_nat ?T) 0])
       (st_clauses s @ ?NC) (Suc ?g) \<and> l = (?A, True)\<close>
    using assms(4)[unfolded gate_xor_eq, symmetric] by (simp only: prod.inject)
  then have l: \<open>l = (?A, True)\<close> and s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0]) (st_clauses s @ ?NC) (Suc ?g)\<close> by simp_all
  have ss: \<open>pre s s'\<close> using s' by (simp add: pre_St)
  have b: \<open>Suc ?g < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close>
    using pre_len[OF assms(5)] assms(6) s' by (auto simp: bnd_def)
  have ba: \<open>a < 2 ^ 64\<close> \<open>b < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> using assms(2,3) b by simp_all
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1,2,3) b by (simp add: st_wf_def unat_wn lit_m_def less_Suc_eq del: of_nat_Suc)
  have e: \<open>ext q s s'\<close>
  proof (rule ext_fresh[OF assms(1) pre_trans[OF ss assms(5)]])
    show \<open>st_clauses s' = st_clauses s @ ?NC\<close> using s' by simp
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume bI: \<open>base q I\<close>
    let ?v = \<open>if lv I q a pa \<noteq> lv I q b pb then tv I q 0 else tv I q 1\<close>
    have nt: \<open>?T < length (st_terms s')\<close> \<open>st_terms s' ! ?T = make_Term (word_of_nat ?g) []\<close> using s' by simp_all
    note fv = fresh_vals[OF assms(1) ss assms(5,6) nt, where v=\<open>?v\<close> and I=I]
    have l2: \<open>0 < ?T\<close> using assms(1) by (auto simp: st_wf_def)
    have at: \<open>lv J q ?A p1 = ((tv J q ?T = tv J q 0) = p1)\<close> for J :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and p1
      using lv_new[OF assms(5), of ?A ?T 0] s' b by (simp add: nth_append)
    show \<open>\<exists>v. \<forall>c \<in> set ?NC. clause_true (I(?g := \<lambda>_. v)) (st_prob q) c\<close>
      using bI fv l2 assms(2,3) ba at
      by (intro exI[of _ ?v]) (auto simp: clause_true_mk lit_true_m lv_neg lv_False base_def)
  qed
  show ?thesis using w e l s' ss by (simp add: lit_wf_def)
qed

lemma gate_ite_wb:
  assumes \<open>st_wf nf s\<close> \<open>kc < length (st_atoms s)\<close> \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close>
    \<open>gate_ite_m s (kc, pc) (a, pa) (b, pb) = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> enc_wf s' e \<and> ext q s s' \<and> pre s s'\<close>
proof -
  let ?T = \<open>length (st_terms s)\<close> and ?A = \<open>length (st_atoms s)\<close> and ?g = \<open>st_next s\<close>
  let ?NC = \<open>[make_Clause [lit_m kc (\<not> pc), lit_m a (\<not> pa), lit_m ?A True],
          make_Clause [lit_m kc (\<not> pc), lit_m a pa, lit_m ?A False],
          make_Clause [lit_m kc pc, lit_m b (\<not> pb), lit_m ?A True],
          make_Clause [lit_m kc pc, lit_m b pb, lit_m ?A False]]\<close>
  have r: \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []]) (st_atoms s @ [make_Atom (word_of_nat ?T) 0])
       (st_clauses s @ ?NC) (Suc ?g) \<and> e = ELit ?A True\<close>
    using assms(5)[unfolded gate_ite_eq, symmetric] by (simp only: prod.inject)
  then have l: \<open>e = ELit ?A True\<close> and s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0]) (st_clauses s @ ?NC) (Suc ?g)\<close> by simp_all
  have ss: \<open>pre s s'\<close> using s' by (simp add: pre_St)
  have b: \<open>Suc ?g < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close>
    using pre_len[OF assms(6)] assms(7) s' by (auto simp: bnd_def)
  have ba: \<open>kc < 2 ^ 64\<close> \<open>a < 2 ^ 64\<close> \<open>b < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> using assms(2,3,4) b by simp_all
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1,2,3,4) b by (simp add: st_wf_def unat_wn lit_m_def less_Suc_eq del: of_nat_Suc)
  have ex: \<open>ext q s s'\<close>
  proof (rule ext_fresh[OF assms(1) pre_trans[OF ss assms(6)]])
    show \<open>st_clauses s' = st_clauses s @ ?NC\<close> using s' by simp
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume bI: \<open>base q I\<close>
    let ?v = \<open>if (if lv I q kc pc then lv I q a pa else lv I q b pb) then tv I q 0 else tv I q 1\<close>
    have nt: \<open>?T < length (st_terms s')\<close> \<open>st_terms s' ! ?T = make_Term (word_of_nat ?g) []\<close> using s' by simp_all
    note fv = fresh_vals[OF assms(1) ss assms(6,7) nt, where v=\<open>?v\<close> and I=I]
    have l2: \<open>0 < ?T\<close> using assms(1) by (auto simp: st_wf_def)
    have at: \<open>lv J q ?A p1 = ((tv J q ?T = tv J q 0) = p1)\<close> for J :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and p1
      using lv_new[OF assms(6), of ?A ?T 0] s' b by (simp add: nth_append)
    show \<open>\<exists>v. \<forall>c \<in> set ?NC. clause_true (I(?g := \<lambda>_. v)) (st_prob q) c\<close>
      using bI fv l2 assms(2,3,4) ba at
      by (intro exI[of _ ?v]) (auto simp: clause_true_mk lit_true_m lv_neg lv_False base_def)
  qed
  show ?thesis using w ex l s' ss by (simp add: enc_wf_def)
qed

lemma gate_andor_wb:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>l \<in> set ls. lit_wf s l\<close> \<open>gate_andor_m s ls cj = (s', e)\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> enc_wf s' e \<and> ext q s s' \<and> pre s s'\<close>
proof -
  let ?T = \<open>length (st_terms s)\<close> and ?A = \<open>length (st_atoms s)\<close> and ?g = \<open>st_next s\<close>
  let ?NC = \<open>map (\<lambda>l. make_Clause (andor_cl_m ?A cj l)) ls @
          [make_Clause (lit_m ?A cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) ls)]\<close>
  have r: \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []]) (st_atoms s @ [make_Atom (word_of_nat ?T) 0])
       (st_clauses s @ ?NC) (Suc ?g) \<and> e = ELit ?A True\<close>
    using assms(3)[unfolded gate_andor_eq, symmetric] by (simp only: prod.inject append_assoc)
  then have l: \<open>e = ELit ?A True\<close> and s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0]) (st_clauses s @ ?NC) (Suc ?g)\<close> by simp_all
  have ss: \<open>pre s s'\<close> using s' by (simp add: pre_St)
  have b: \<open>Suc ?g < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close>
    using pre_len[OF assms(4)] assms(5) s' by (auto simp: bnd_def)
  have ls: \<open>\<forall>l \<in> set ls. fst l < ?A \<and> fst l < 2 ^ 64\<close> using assms(2) b by (auto simp: lit_wf_def)
  have ba: \<open>?A < 2 ^ 64\<close> using b by simp
  have cl: \<open>\<forall>c \<in> set ?NC. \<forall>x \<in> set (Clause_lits c). unat (Lit_atom x) < ?A + 1\<close>
    using ls ba by (auto simp: andor_cl_m_def lit_m_def unat_wn)
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1) b cl by (simp add: unat_wn) (auto simp: st_wf_def)
  have ex: \<open>ext q s s'\<close>
  proof (rule ext_fresh[OF assms(1) pre_trans[OF ss assms(4)]])
    show \<open>st_clauses s' = st_clauses s @ ?NC\<close> using s' by simp
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume bI: \<open>base q I\<close>
    let ?B = \<open>if cj then \<forall>l \<in> set ls. lv I q (fst l) (snd l) else \<exists>l \<in> set ls. lv I q (fst l) (snd l)\<close>
    let ?v = \<open>if ?B then tv I q 0 else tv I q 1\<close>
    have nt: \<open>?T < length (st_terms s')\<close> \<open>st_terms s' ! ?T = make_Term (word_of_nat ?g) []\<close> using s' by simp_all
    note fv = fresh_vals[OF assms(1) ss assms(4,5) nt, where v=\<open>?v\<close> and I=I]
    have l2: \<open>0 < ?T\<close> using assms(1) by (auto simp: st_wf_def)
    have at: \<open>lv J q ?A p1 = ((tv J q ?T = tv J q 0) = p1)\<close> for J :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and p1
      using lv_new[OF assms(4), of ?A ?T 0] s' b by (simp add: nth_append)
    have V: \<open>lv (I(?g := \<lambda>_. ?v)) q ?A p1 = (?B = p1)\<close> for p1
      using at fv(1) fv(2)[OF l2] bI by (auto simp: base_def)
    have L: \<open>l \<in> set ls \<Longrightarrow> lit_true (I(?g := \<lambda>_. ?v)) (st_prob q) (lit_m (fst l) p1) = lv I q (fst l) p1\<close> for l p1
      using ls fv(3) by (simp add: lit_true_m)
    have VL: \<open>lit_true (I(?g := \<lambda>_. ?v)) (st_prob q) (lit_m ?A p1) = (?B = p1)\<close> for p1
      using V ba by (simp add: lit_true_m)
    show \<open>\<exists>v. \<forall>c \<in> set ?NC. clause_true (I(?g := \<lambda>_. v)) (st_prob q) c\<close>
    proof (intro exI[of _ ?v] ballI)
      fix c assume c: \<open>c \<in> set ?NC\<close>
      show \<open>clause_true (I(?g := \<lambda>_. ?v)) (st_prob q) c\<close>
      proof (cases \<open>c \<in> set (map (\<lambda>l. make_Clause (andor_cl_m ?A cj l)) ls)\<close>)
        case True
        then obtain l where l: \<open>l \<in> set ls\<close> \<open>c = make_Clause (andor_cl_m ?A cj l)\<close> by auto
        show ?thesis using l VL L[OF l(1)] by (cases cj) (auto simp: clause_true_mk andor_cl_m_def lv_neg lv_False)
      next
        case False
        then have c: \<open>c = make_Clause (lit_m ?A cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) ls)\<close>
          using c by simp
        show ?thesis using VL L unfolding c by (cases cj) (auto simp: clause_true_mk lv_neg lv_False)
      qed
    qed
  qed
  show ?thesis using w ex l s' ss by (simp add: enc_wf_def)
qed

lemma ite_term_wb:
  assumes \<open>st_wf nf s\<close> \<open>enc_lit_m (es ! 0) = (kc, pc)\<close> \<open>kc < length (st_atoms s)\<close>
    \<open>es ! 1 = ETerm k1\<close> \<open>es ! 2 = ETerm k2\<close> \<open>k1 < length (st_terms s)\<close> \<open>k2 < length (st_terms s)\<close>
    \<open>ite_term_m s es = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> enc_wf s' e \<and> ext q s s' \<and> pre s s'\<close>
proof -
  let ?T = \<open>length (st_terms s)\<close> and ?A = \<open>length (st_atoms s)\<close> and ?g = \<open>st_next s\<close>
  let ?NC = \<open>[make_Clause [lit_m kc (\<not> pc), lit_m ?A True], make_Clause [lit_m kc pc, lit_m (Suc ?A) True]]\<close>
  have r: \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) (word_of_nat k1), make_Atom (word_of_nat ?T) (word_of_nat k2)])
       (st_clauses s @ ?NC) (Suc ?g) \<and> e = ETerm ?T\<close>
    using assms(8)[unfolded ite_term_eq[OF assms(4,5,2)], symmetric] by (simp only: prod.inject)
  then have l: \<open>e = ETerm ?T\<close> and s': \<open>s' = St (st_terms s @ [make_Term (word_of_nat ?g) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) (word_of_nat k1), make_Atom (word_of_nat ?T) (word_of_nat k2)])
       (st_clauses s @ ?NC) (Suc ?g)\<close> by simp_all
  have ss: \<open>pre s s'\<close> using s' by (simp add: pre_St)
  have b: \<open>Suc ?g < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> \<open>Suc (Suc ?A) < 2 ^ 64\<close>
    using pre_len[OF assms(9)] assms(10) s' by (auto simp: bnd_def)
  have ba: \<open>kc < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close> \<open>k1 < 2 ^ 64\<close> \<open>k2 < 2 ^ 64\<close>
    using assms(3,6,7) b by simp_all
  have w: \<open>st_wf nf s'\<close>
    using wf_extend[OF assms(1) s'] assms(1,3,6,7) b ba by (simp add: st_wf_def unat_wn lit_m_def less_Suc_eq del: of_nat_Suc)
  have ex: \<open>ext q s s'\<close>
  proof (rule ext_fresh[OF assms(1) pre_trans[OF ss assms(9)]])
    show \<open>st_clauses s' = st_clauses s @ ?NC\<close> using s' by simp
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> assume bI: \<open>base q I\<close>
    let ?v = \<open>if lv I q kc pc then tv I q k1 else tv I q k2\<close>
    have nt: \<open>?T < length (st_terms s')\<close> \<open>st_terms s' ! ?T = make_Term (word_of_nat ?g) []\<close> using s' by simp_all
    note fv = fresh_vals[OF assms(1) ss assms(9,10) nt, where v=\<open>?v\<close> and I=I]
    have at: \<open>lv J q ?A p1 = ((tv J q ?T = tv J q k1) = p1)\<close> \<open>lv J q (Suc ?A) p1 = ((tv J q ?T = tv J q k2) = p1)\<close>
      for J :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and p1
      using lv_new[OF assms(9), of ?A ?T k1] lv_new[OF assms(9), of \<open>Suc ?A\<close> ?T k2] s' b ba by (simp_all add: nth_append)
    show \<open>\<exists>v. \<forall>c \<in> set ?NC. clause_true (I(?g := \<lambda>_. v)) (st_prob q) c\<close>
      using fv assms(3,6,7) ba at
      by (intro exI[of _ ?v]) (auto simp: clause_true_mk lit_true_m lv_neg lv_False)
  qed
  show ?thesis using w ex l s' ss by (simp add: enc_wf_def)
qed

lemma eq_pairs_set: \<open>set (eq_pairs_m n dst) = {(i, j). i < j \<and> j < n \<and> (dst \<or> j = Suc i)}\<close>
  by (auto simp: eq_pairs_m_def image_iff)

lemma eq_fold_wb:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>i < length es. enc_wf s (es ! i)\<close>
    \<open>\<forall>i < length es. \<forall>j < length es. is_lit_m (es ! i) = is_lit_m (es ! j)\<close>
    \<open>\<forall>ij \<in> set prs. fst ij < length es \<and> snd ij < length es\<close> \<open>\<forall>l \<in> set ls. lit_wf s l\<close>
    \<open>foldl (eq_step_m es dst) (s, ls) prs = (s', ls')\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> (\<forall>l \<in> set ls'. lit_wf s' l) \<and> ext q s s' \<and> pre s s'\<close>
  using assms
proof (induction prs arbitrary: s ls)
  case Nil
  then show ?case by (simp add: ext_refl pre_refl)
next
  case (Cons ij prs)
  obtain i j where ij: \<open>ij = (i, j)\<close> by (cases ij)
  obtain s1 ls1 where st: \<open>eq_step_m es dst (s, ls) (i, j) = (s1, ls1)\<close> by (cases \<open>eq_step_m es dst (s, ls) (i, j)\<close>)
  have f: \<open>foldl (eq_step_m es dst) (s1, ls1) prs = (s', ls')\<close> using Cons.prems(6) ij st by simp
  have p1: \<open>pre s1 s'\<close> using pre_eq_fold[of s1 \<open>(s1, ls1)\<close> es dst prs] f pre_refl by simp
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p1 Cons.prems(7)] .
  have ijl: \<open>i < length es\<close> \<open>j < length es\<close> using Cons.prems(4) ij by auto
  have A: \<open>st_wf nf s1 \<and> (\<forall>l \<in> set ls1. lit_wf s1 l) \<and> ext q s s1 \<and> pre s s1\<close>
  proof (cases \<open>is_lit_m (es ! i)\<close>)
    case True
    then have \<open>is_lit_m (es ! j)\<close> using Cons.prems(3) ijl by blast
    then obtain a pa b pb where ei: \<open>es ! i = ELit a pa\<close> \<open>es ! j = ELit b pb\<close>
      using True by (cases \<open>es ! i\<close>; cases \<open>es ! j\<close>) auto
    obtain sx x where gx: \<open>gate_xor_m s (a, pa) (b, pb) = (sx, x)\<close> by (cases \<open>gate_xor_m s (a, pa) (b, pb)\<close>)
    have e: \<open>eq_step_m es dst (s, ls) (i, j) = (sx, ls @ [(fst x, if dst then snd x else \<not> snd x)])\<close>
      using gx ei by (simp add: eq_step_m_def Let_def)
    have st': \<open>s1 = sx\<close> \<open>ls1 = ls @ [(fst x, if dst then snd x else \<not> snd x)]\<close> using st e by simp_all
    have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> using Cons.prems(2) ijl ei by (auto simp: enc_wf_def)
    have G: \<open>st_wf nf sx \<and> lit_wf sx x \<and> ext q s sx \<and> pre s sx\<close>
      using gate_xor_wb[OF Cons.prems(1) ab gx _ Cons.prems(8)] q1 st' by simp
    then show ?thesis using Cons.prems(5) st' lit_wf_pre[of s sx] by (auto simp: lit_wf_def)
  next
    case False
    then have \<open>\<not> is_lit_m (es ! j)\<close> using Cons.prems(3) ijl by blast
    then obtain ki kj where ei: \<open>es ! i = ETerm ki\<close> \<open>es ! j = ETerm kj\<close>
      using False by (cases \<open>es ! i\<close>; cases \<open>es ! j\<close>) auto
    obtain sx x where gx: \<open>add_atom_m s ki kj = (sx, x)\<close> by (cases \<open>add_atom_m s ki kj\<close>)
    have e: \<open>eq_step_m es dst (s, ls) (i, j) = (sx, ls @ [(x, \<not> dst)])\<close>
      using gx ei by (simp add: eq_step_m_def Let_def)
    have st': \<open>s1 = sx\<close> \<open>ls1 = ls @ [(x, \<not> dst)]\<close> using st e by simp_all
    have ab: \<open>ki < length (st_terms s)\<close> \<open>kj < length (st_terms s)\<close> using Cons.prems(2) ijl ei by (auto simp: enc_wf_def)
    have G: \<open>st_wf nf sx \<and> x < length (st_atoms sx) \<and> ext q s sx \<and> pre s sx\<close>
      using add_atom_wb[OF Cons.prems(1) ab gx _ Cons.prems(8)] q1 st' by simp
    then show ?thesis using Cons.prems(5) st' lit_wf_pre[of s sx] by (auto simp: lit_wf_def)
  qed
  have e1: \<open>\<forall>i < length es. enc_wf s1 (es ! i)\<close> using Cons.prems(2) A enc_wf_pre[of s s1] by blast
  have pr: \<open>\<forall>ij \<in> set prs. fst ij < length es \<and> snd ij < length es\<close> using Cons.prems(4) by simp
  have B: \<open>st_wf nf s' \<and> (\<forall>l \<in> set ls'. lit_wf s' l) \<and> ext q s1 s' \<and> pre s1 s'\<close>
    using Cons.IH[OF conjunct1[OF A] e1 Cons.prems(3) pr conjunct1[OF conjunct2[OF A]] f Cons.prems(7,8)] .
  show ?case using A B by (auto intro: ext_trans pre_trans simp: pre_def)
qed

lemma xor_fold_wb:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>e \<in> set es. enc_wf s e\<close> \<open>lit_wf s acc\<close>
    \<open>foldl xor_step_m (s, acc) es = (s', l)\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> lit_wf s' l \<and> ext q s s' \<and> pre s s'\<close>
  using assms
proof (induction es arbitrary: s acc)
  case Nil
  then show ?case by (simp add: ext_refl pre_refl)
next
  case (Cons e es)
  obtain a pa where acc: \<open>acc = (a, pa)\<close> by (cases acc)
  obtain b pb where el: \<open>enc_lit_m e = (b, pb)\<close> by (cases \<open>enc_lit_m e\<close>)
  obtain s1 x where gx: \<open>gate_xor_m s (a, pa) (b, pb) = (s1, x)\<close> by (cases \<open>gate_xor_m s (a, pa) (b, pb)\<close>)
  have st: \<open>xor_step_m (s, acc) e = (s1, x)\<close> using acc el gx by (simp add: xor_step_m_def)
  have f: \<open>foldl xor_step_m (s1, x) es = (s', l)\<close> using Cons.prems(4) st by simp
  have p1: \<open>pre s1 s'\<close> using pre_xor_fold[of s1 \<open>(s1, x)\<close> es] f pre_refl by simp
  have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close>
    using Cons.prems(3) acc enc_lit_wf[OF Cons.prems(1), of e] Cons.prems(2) el by (auto simp: lit_wf_def)
  have A: \<open>st_wf nf s1 \<and> lit_wf s1 x \<and> ext q s s1 \<and> pre s s1\<close>
    using gate_xor_wb[OF Cons.prems(1) ab gx pre_trans[OF p1 Cons.prems(5)] Cons.prems(6)] .
  have e1: \<open>\<forall>e \<in> set es. enc_wf s1 e\<close> using Cons.prems(2) A enc_wf_pre[of s s1] by simp
  have B: \<open>st_wf nf s' \<and> lit_wf s' l \<and> ext q s1 s' \<and> pre s1 s'\<close>
    using Cons.IH[OF conjunct1[OF A] e1 conjunct1[OF conjunct2[OF A]] f Cons.prems(5,6)] .
  show ?case using A B by (auto intro: ext_trans pre_trans simp: pre_def)
qed

lemma enc_terms_wb:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>e \<in> set es. enc_wf s e\<close> \<open>\<forall>t \<in> set ts. t < length (st_terms s)\<close>
    \<open>foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s, ts) es = (s', ts')\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> (\<forall>t \<in> set ts'. t < length (st_terms s')) \<and> ext q s s' \<and> pre s s'\<close>
  using assms
proof (induction es arbitrary: s ts)
  case Nil
  then show ?case by (simp add: ext_refl pre_refl)
next
  case (Cons e es)
  obtain s1 k where r: \<open>enc_term_m s e = (s1, k)\<close> by (cases \<open>enc_term_m s e\<close>)
  have f: \<open>foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s1, ts @ [k]) es = (s', ts')\<close>
    using Cons.prems(4) r by simp
  have p1: \<open>pre s1 s'\<close> using pre_enc_terms[of s1 \<open>(s1, ts @ [k])\<close> es] f pre_refl by simp
  have p0: \<open>pre s s1\<close> using pre_enc_term[OF pre_refl, of s e] r by simp
  have A: \<open>st_wf nf s1 \<and> k < length (st_terms s1) \<and> ext q s s1\<close>
    using enc_term_wb[OF Cons.prems(1) _ r pre_trans[OF p1 Cons.prems(5)] Cons.prems(6)] Cons.prems(2) by simp
  have e1: \<open>\<forall>e \<in> set es. enc_wf s1 e\<close> using Cons.prems(2) enc_wf_pre[OF p0] by simp
  have t1: \<open>\<forall>t \<in> set (ts @ [k]). t < length (st_terms s1)\<close>
    using Cons.prems(3) A pre_len[OF p0] by auto
  have B: \<open>st_wf nf s' \<and> (\<forall>t \<in> set ts'. t < length (st_terms s')) \<and> ext q s1 s' \<and> pre s1 s'\<close>
    using Cons.IH[OF conjunct1[OF A] e1 t1 f Cons.prems(5,6)] .
  show ?case using A B p0 by (auto intro: ext_trans pre_trans simp: pre_def)
qed

text \<open>A Boolean term is translated into a literal, a term of another sort into a term.\<close>
definition shape :: \<open>SmtSort \<Rightarrow> enc_m \<Rightarrow> bool\<close> where
  \<open>shape so e \<equiv> (is_lit_m e = (so = SmtSort_Bool))\<close>

lemma op_sort_bool:
  \<open>op \<in> {SmtOp_And, SmtOp_Or, SmtOp_Xor, SmtOp_Implies} \<Longrightarrow> smt_op_sort op ss = Some so \<Longrightarrow>
     so = SmtSort_Bool \<and> 2 \<le> length ss \<and> set ss \<subseteq> {SmtSort_Bool}\<close>
  by (auto split: if_splits)

lemma op_sort_eq:
  \<open>op \<in> {SmtOp_Eq, SmtOp_Distinct} \<Longrightarrow> smt_op_sort op ss = Some so \<Longrightarrow>
     so = SmtSort_Bool \<and> 2 \<le> length ss \<and> set ss \<subseteq> {hd ss}\<close>
  by (auto split: if_splits)

lemma op_sort_ite:
  \<open>smt_op_sort SmtOp_Ite ss = Some so \<Longrightarrow> ss = [SmtSort_Bool, so, so]\<close>
  by (auto split: list.splits if_splits)

lemma op_sort_not:
  \<open>smt_op_sort SmtOp_Not ss = Some so \<Longrightarrow> ss = [SmtSort_Bool] \<and> so = SmtSort_Bool\<close>
  by (auto split: if_splits)

lemma enc_app_wb:
  assumes \<open>st_wf nf s\<close> \<open>smt_core_op op\<close> \<open>smt_op_sort op ss = Some so\<close> \<open>length es = length ss\<close>
    \<open>\<forall>i < length es. enc_wf s (es ! i) \<and> shape (ss ! i) (es ! i)\<close>
    \<open>enc_app_m s op es = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close>
  shows \<open>st_wf nf s' \<and> enc_wf s' e \<and> shape so e \<and> ext q s s' \<and> pre s s'\<close>
proof -
  have ew: \<open>\<forall>x \<in> set es. enc_wf s x\<close> using assms(5) by (auto simp: in_set_conv_nth)
  have lw: \<open>\<forall>l \<in> set (map enc_lit_m es). lit_wf s l\<close> using ew enc_lit_wf[OF assms(1)] by auto
  consider (Not) \<open>op = SmtOp_Not\<close> | (AO) \<open>op = SmtOp_And \<or> op = SmtOp_Or\<close> | (Xor) \<open>op = SmtOp_Xor\<close>
    | (Imp) \<open>op = SmtOp_Implies\<close> | (Eq) \<open>op = SmtOp_Eq \<or> op = SmtOp_Distinct\<close> | (Ite) \<open>op = SmtOp_Ite\<close>
    using assms(2) by (cases op) auto
  then show ?thesis
  proof cases
    case Not
    have o: \<open>smt_op_sort SmtOp_Not ss = Some so\<close> using assms(3) Not by (simp only:)
    have ss: \<open>ss = [SmtSort_Bool]\<close> \<open>so = SmtSort_Bool\<close> using op_sort_not[OF o] by simp_all
    have s0: \<open>shape SmtSort_Bool (es ! 0)\<close> \<open>enc_wf s (es ! 0)\<close> using assms(4,5) ss by auto
    then obtain a pos where e0: \<open>es ! 0 = ELit a pos\<close> by (cases \<open>es ! 0\<close>) (simp_all add: shape_def)
    have \<open>s' = s\<close> \<open>e = ELit a (\<not> pos)\<close> using assms(6) Not e0 by auto
    then show ?thesis using assms(1) s0 e0 ss by (simp add: enc_wf_def shape_def ext_refl pre_refl)
  next
    case AO
    have so: \<open>so = SmtSort_Bool\<close> using op_sort_bool[of op ss so] AO assms(3) by auto
    have g: \<open>gate_andor_m s (map enc_lit_m es) (op = SmtOp_And) = (s', e)\<close> using assms(6) AO by auto
    show ?thesis using gate_andor_wb[OF assms(1) lw g assms(7,8)] g so
      by (auto simp: gate_andor_eq shape_def)
  next
    case Imp
    have so: \<open>so = SmtSort_Bool\<close> using op_sort_bool[of op ss so] Imp assms(3) by auto
    have g: \<open>gate_andor_m s (implies_lits_m es) False = (s', e)\<close> using assms(6) Imp by auto
    have lw': \<open>\<forall>l \<in> set (implies_lits_m es). lit_wf s l\<close>
      using lw by (auto simp: implies_lits_m_def lit_wf_def)
    show ?thesis using gate_andor_wb[OF assms(1) lw' g assms(7,8)] g so
      by (auto simp: gate_andor_eq shape_def)
  next
    case Xor
    have so: \<open>so = SmtSort_Bool\<close> and l2: \<open>2 \<le> length es\<close> using op_sort_bool[of op ss so] Xor assms(3,4) by auto
    obtain s1 l where r: \<open>foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es) = (s1, l)\<close>
      by (cases \<open>foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es)\<close>)
    have se: \<open>s' = s1\<close> \<open>e = ELit (fst l) (snd l)\<close> using assms(6) Xor r by auto
    have \<open>es ! 0 \<in> set es\<close> using l2 by (intro nth_mem) linarith
    then have a0: \<open>lit_wf s (enc_lit_m (es ! 0))\<close> using lw by simp
    have et: \<open>\<forall>x \<in> set (tl es). enc_wf s x\<close> using ew by (cases es) auto
    show ?thesis using xor_fold_wb[OF assms(1) et a0 r] assms(7,8) se so
      by (auto simp: enc_wf_def lit_wf_def shape_def)
  next
    case Eq
    have so: \<open>so = SmtSort_Bool\<close> and hs: \<open>set ss \<subseteq> {hd ss}\<close> using op_sort_eq[of op ss so] Eq assms(3) by auto
    let ?d = \<open>op = SmtOp_Distinct\<close>
    obtain s1 ls where r: \<open>foldl (eq_step_m es ?d) (s, []) (eq_pairs_m (length es) ?d) = (s1, ls)\<close>
      by (cases \<open>foldl (eq_step_m es ?d) (s, []) (eq_pairs_m (length es) ?d)\<close>)
    have g: \<open>gate_andor_m s1 ls True = (s', e)\<close> using assms(6) Eq r by (auto simp: enc_eq_m_def)
    have p1: \<open>pre s1 s'\<close> using pre_gate_andor[OF pre_refl, of s1 ls True] g by simp
    have sh: \<open>\<forall>i < length es. ss ! i = hd ss\<close> using hs assms(4) by (auto simp: subset_iff)
    have li: \<open>\<forall>i < length es. \<forall>j < length es. is_lit_m (es ! i) = is_lit_m (es ! j)\<close>
      using assms(5) sh by (auto simp: shape_def)
    have prs: \<open>\<forall>ij \<in> set (eq_pairs_m (length es) ?d). fst ij < length es \<and> snd ij < length es\<close>
      by (auto simp: eq_pairs_set)
    have A: \<open>st_wf nf s1 \<and> (\<forall>l \<in> set ls. lit_wf s1 l) \<and> ext q s s1 \<and> pre s s1\<close>
      using eq_fold_wb[OF assms(1) _ li prs _ r pre_trans[OF p1 assms(7)] assms(8)] assms(5) by simp
    have B: \<open>st_wf nf s' \<and> enc_wf s' e \<and> ext q s1 s' \<and> pre s1 s'\<close>
      using gate_andor_wb[OF conjunct1[OF A] _ g assms(7,8)] A by simp
    have \<open>is_lit_m e\<close> using g by (auto simp: gate_andor_eq)
    then show ?thesis using A B so by (auto intro: ext_trans pre_trans simp: shape_def pre_def)
  next
    case Ite
    have ss: \<open>ss = [SmtSort_Bool, so, so]\<close> using op_sort_ite assms(3) Ite by simp
    have l3: \<open>length es = 3\<close> using assms(4) ss by simp
    have sh: \<open>shape SmtSort_Bool (es ! 0)\<close> \<open>shape so (es ! 1)\<close> \<open>shape so (es ! 2)\<close> \<open>enc_wf s (es ! 0)\<close>
      \<open>enc_wf s (es ! 1)\<close> \<open>enc_wf s (es ! 2)\<close> using assms(5) l3 ss by (auto simp: numeral_eq_Suc)
    obtain kc pc where c: \<open>es ! 0 = ELit kc pc\<close> using sh(1) by (cases \<open>es ! 0\<close>) (auto simp: shape_def)
    have kc: \<open>kc < length (st_atoms s)\<close> using sh(4) c by (simp add: enc_wf_def)
    show ?thesis
    proof (cases \<open>is_lit_m (es ! 1)\<close>)
      case True
      then have sb: \<open>so = SmtSort_Bool\<close> using sh(2) by (simp add: shape_def)
      obtain a pa where a: \<open>es ! 1 = ELit a pa\<close> using True by (cases \<open>es ! 1\<close>) auto
      obtain b pb where b: \<open>es ! 2 = ELit b pb\<close> using sh(3) sb by (cases \<open>es ! 2\<close>) (auto simp: shape_def)
      have g: \<open>gate_ite_m s (kc, pc) (a, pa) (b, pb) = (s', e)\<close> using assms(6) Ite True a b c by simp
      have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> using sh(5,6) a b by (simp_all add: enc_wf_def)
      have \<open>is_lit_m e\<close> using g by (auto simp: gate_ite_eq)
      then show ?thesis using gate_ite_wb[OF assms(1) kc ab g assms(7,8)] sb by (simp add: shape_def)
    next
      case False
      then have sb: \<open>so \<noteq> SmtSort_Bool\<close> using sh(2) by (simp add: shape_def)
      obtain k1 where a: \<open>es ! 1 = ETerm k1\<close> using False by (cases \<open>es ! 1\<close>) auto
      obtain k2 where b: \<open>es ! 2 = ETerm k2\<close> using sh(3) sb by (cases \<open>es ! 2\<close>) (auto simp: shape_def)
      have g: \<open>ite_term_m s es = (s', e)\<close> using assms(6) Ite False by simp
      have ab: \<open>k1 < length (st_terms s)\<close> \<open>k2 < length (st_terms s)\<close> using sh(5,6) a b by (simp_all add: enc_wf_def)
      have c': \<open>enc_lit_m (es ! 0) = (kc, pc)\<close> using c by simp
      have \<open>e = ETerm (length (st_terms s))\<close> using g ite_term_eq[OF a b c'] by simp
      then show ?thesis using ite_term_wb[OF assms(1) c' kc a b ab g assms(7,8)] sb by (simp add: shape_def)
    qed
  qed
qed

subsection \<open>The translation of terms keeps the state well-formed and extendable\<close>

definition env_ok :: \<open>st \<Rightarrow> SmtSort list \<Rightarrow> enc_m list \<Rightarrow> bool\<close> where
  \<open>env_ok s ps env \<equiv> length env = length ps \<and> (\<forall>i < length ps. enc_wf s (env ! i) \<and> shape (ps ! i) (env ! i))\<close>

definition dm_ok :: \<open>SmtProblem \<Rightarrow> st \<Rightarrow> nat \<Rightarrow> enc_m list \<Rightarrow> bool\<close> where
  \<open>dm_ok p s n dm \<equiv> n \<le> length (SmtProblem_defs p) \<and> n \<le> length dm \<and>
     (\<forall>d < n. enc_wf s (dm ! d) \<and>
        (SmtDef_params (SmtProblem_defs p ! d) = [] \<longrightarrow> shape (SmtDef_ret (SmtProblem_defs p ! d)) (dm ! d)))\<close>

lemma env_ok_pre: \<open>pre s s' \<Longrightarrow> env_ok s ps env \<Longrightarrow> env_ok s' ps env\<close>
  by (auto simp: env_ok_def intro: enc_wf_pre)

lemma dm_ok_pre: \<open>pre s s' \<Longrightarrow> dm_ok p s n dm \<Longrightarrow> m \<le> n \<Longrightarrow> dm_ok p s' m dm\<close>
  by (auto simp: dm_ok_def intro: enc_wf_pre)

lemma tr_wb:
  shows \<open>tr_term_m p dm env n s t = (s', e) \<Longrightarrow> smt_wf p \<Longrightarrow> smt_fragment p \<Longrightarrow> smt_term_no_bv t \<Longrightarrow>
     smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t = Some so \<Longrightarrow>
     env_ok s ps env \<Longrightarrow> dm_ok p s n dm \<Longrightarrow> st_wf (length (SmtProblem_funs p)) s \<Longrightarrow> pre s' q \<Longrightarrow> bnd q \<Longrightarrow>
     st_wf (length (SmtProblem_funs p)) s' \<and> enc_wf s' e \<and> shape so e \<and> ext q s s'\<close>
    and \<open>tr_args_m p dm env n s ts = (s', es) \<Longrightarrow> smt_wf p \<Longrightarrow> smt_fragment p \<Longrightarrow> (\<forall>t \<in> set ts. smt_term_no_bv t) \<Longrightarrow>
     map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts = map Some ss \<Longrightarrow>
     env_ok s ps env \<Longrightarrow> dm_ok p s n dm \<Longrightarrow> st_wf (length (SmtProblem_funs p)) s \<Longrightarrow> pre s' q \<Longrightarrow> bnd q \<Longrightarrow>
     st_wf (length (SmtProblem_funs p)) s' \<and> (\<forall>i < length ts. enc_wf s' (es ! i) \<and> shape (ss ! i) (es ! i)) \<and> ext q s s'\<close>
proof (induction p dm env n s t and p dm env n s ts arbitrary: s' e ps so and s' es ps ss rule: tr_term_m_tr_args_m.induct)
  case (1 p dm env n s b s' e ps so)
  then show ?case by (auto simp: enc_wf_def shape_def st_wf_def ext_refl)
next
  case (2 p dm env n s bs s' e ps so)
  then show ?case by simp
next
  case (3 p dm env n s k s' e ps so)
  then show ?case by (auto simp: env_ok_def ext_refl split: if_splits)
next
  case (4 p dm env n s f args s' e ps so)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  have ts: \<open>unat f < length ?fs\<close> \<open>map (smt_tsort ?fs (take n (SmtProblem_defs p)) ps) args = map Some (SmtFun_args (?fs ! unat f))\<close>
    \<open>so = SmtFun_ret (?fs ! unat f)\<close> using 4(6) by (auto split: if_splits)
  obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  obtain s2 ts2 where r2: \<open>enc_terms_m s1 es1 = (s2, ts2)\<close> by (cases \<open>enc_terms_m s1 es1\<close>)
  obtain s3 k where r3: \<open>add_term_m s2 (unat f) ts2 = (s3, k)\<close> by (cases \<open>add_term_m s2 (unat f) ts2\<close>)
  have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
  have p2: \<open>pre s1 s2\<close> using pre_enc_terms[of s1 \<open>(s1, [])\<close> es1] r2 pre_refl by (simp add: enc_terms_m_def)
  have p3: \<open>pre s2 s3\<close> using pre_add_term[OF pre_refl, of s2 \<open>unat f\<close> ts2] r3 by simp
  have res: \<open>if SmtFun_ret (?fs ! unat f) = SmtSort_Bool
      then s' = fst (add_atom_m s3 k 0) \<and> e = ELit (snd (add_atom_m s3 k 0)) True else s' = s3 \<and> e = ETerm k\<close>
    using 4(2) r1 r2 r3 by (auto simp: Let_def split: if_splits)
  have p4: \<open>pre s3 s'\<close> using res pre_add_atom[OF pre_refl, of s3 k 0] pre_refl by (auto split: if_splits)
  have q3: \<open>pre s3 q\<close> using pre_trans[OF p4 4(10)] .
  have q2: \<open>pre s2 q\<close> using pre_trans[OF p3 q3] .
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 q2] .
  have A: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (SmtFun_args (?fs ! unat f) ! i) (es1 ! i)) \<and> ext q s s1\<close>
    using 4(1)[OF r1 4(3,4) _ ts(2) 4(7,8,9) q1 4(11)] 4(5) by simp
  have ew: \<open>\<forall>x \<in> set es1. enc_wf s1 x\<close> using A p1(2) by (auto simp: in_set_conv_nth)
  have B: \<open>st_wf ?nf s2 \<and> (\<forall>t \<in> set ts2. t < length (st_terms s2)) \<and> ext q s1 s2 \<and> pre s1 s2\<close>
    using enc_terms_wb[OF conjunct1[OF A] ew _ _ q2 4(11), of \<open>[]\<close> ts2] r2 by (simp add: enc_terms_m_def)
  have fn: \<open>unat f < st_next s2\<close> using B ts(1) by (auto simp: st_wf_def)
  have C: \<open>st_wf ?nf s3 \<and> k < length (st_terms s3) \<and> ext q s2 s3 \<and> pre s2 s3\<close>
    using add_term_wb[OF conjunct1[OF B] fn _ r3 q3 4(11)] B by simp
  have E: \<open>ext q s s3\<close> using A B C p1 p2 by (meson ext_trans pre_len)
  show ?case
  proof (cases \<open>SmtFun_ret (?fs ! unat f) = SmtSort_Bool\<close>)
    case True
    obtain s4 a where r4: \<open>add_atom_m s3 k 0 = (s4, a)\<close> by (cases \<open>add_atom_m s3 k 0\<close>)
    have se: \<open>s' = s4\<close> \<open>e = ELit a True\<close> using res True r4 by simp_all
    have z: \<open>0 < length (st_terms s3)\<close> using C by (auto simp: st_wf_def)
    have D: \<open>st_wf ?nf s4 \<and> a < length (st_atoms s4) \<and> ext q s3 s4 \<and> pre s3 s4\<close>
      using add_atom_wb[OF conjunct1[OF C] _ z r4 _ 4(11)] C 4(10) se by simp
    have nx: \<open>st_next s \<le> st_next s3\<close> using pre_len[OF pre_trans[OF p1(1) pre_trans[OF p2 p3]]] by simp
    show ?thesis using D ext_trans[OF E _ nx] se ts(3) True by (simp add: enc_wf_def shape_def)
  next
    case False
    then show ?thesis using res C E ts(3) by (simp add: enc_wf_def shape_def)
  qed
next
  case (5 p dm env n s d args s' e ps so)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  have d: \<open>unat d < length (take n ?ds)\<close> \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some (SmtDef_params (?ds ! unat d))\<close>
    \<open>so = SmtDef_ret (?ds ! unat d)\<close> using 5(7) by (auto split: if_splits)
  have dn: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close> using d(1) by auto
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! unat d) = []\<close>)
    case True
    then show ?thesis using 5(3) 5(9) 5(10) dn d(3) by (auto simp: dm_ok_def ext_refl)
  next
    case False
    obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
    have res: \<open>tr_term_m p dm es1 (unat d) s1 (SmtDef_body (?ds ! unat d)) = (s', e)\<close>
      using 5(3) False dn(1) r1 by (simp add: Let_def)
    have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
    have p2: \<open>pre s1 s'\<close> using tr_pre(1)[OF res] .
    have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 5(11)] .
    have A: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (SmtDef_params (?ds ! unat d) ! i) (es1 ! i)) \<and> ext q s s1\<close>
      using 5(1)[OF False dn(1) r1 5(4,5) _ d(2) 5(8,9,10) q1 5(12)] 5(6) by simp
    have la: \<open>length args = length (SmtDef_params (?ds ! unat d))\<close> using d(2) by (metis length_map)
    have env1: \<open>env_ok s1 (SmtDef_params (?ds ! unat d)) es1\<close> using A p1(2) la by (simp add: env_ok_def)
    have dm1: \<open>dm_ok p s1 (unat d) dm\<close> using dm_ok_pre[OF p1(1) 5(9)] dn(1) by simp
    have tb: \<open>smt_tsort ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) = Some (SmtDef_ret (?ds ! unat d))\<close>
      using 5(4) dn(2) by (simp add: smt_wf_def Let_def)
    have nb: \<open>smt_term_no_bv (SmtDef_body (?ds ! unat d))\<close> using 5(5) dn(2) by (simp add: smt_fragment_def)
    have B: \<open>st_wf ?nf s' \<and> enc_wf s' e \<and> shape (SmtDef_ret (?ds ! unat d)) e \<and> ext q s1 s'\<close>
      using 5(2)[OF False dn(1) r1[symmetric], simplified, OF res 5(4,5) nb tb env1 dm1 conjunct1[OF A] 5(11,12)] .
    show ?thesis using A B d(3) p1 by (auto intro: ext_trans dest: pre_len)
  qed
next
  case (6 p dm env n s op args s' e ps so)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?ss = \<open>map (the \<circ> smt_tsort ?fs (take n ?ds) ps) args\<close>
  have o: \<open>None \<notin> set (map (smt_tsort ?fs (take n ?ds) ps) args)\<close> \<open>smt_op_sort op ?ss = Some so\<close>
    using 6(6) by (auto split: if_splits)
  have m: \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some ?ss\<close> using o(1) by (induction args) auto
  obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  have res: \<open>enc_app_m s1 op es1 = (s', e)\<close> using 6(2) r1 by (simp add: Let_def)
  have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
  have p2: \<open>pre s1 s'\<close> using pre_enc_app[OF pre_refl, of s1 op es1] res by simp
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 6(10)] .
  have A: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (?ss ! i) (es1 ! i)) \<and> ext q s s1\<close>
    using 6(1)[OF r1 6(3,4) _ m 6(7,8,9) q1 6(11)] 6(5) by simp
  have co: \<open>smt_core_op op\<close> using 6(5) by simp
  have B: \<open>st_wf ?nf s' \<and> enc_wf s' e \<and> shape so e \<and> ext q s1 s' \<and> pre s1 s'\<close>
    using enc_app_wb[OF conjunct1[OF A] co o(2) _ _ res 6(10,11)] A p1(2) by simp
  show ?case using A B p1 by (auto intro: ext_trans dest: pre_len)
next
  case (7 p dm env n s s' es ps ss)
  then show ?case by (auto simp: ext_refl)
next
  case (8 p dm env n s a rest s' es ps ss)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  obtain s1 e1 where r1: \<open>tr_term_m p dm env n s a = (s1, e1)\<close> by (cases \<open>tr_term_m p dm env n s a\<close>)
  obtain s2 es2 where r2: \<open>tr_args_m p dm env n s1 rest = (s2, es2)\<close> by (cases \<open>tr_args_m p dm env n s1 rest\<close>)
  have res: \<open>s' = s2\<close> \<open>es = e1 # es2\<close> using 8(3) r1 r2 by (simp_all add: Let_def)
  obtain s0 ss' where ss: \<open>ss = s0 # ss'\<close> \<open>smt_tsort ?fs (take n ?ds) ps a = Some s0\<close>
    \<open>map (smt_tsort ?fs (take n ?ds) ps) rest = map Some ss'\<close> using 8(7) by (cases ss) auto
  have p1: \<open>pre s s1\<close> using tr_pre(1)[OF r1] .
  have p2: \<open>pre s1 s2\<close> \<open>length es2 = length rest\<close> using tr_pre(2)[OF r2] by simp_all
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2(1)] 8(11) res by simp
  have A: \<open>st_wf ?nf s1 \<and> enc_wf s1 e1 \<and> shape s0 e1 \<and> ext q s s1\<close>
    using 8(1)[OF r1 8(4,5) _ ss(2) 8(8,9,10) q1 8(12)] 8(6) by simp
  have B: \<open>st_wf ?nf s2 \<and> (\<forall>i < length rest. enc_wf s2 (es2 ! i) \<and> shape (ss' ! i) (es2 ! i)) \<and> ext q s1 s2\<close>
    using 8(2)[OF r1[symmetric], simplified, OF r2 8(4,5) _ ss(3) env_ok_pre[OF p1 8(8)] dm_ok_pre[OF p1 8(9) order_refl] conjunct1[OF A]]
      8(6) 8(11,12) res by simp
  have e1: \<open>enc_wf s2 e1\<close> using A enc_wf_pre[OF p2(1)] by simp
  show ?case
  proof (intro conjI)
    show \<open>st_wf ?nf s'\<close> using B res by simp
    show \<open>\<forall>i < length (a # rest). enc_wf s' (es ! i) \<and> shape (ss ! i) (es ! i)\<close>
      using A B e1 res ss(1) by (auto simp: nth_Cons split: nat.splits)
    show \<open>ext q s s'\<close> using A B p1 res by (auto intro: ext_trans dest: pre_len)
  qed
qed

section \<open>Semantics of the translation\<close>

subsection \<open>The primitive operations\<close>

text \<open>Under an interpretation \<open>I\<close> that makes the clauses of the final state \<open>q\<close> true, the new
  literal or term of a primitive operation has the value its clauses define.\<close>

lemma cls_new: \<open>cls_true q I s' \<Longrightarrow> s' = St T A (C @ NC) n \<Longrightarrow> \<forall>c \<in> set NC. clause_true I (st_prob q) c\<close>
  by (simp add: cls_true_def)

lemma gate_xor_sem:
  assumes \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> \<open>gate_xor_m s (a, pa) (b, pb) = (s', l)\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>lv I q (fst l) (snd l) = (lv I q a pa \<noteq> lv I q b pb)\<close>
proof -
  let ?A = \<open>length (st_atoms s)\<close>
  have r: \<open>s' = fst (gate_xor_m s (a, pa) (b, pb))\<close> \<open>l = (?A, True)\<close> using assms(3) by (auto simp: gate_xor_eq)
  have b: \<open>Suc ?A < 2 ^ 64\<close> using pre_len[OF assms(4)] assms(5) r by (auto simp: bnd_def gate_xor_eq)
  have ba: \<open>a < 2 ^ 64\<close> \<open>b < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> using assms(1,2) b by simp_all
  note c = cls_new[OF assms(6) r(1)[unfolded gate_xor_eq fst_conv]]
  show ?thesis using c ba r(2) by (auto simp: clause_true_mk lit_true_m lv_neg lv_False)
qed

lemma gate_ite_sem:
  assumes \<open>kc < length (st_atoms s)\<close> \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close>
    \<open>gate_ite_m s (kc, pc) (a, pa) (b, pb) = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>e = ELit (length (st_atoms s)) True \<and>
    lv I q (length (st_atoms s)) True = (if lv I q kc pc then lv I q a pa else lv I q b pb)\<close>
proof -
  let ?A = \<open>length (st_atoms s)\<close>
  have r: \<open>s' = fst (gate_ite_m s (kc, pc) (a, pa) (b, pb))\<close> \<open>e = ELit ?A True\<close> using assms(4) by (auto simp: gate_ite_eq)
  have b: \<open>Suc ?A < 2 ^ 64\<close> using pre_len[OF assms(5)] assms(6) r by (auto simp: bnd_def gate_ite_eq)
  have ba: \<open>kc < 2 ^ 64\<close> \<open>a < 2 ^ 64\<close> \<open>b < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> using assms(1,2,3) b by simp_all
  note c = cls_new[OF assms(7) r(1)[unfolded gate_ite_eq fst_conv]]
  show ?thesis using c ba r(2) by (auto simp: clause_true_mk lit_true_m lv_neg lv_False)
qed

lemma gate_andor_sem:
  assumes \<open>\<forall>l \<in> set ls. lit_wf s l\<close> \<open>gate_andor_m s ls cj = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>e = ELit (length (st_atoms s)) True \<and> lv I q (length (st_atoms s)) True =
    (if cj then \<forall>l \<in> set ls. lv I q (fst l) (snd l) else \<exists>l \<in> set ls. lv I q (fst l) (snd l))\<close>
proof -
  let ?A = \<open>length (st_atoms s)\<close>
  have r: \<open>s' = fst (gate_andor_m s ls cj)\<close> \<open>e = ELit ?A True\<close> using assms(2) by (auto simp: gate_andor_eq)
  have b: \<open>Suc ?A < 2 ^ 64\<close> using pre_len[OF assms(3)] assms(4) r by (auto simp: bnd_def gate_andor_eq)
  have ba: \<open>?A < 2 ^ 64\<close> \<open>\<forall>l \<in> set ls. fst l < 2 ^ 64\<close> using assms(1) b by (auto simp: lit_wf_def)
  have L: \<open>l \<in> set ls \<Longrightarrow> lit_true I (st_prob q) (lit_m (fst l) p1) = lv I q (fst l) p1\<close> for l p1
    using ba by (simp add: lit_true_m)
  have V: \<open>lit_true I (st_prob q) (lit_m ?A p1) = lv I q ?A p1\<close> for p1 using ba by (simp add: lit_true_m)
  have c1: \<open>l \<in> set ls \<Longrightarrow> clause_true I (st_prob q) (make_Clause (andor_cl_m ?A cj l))\<close> for l
    using cls_new[OF assms(5) r(1)[unfolded gate_andor_eq fst_conv]] by simp
  have c2: \<open>clause_true I (st_prob q) (make_Clause (lit_m ?A cj # map (\<lambda>l. lit_m (fst l) (if cj then \<not> snd l else snd l)) ls))\<close>
    using cls_new[OF assms(5) r(1)[unfolded gate_andor_eq fst_conv]] by simp
  have \<open>lv I q ?A True = (if cj then \<forall>l \<in> set ls. lv I q (fst l) (snd l) else \<exists>l \<in> set ls. lv I q (fst l) (snd l))\<close>
  proof (cases cj)
    case True
    have i1: \<open>lv I q ?A True \<Longrightarrow> l \<in> set ls \<Longrightarrow> lv I q (fst l) (snd l)\<close> for l
      using c1[of l] L[of l] V True by (auto simp: clause_true_mk andor_cl_m_def lv_neg lv_False)
    have i2: \<open>\<forall>l \<in> set ls. lv I q (fst l) (snd l) \<Longrightarrow> lv I q ?A True\<close>
      using c2 L V True by (auto simp: clause_true_mk lv_neg lv_False)
    show ?thesis using i1 i2 True by auto
  next
    case False
    have i1: \<open>l \<in> set ls \<Longrightarrow> lv I q (fst l) (snd l) \<Longrightarrow> lv I q ?A True\<close> for l
      using c1[of l] L[of l] V False by (auto simp: clause_true_mk andor_cl_m_def lv_neg lv_False)
    have i2: \<open>lv I q ?A True \<Longrightarrow> \<exists>l \<in> set ls. lv I q (fst l) (snd l)\<close>
      using c2 L V False by (auto simp: clause_true_mk lv_neg lv_False)
    show ?thesis using i1 i2 False by auto
  qed
  then show ?thesis using r(2) by simp
qed

lemma enc_term_sem:
  assumes \<open>enc_wf s (ELit a pos)\<close> \<open>enc_term_m s (ELit a pos) = (s', k)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>tv I q k = (if lv I q a pos then tv I q 0 else tv I q 1)\<close>
proof -
  let ?A = \<open>length (st_atoms s)\<close> and ?T = \<open>length (st_terms s)\<close>
  have r: \<open>s' = fst (enc_term_m s (ELit a pos))\<close> \<open>k = ?T\<close>
    using assms(2) by (auto simp: enc_term_lit_eq simp del: enc_term_m.simps)
  have r': \<open>s' = St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) 0, make_Atom (word_of_nat ?T) 1])
       (st_clauses s @ [make_Clause [lit_m a (\<not> pos), lit_m ?A True], make_Clause [lit_m a pos, lit_m (Suc ?A) True]])
       (Suc (st_next s))\<close>
    using r(1) by (simp add: enc_term_lit_eq del: enc_term_m.simps)
  have b: \<open>Suc (Suc ?A) < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> using pre_len[OF assms(3)] assms(4) r' by (auto simp: bnd_def)
  have ba: \<open>a < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close> using assms(1) b by (simp_all add: enc_wf_def)
  have at: \<open>lv I q ?A p1 = ((tv I q ?T = tv I q 0) = p1)\<close> \<open>lv I q (Suc ?A) p1 = ((tv I q ?T = tv I q 1) = p1)\<close> for p1
    using lv_new[OF assms(3), of ?A ?T 0] lv_new[OF assms(3), of \<open>Suc ?A\<close> ?T 1] r' b by (simp_all add: nth_append)
  note c = cls_new[OF assms(5) r']
  show ?thesis using c ba at r(2) by (auto simp: clause_true_mk lit_true_m lv_neg lv_False)
qed

lemma ite_term_sem:
  assumes \<open>enc_lit_m (es ! 0) = (kc, pc)\<close> \<open>kc < length (st_atoms s)\<close>
    \<open>es ! 1 = ETerm k1\<close> \<open>es ! 2 = ETerm k2\<close> \<open>k1 < length (st_terms s)\<close> \<open>k2 < length (st_terms s)\<close>
    \<open>ite_term_m s es = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>e = ETerm (length (st_terms s)) \<and>
    tv I q (length (st_terms s)) = (if lv I q kc pc then tv I q k1 else tv I q k2)\<close>
proof -
  let ?A = \<open>length (st_atoms s)\<close> and ?T = \<open>length (st_terms s)\<close>
  have r: \<open>s' = St (st_terms s @ [make_Term (word_of_nat (st_next s)) []])
       (st_atoms s @ [make_Atom (word_of_nat ?T) (word_of_nat k1), make_Atom (word_of_nat ?T) (word_of_nat k2)])
       (st_clauses s @ [make_Clause [lit_m kc (\<not> pc), lit_m ?A True], make_Clause [lit_m kc pc, lit_m (Suc ?A) True]])
       (Suc (st_next s)) \<and> e = ETerm ?T\<close>
    using assms(7)[unfolded ite_term_eq[OF assms(3,4,1)], symmetric] by (simp only: prod.inject)
  have b: \<open>Suc (Suc ?A) < 2 ^ 64\<close> \<open>Suc ?T < 2 ^ 64\<close> using pre_len[OF assms(8)] assms(9) r by (auto simp: bnd_def)
  have ba: \<open>kc < 2 ^ 64\<close> \<open>?A < 2 ^ 64\<close> \<open>Suc ?A < 2 ^ 64\<close> \<open>k1 < 2 ^ 64\<close> \<open>k2 < 2 ^ 64\<close> using assms(2,5,6) b by simp_all
  have at: \<open>lv I q ?A p1 = ((tv I q ?T = tv I q k1) = p1)\<close> \<open>lv I q (Suc ?A) p1 = ((tv I q ?T = tv I q k2) = p1)\<close> for p1
    using lv_new[OF assms(8), of ?A ?T k1] lv_new[OF assms(8), of \<open>Suc ?A\<close> ?T k2] r ba b by (simp_all add: nth_append)
  note c = cls_new[OF assms(10) conjunct1[OF r]]
  show ?thesis using c ba at r by (auto simp: clause_true_mk lit_true_m lv_neg lv_False)
qed

subsection \<open>Relating translated terms to values\<close>

text \<open>\<open>ru v d\<close>: the element \<open>d\<close> of the translation stands for the value \<open>v\<close> of an uninterpreted
  sort. It must relate only elements of uninterpreted sorts and be injective both ways.\<close>
definition ru_ok :: \<open>(sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>ru_ok ru \<equiv> (\<forall>v d. ru v d \<longrightarrow> (\<exists>x. v = VElem x)) \<and> (\<forall>v d v' d'. ru v d \<longrightarrow> ru v' d' \<longrightarrow> (v = v') = (d = d'))\<close>

text \<open>The translation \<open>e\<close> of a term of sort \<open>so\<close> stands for the value \<open>v\<close>: a Boolean term is a
  literal with the truth value of \<open>v\<close>, another term a term whose element stands for \<open>v\<close>.\<close>
definition enc_ok :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> (sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> SmtSort \<Rightarrow> sval \<Rightarrow> enc_m \<Rightarrow> bool\<close> where
  \<open>enc_ok I q ru so v e \<equiv> (case e of
      ELit a pos \<Rightarrow> so = SmtSort_Bool \<and> v = VBool (lv I q a pos)
    | ETerm k \<Rightarrow> so \<noteq> SmtSort_Bool \<and> ru v (tv I q k))\<close>

text \<open>The element \<open>d\<close> stands for the value \<open>v\<close> of sort \<open>so\<close>: a truth value is the value of TRUE or
  of FALSE.\<close>
definition vrel :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> (sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> SmtSort \<Rightarrow> sval \<Rightarrow> 'd \<Rightarrow> bool\<close> where
  \<open>vrel I q ru so v d \<equiv>
     (if so = SmtSort_Bool then \<exists>b. v = VBool b \<and> d = (if b then tv I q 0 else tv I q 1) else ru v d)\<close>

definition lve :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> enc_m \<Rightarrow> bool\<close> where
  \<open>lve I q e \<equiv> lv I q (fst (enc_lit_m e)) (snd (enc_lit_m e))\<close>

lemma enc_ok_bool: \<open>enc_ok I q ru SmtSort_Bool v e \<Longrightarrow> v = VBool (lve I q e) \<and> is_lit_m e\<close>
  by (cases e) (auto simp: enc_ok_def lve_def)

lemma bool_vals:
  assumes \<open>length vs = length es\<close> \<open>\<forall>i < length es. enc_ok I q ru SmtSort_Bool (vs ! i) (es ! i)\<close>
  shows \<open>vs = map (\<lambda>e. VBool (lve I q e)) es\<close>
  using assms by (intro nth_equalityI) (auto dest: enc_ok_bool)

lemma enc_ok_lit: \<open>enc_ok I q ru so v e \<Longrightarrow> is_lit_m e = (so = SmtSort_Bool)\<close>
  by (cases e) (auto simp: enc_ok_def)

subsection \<open>Folds\<close>

lemma eq_fold_sem:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>i < length es. enc_wf s (es ! i) \<and> enc_ok I q ru so (vs ! i) (es ! i)\<close> \<open>length vs = length es\<close>
    \<open>\<forall>ij \<in> set prs. fst ij < length es \<and> snd ij < length es\<close> \<open>ru_ok ru\<close> \<open>\<forall>l \<in> set ls. lit_wf s l\<close>
    \<open>foldl (eq_step_m es dst) (s, ls) prs = (s', ls')\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>(\<forall>l \<in> set ls'. lv I q (fst l) (snd l)) =
    ((\<forall>l \<in> set ls. lv I q (fst l) (snd l)) \<and> (\<forall>ij \<in> set prs. (vs ! fst ij = vs ! snd ij) = (\<not> dst)))\<close>
  using assms
proof (induction prs arbitrary: s ls)
  case Nil
  then show ?case by simp
next
  case (Cons ij prs)
  obtain i j where ij: \<open>ij = (i, j)\<close> by (cases ij)
  obtain s1 ls1 where st: \<open>eq_step_m es dst (s, ls) (i, j) = (s1, ls1)\<close> by (cases \<open>eq_step_m es dst (s, ls) (i, j)\<close>)
  have f: \<open>foldl (eq_step_m es dst) (s1, ls1) prs = (s', ls')\<close> using Cons.prems(7) ij st by simp
  have p1: \<open>pre s1 s'\<close> using pre_eq_fold[of s1 \<open>(s1, ls1)\<close> es dst prs] f pre_refl by simp
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p1 Cons.prems(8)] .
  have c1: \<open>cls_true q I s1\<close> using cls_true_pre[OF p1 Cons.prems(10)] .
  have ijl: \<open>i < length es\<close> \<open>j < length es\<close> using Cons.prems(4) ij by auto
  have ew: \<open>\<forall>i < length es. enc_wf s (es ! i)\<close> using Cons.prems(2) by simp
  have li: \<open>\<forall>i < length es. \<forall>j < length es. is_lit_m (es ! i) = is_lit_m (es ! j)\<close>
    using Cons.prems(2) enc_ok_lit by metis
  have W: \<open>st_wf nf s1 \<and> (\<forall>l \<in> set ls1. lit_wf s1 l) \<and> ext q s s1 \<and> pre s s1\<close>
    using eq_fold_wb[where prs=\<open>[(i, j)]\<close> and s'=s1 and ls'=ls1 and dst=dst and q=q, OF Cons.prems(1) ew li _ Cons.prems(6)]
      ijl st q1 Cons.prems(9) by simp
  have S: \<open>\<exists>l. ls1 = ls @ [l] \<and> lv I q (fst l) (snd l) = ((vs ! i = vs ! j) = (\<not> dst))\<close>
  proof (cases \<open>is_lit_m (es ! i)\<close>)
    case True
    then have \<open>is_lit_m (es ! j)\<close> using li ijl by blast
    then obtain a pa b pb where ei: \<open>es ! i = ELit a pa\<close> \<open>es ! j = ELit b pb\<close>
      using True by (cases \<open>es ! i\<close>; cases \<open>es ! j\<close>) auto
    have vv: \<open>vs ! i = VBool (lv I q a pa)\<close> \<open>vs ! j = VBool (lv I q b pb)\<close>
      using Cons.prems(2) ijl ei by (auto simp: enc_ok_def)
    obtain sx x where gx: \<open>gate_xor_m s (a, pa) (b, pb) = (sx, x)\<close> by (cases \<open>gate_xor_m s (a, pa) (b, pb)\<close>)
    have e: \<open>eq_step_m es dst (s, ls) (i, j) = (sx, ls @ [(fst x, if dst then snd x else \<not> snd x)])\<close>
      using gx ei by (simp add: eq_step_m_def Let_def)
    have st': \<open>s1 = sx\<close> \<open>ls1 = ls @ [(fst x, if dst then snd x else \<not> snd x)]\<close> using st e by simp_all
    have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> using ew ijl ei by (auto simp: enc_wf_def)
    have G: \<open>lv I q (fst x) (snd x) = (lv I q a pa \<noteq> lv I q b pb)\<close>
      using gate_xor_sem[OF ab gx _ Cons.prems(9)] q1 c1 st' by simp
    show ?thesis using G vv st' by (cases dst) (auto simp: lv_neg)
  next
    case False
    then have \<open>\<not> is_lit_m (es ! j)\<close> using li ijl by blast
    then obtain ki kj where ei: \<open>es ! i = ETerm ki\<close> \<open>es ! j = ETerm kj\<close>
      using False by (cases \<open>es ! i\<close>; cases \<open>es ! j\<close>) auto
    have vv: \<open>ru (vs ! i) (tv I q ki)\<close> \<open>ru (vs ! j) (tv I q kj)\<close>
      using Cons.prems(2) ijl ei by (auto simp: enc_ok_def)
    obtain sx k where gx: \<open>add_atom_m s ki kj = (sx, k)\<close> by (cases \<open>add_atom_m s ki kj\<close>)
    have e: \<open>eq_step_m es dst (s, ls) (i, j) = (sx, ls @ [(k, \<not> dst)])\<close>
      using gx ei by (simp add: eq_step_m_def Let_def)
    have st': \<open>s1 = sx\<close> \<open>ls1 = ls @ [(k, \<not> dst)]\<close> using st e by simp_all
    have ab: \<open>ki < length (st_terms s)\<close> \<open>kj < length (st_terms s)\<close> using ew ijl ei by (auto simp: enc_wf_def)
    have sx: \<open>sx = St (st_terms s) (st_atoms s @ [make_Atom (word_of_nat ki) (word_of_nat kj)]) (st_clauses s) (st_next s)\<close>
      \<open>k = length (st_atoms s)\<close> using gx by (auto simp: add_atom_m_def)
    have b: \<open>length (st_terms s) < 2 ^ 64\<close> using pre_len[OF q1] Cons.prems(9) st' sx by (auto simp: bnd_def)
    have L: \<open>lv I q k (\<not> dst) = ((tv I q ki = tv I q kj) = (\<not> dst))\<close>
      using lv_new[OF q1, of k ki kj] st' sx ab b by simp
    have \<open>(vs ! i = vs ! j) = (tv I q ki = tv I q kj)\<close> using Cons.prems(5) vv by (simp add: ru_ok_def)
    then show ?thesis using L st' by auto
  qed
  then obtain l where l: \<open>ls1 = ls @ [l]\<close> \<open>lv I q (fst l) (snd l) = ((vs ! i = vs ! j) = (\<not> dst))\<close> by blast
  have e1: \<open>\<forall>i < length es. enc_wf s1 (es ! i) \<and> enc_ok I q ru so (vs ! i) (es ! i)\<close>
    using Cons.prems(2) W enc_wf_pre[of s s1] by blast
  have pr: \<open>\<forall>ij \<in> set prs. fst ij < length es \<and> snd ij < length es\<close> using Cons.prems(4) by simp
  have IH: \<open>(\<forall>l \<in> set ls'. lv I q (fst l) (snd l)) =
    ((\<forall>l \<in> set ls1. lv I q (fst l) (snd l)) \<and> (\<forall>ij \<in> set prs. (vs ! fst ij = vs ! snd ij) = (\<not> dst)))\<close>
    using Cons.IH[OF conjunct1[OF W] e1 Cons.prems(3) pr Cons.prems(5) conjunct1[OF conjunct2[OF W]] f Cons.prems(8,9,10)] .
  show ?case using IH l ij by auto
qed

lemma xor_fold_sem:
  assumes \<open>st_wf nf s\<close> \<open>\<forall>e \<in> set es. enc_wf s e\<close> \<open>lit_wf s acc\<close>
    \<open>foldl xor_step_m (s, acc) es = (s', l)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>lv I q (fst l) (snd l) = (lv I q (fst acc) (snd acc) \<noteq> odd (length (filter (lve I q) es)))\<close>
  using assms
proof (induction es arbitrary: s acc)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain a pa where acc: \<open>acc = (a, pa)\<close> by (cases acc)
  obtain b pb where el: \<open>enc_lit_m e = (b, pb)\<close> by (cases \<open>enc_lit_m e\<close>)
  obtain s1 x where gx: \<open>gate_xor_m s (a, pa) (b, pb) = (s1, x)\<close> by (cases \<open>gate_xor_m s (a, pa) (b, pb)\<close>)
  have st: \<open>xor_step_m (s, acc) e = (s1, x)\<close> using acc el gx by (simp add: xor_step_m_def)
  have f: \<open>foldl xor_step_m (s1, x) es = (s', l)\<close> using Cons.prems(4) st by simp
  have p1: \<open>pre s1 s'\<close> using pre_xor_fold[of s1 \<open>(s1, x)\<close> es] f pre_refl by simp
  have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close>
    using Cons.prems(3) acc enc_lit_wf[OF Cons.prems(1), of e] Cons.prems(2) el by (auto simp: lit_wf_def)
  have W: \<open>st_wf nf s1 \<and> lit_wf s1 x \<and> ext q s s1 \<and> pre s s1\<close>
    using gate_xor_wb[OF Cons.prems(1) ab gx pre_trans[OF p1 Cons.prems(5)] Cons.prems(6)] .
  have G: \<open>lv I q (fst x) (snd x) = (lv I q a pa \<noteq> lv I q b pb)\<close>
    using gate_xor_sem[OF ab gx pre_trans[OF p1 Cons.prems(5)] Cons.prems(6) cls_true_pre[OF p1 Cons.prems(7)]] .
  have e1: \<open>\<forall>e \<in> set es. enc_wf s1 e\<close> using Cons.prems(2) W enc_wf_pre[of s s1] by simp
  have IH: \<open>lv I q (fst l) (snd l) = (lv I q (fst x) (snd x) \<noteq> odd (length (filter (lve I q) es)))\<close>
    using Cons.IH[OF conjunct1[OF W] e1 conjunct1[OF conjunct2[OF W]] f Cons.prems(5,6,7)] .
  have le: \<open>lve I q e = lv I q b pb\<close> using el by (simp add: lve_def)
  show ?case using IH G le acc by auto
qed

lemma enc_terms_sem:
  assumes \<open>st_wf nf s\<close> \<open>length ss = length es\<close> \<open>length vs = length es\<close>
    \<open>\<forall>i < length es. enc_wf s (es ! i) \<and> enc_ok I q ru (ss ! i) (vs ! i) (es ! i)\<close>
    \<open>foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s, ts) es = (s', ts')\<close>
    \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>\<exists>new. ts' = ts @ new \<and> length new = length es \<and> (\<forall>i < length es. vrel I q ru (ss ! i) (vs ! i) (tv I q (new ! i)))\<close>
  using assms
proof (induction es arbitrary: s ts ss vs)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain so ss' where ss: \<open>ss = so # ss'\<close> using Cons.prems(2) by (cases ss) auto
  obtain v vs' where vs: \<open>vs = v # vs'\<close> using Cons.prems(3) by (cases vs) auto
  obtain s1 k where r: \<open>enc_term_m s e = (s1, k)\<close> by (cases \<open>enc_term_m s e\<close>)
  have f: \<open>foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s1, ts @ [k]) es = (s', ts')\<close>
    using Cons.prems(5) r by simp
  have p1: \<open>pre s1 s'\<close> using pre_enc_terms[of s1 \<open>(s1, ts @ [k])\<close> es] f pre_refl by simp
  have p0: \<open>pre s s1\<close> using pre_enc_term[OF pre_refl, of s e] r by simp
  have h0: \<open>enc_wf s e\<close> \<open>enc_ok I q ru so v e\<close> using Cons.prems(4) ss vs by auto
  have W: \<open>st_wf nf s1 \<and> k < length (st_terms s1) \<and> ext q s s1\<close>
    using enc_term_wb[OF Cons.prems(1) h0(1) r pre_trans[OF p1 Cons.prems(6)] Cons.prems(7)] .
  have V: \<open>vrel I q ru so v (tv I q k)\<close>
  proof (cases e)
    case (ETerm i)
    then show ?thesis using h0(2) r by (simp add: enc_ok_def vrel_def)
  next
    case (ELit a pos)
    have \<open>tv I q k = (if lv I q a pos then tv I q 0 else tv I q 1)\<close>
      using enc_term_sem[OF _ _ pre_trans[OF p1 Cons.prems(6)] Cons.prems(7) cls_true_pre[OF p1 Cons.prems(8)]] h0(1) r ELit
      by simp
    then show ?thesis using h0(2) ELit by (simp add: enc_ok_def vrel_def)
  qed
  have e1: \<open>\<forall>i < length es. enc_wf s1 (es ! i) \<and> enc_ok I q ru (ss' ! i) (vs' ! i) (es ! i)\<close>
    using Cons.prems(4) ss vs enc_wf_pre[OF p0] by auto
  obtain new where n: \<open>ts' = (ts @ [k]) @ new\<close> \<open>length new = length es\<close>
    \<open>\<forall>i < length es. vrel I q ru (ss' ! i) (vs' ! i) (tv I q (new ! i))\<close>
    using Cons.IH[OF conjunct1[OF W] _ _ e1 f Cons.prems(6,7,8)] Cons.prems(2,3) ss vs by auto
  show ?case
  proof (intro exI conjI)
    show \<open>ts' = ts @ (k # new)\<close> using n by simp
    show \<open>length (k # new) = length (e # es)\<close> using n by simp
    show \<open>\<forall>i < length (e # es). vrel I q ru (ss ! i) (vs ! i) (tv I q ((k # new) ! i))\<close>
      using V n(3) ss vs by (auto simp: nth_Cons split: nat.splits)
  qed
qed

subsection \<open>Theory functions\<close>

lemma implies_val:
  assumes \<open>2 \<le> length bs\<close>
  shows \<open>(\<exists>i < length bs. (if i + 1 < length bs then \<not> bs ! i else bs ! i)) =
    ((\<exists>b \<in> set (butlast bs). \<not> b) \<or> last bs)\<close>
proof -
  let ?n = \<open>length bs\<close>
  have l: \<open>last bs = bs ! (?n - 1)\<close> using assms by (intro last_conv_nth) auto
  have b: \<open>(\<exists>b \<in> set (butlast bs). \<not> b) = (\<exists>i < ?n - 1. \<not> bs ! i)\<close>
    by (metis (no_types, lifting) in_set_conv_nth length_butlast nth_butlast)
  have m: \<open>(\<exists>i < ?n. (if i + 1 < ?n then \<not> bs ! i else bs ! i)) = ((\<exists>i < ?n - 1. \<not> bs ! i) \<or> bs ! (?n - 1))\<close>
  proof
    assume \<open>\<exists>i < ?n. (if i + 1 < ?n then \<not> bs ! i else bs ! i)\<close>
    then obtain i where i: \<open>i < ?n\<close> \<open>if i + 1 < ?n then \<not> bs ! i else bs ! i\<close> by blast
    show \<open>(\<exists>i < ?n - 1. \<not> bs ! i) \<or> bs ! (?n - 1)\<close>
    proof (cases \<open>i + 1 < ?n\<close>)
      case True
      then show ?thesis using i by (intro disjI1) (auto intro!: exI[of _ i])
    next
      case False
      then have \<open>i = ?n - 1\<close> using i(1) by simp
      then show ?thesis using i False by simp
    qed
  next
    assume \<open>(\<exists>i < ?n - 1. \<not> bs ! i) \<or> bs ! (?n - 1)\<close>
    then show \<open>\<exists>i < ?n. (if i + 1 < ?n then \<not> bs ! i else bs ! i)\<close>
    proof
      assume \<open>\<exists>i < ?n - 1. \<not> bs ! i\<close>
      then obtain i where \<open>i < ?n - 1\<close> \<open>\<not> bs ! i\<close> by blast
      then show ?thesis by (intro exI[of _ i]) auto
    next
      assume \<open>bs ! (?n - 1)\<close>
      then show ?thesis using assms by (intro exI[of _ \<open>?n - 1\<close>]) auto
    qed
  qed
  show ?thesis using l b m by simp
qed

lemma enc_app_sem:
  assumes \<open>st_wf nf s\<close> \<open>smt_core_op op\<close> \<open>smt_op_sort op ss = Some so\<close> \<open>length es = length ss\<close> \<open>length vs = length ss\<close>
    \<open>\<forall>i < length es. enc_wf s (es ! i) \<and> enc_ok I q ru (ss ! i) (vs ! i) (es ! i)\<close> \<open>ru_ok ru\<close>
    \<open>enc_app_m s op es = (s', e)\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>cls_true q I s'\<close>
  shows \<open>enc_ok I q ru so (smt_op_sem op vs) e\<close>
proof -
  have ew: \<open>\<forall>x \<in> set es. enc_wf s x\<close> using assms(6) by (auto simp: in_set_conv_nth)
  have lw: \<open>\<forall>l \<in> set (map enc_lit_m es). lit_wf s l\<close> using ew enc_lit_wf[OF assms(1)] by auto
  have bv: \<open>vs = map (\<lambda>e. VBool (lve I q e)) es\<close> if a: \<open>set ss \<subseteq> {SmtSort_Bool}\<close>
  proof -
    have \<open>\<forall>i < length es. enc_ok I q ru SmtSort_Bool (vs ! i) (es ! i)\<close>
    proof (intro allI impI)
      fix i assume i: \<open>i < length es\<close>
      then have \<open>ss ! i \<in> set ss\<close> using assms(4) by simp
      then have \<open>ss ! i = SmtSort_Bool\<close> using a by blast
      then show \<open>enc_ok I q ru SmtSort_Bool (vs ! i) (es ! i)\<close> using assms(6) i by metis
    qed
    then show ?thesis using bool_vals[of vs es I q ru] assms(4,5) by simp
  qed
  consider (Not) \<open>op = SmtOp_Not\<close> | (AO) \<open>op = SmtOp_And \<or> op = SmtOp_Or\<close> | (Xor) \<open>op = SmtOp_Xor\<close>
    | (Imp) \<open>op = SmtOp_Implies\<close> | (Eq) \<open>op = SmtOp_Eq \<or> op = SmtOp_Distinct\<close> | (Ite) \<open>op = SmtOp_Ite\<close>
    using assms(2) by (cases op) auto
  then show ?thesis
  proof cases
    case Not
    have o: \<open>smt_op_sort SmtOp_Not ss = Some so\<close> using assms(3) Not by (simp only:)
    have ss: \<open>ss = [SmtSort_Bool]\<close> \<open>so = SmtSort_Bool\<close> using op_sort_not[OF o] by simp_all
    have v: \<open>vs = [VBool (lve I q (es ! 0))]\<close> using bv ss assms(4) by (cases es) auto
    have h0: \<open>enc_ok I q ru SmtSort_Bool (vs ! 0) (es ! 0)\<close> using assms(4,6) ss by simp
    have l0: \<open>is_lit_m (es ! 0)\<close> using enc_ok_lit[OF h0] by simp
    then obtain a pos where e0: \<open>es ! 0 = ELit a pos\<close> by (cases \<open>es ! 0\<close>) auto
    have \<open>e = ELit a (\<not> pos)\<close> using assms(8) Not e0 by auto
    then show ?thesis using v e0 ss Not by (simp add: enc_ok_def lve_def lv_neg)
  next
    case AO
    have ss: \<open>so = SmtSort_Bool\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> using op_sort_bool[of op ss so] AO assms(3) by auto
    have g: \<open>gate_andor_m s (map enc_lit_m es) (op = SmtOp_And) = (s', e)\<close> using assms(8) AO by auto
    have G: \<open>e = ELit (length (st_atoms s)) True \<and> lv I q (length (st_atoms s)) True =
      (if op = SmtOp_And then \<forall>l \<in> set (map enc_lit_m es). lv I q (fst l) (snd l) else \<exists>l \<in> set (map enc_lit_m es). lv I q (fst l) (snd l))\<close>
      using gate_andor_sem[OF lw g assms(9,10,11)] .
    show ?thesis using G bv[OF ss(2)] ss(1) AO by (auto simp: enc_ok_def lve_def)
  next
    case Imp
    have ss: \<open>so = SmtSort_Bool\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>2 \<le> length ss\<close> using op_sort_bool[of op ss so] Imp assms(3) by auto
    have g: \<open>gate_andor_m s (implies_lits_m es) False = (s', e)\<close> using assms(8) Imp by auto
    have lw': \<open>\<forall>l \<in> set (implies_lits_m es). lit_wf s l\<close> using lw by (auto simp: implies_lits_m_def lit_wf_def)
    have G: \<open>e = ELit (length (st_atoms s)) True \<and> lv I q (length (st_atoms s)) True =
      (\<exists>l \<in> set (implies_lits_m es). lv I q (fst l) (snd l))\<close>
      using gate_andor_sem[OF lw' g assms(9,10,11)] by simp
    let ?bs = \<open>map (lve I q) es\<close>
    have ex: \<open>(\<exists>l \<in> set (implies_lits_m es). lv I q (fst l) (snd l)) =
        (\<exists>i < length ?bs. (if i + 1 < length ?bs then \<not> ?bs ! i else ?bs ! i))\<close>
      by (auto simp: implies_lits_m_def lve_def lv_neg)
    have ne: \<open>es \<noteq> []\<close> using ss(3) assms(4) by auto
    have I1: \<open>smt_op_sem SmtOp_Implies vs = VBool ((\<exists>x \<in> set (butlast es). \<not> lve I q x) \<or> lve I q (last es))\<close>
      using bv[OF ss(2)] ne by (simp add: map_butlast[symmetric] last_map)
    have I2: \<open>((\<exists>b \<in> set (butlast ?bs). \<not> b) \<or> last ?bs) = ((\<exists>x \<in> set (butlast es). \<not> lve I q x) \<or> lve I q (last es))\<close>
      using ne by (simp add: map_butlast[symmetric] last_map)
    have \<open>smt_op_sem SmtOp_Implies vs = VBool ((\<exists>b \<in> set (butlast ?bs). \<not> b) \<or> last ?bs)\<close>
      using I1 I2 by simp
    then show ?thesis using G ex implies_val[of ?bs] ss(1,3) assms(4) Imp by (simp add: enc_ok_def)
  next
    case Xor
    have ss: \<open>so = SmtSort_Bool\<close> \<open>set ss \<subseteq> {SmtSort_Bool}\<close> \<open>2 \<le> length ss\<close> using op_sort_bool[of op ss so] Xor assms(3) by auto
    obtain e0 es' where es: \<open>es = e0 # es'\<close> using ss(3) assms(4) by (cases es) auto
    obtain s1 l where r: \<open>foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es) = (s1, l)\<close>
      by (cases \<open>foldl xor_step_m (s, enc_lit_m (es ! 0)) (tl es)\<close>)
    have se: \<open>s' = s1\<close> \<open>e = ELit (fst l) (snd l)\<close> using assms(8) Xor r by auto
    have a0: \<open>lit_wf s (enc_lit_m (es ! 0))\<close> using lw es by simp
    have et: \<open>\<forall>x \<in> set (tl es). enc_wf s x\<close> using ew es by simp
    have X: \<open>lv I q (fst l) (snd l) = (lve I q e0 \<noteq> odd (length (filter (lve I q) es')))\<close>
      using xor_fold_sem[OF assms(1) et a0 r] assms(9,10,11) se es by (simp add: lve_def)
    have \<open>smt_op_sem SmtOp_Xor vs = VBool (odd (length (filter (lve I q) es)))\<close>
      using bv[OF ss(2)] by (simp add: filter_map comp_def)
    then show ?thesis using X se ss(1) es Xor by (simp add: enc_ok_def)
  next
    case Eq
    have ss: \<open>so = SmtSort_Bool\<close> \<open>set ss \<subseteq> {hd ss}\<close> \<open>2 \<le> length ss\<close> using op_sort_eq[of op ss so] Eq assms(3) by auto
    let ?d = \<open>op = SmtOp_Distinct\<close>
    obtain s1 ls where r: \<open>foldl (eq_step_m es ?d) (s, []) (eq_pairs_m (length es) ?d) = (s1, ls)\<close>
      by (cases \<open>foldl (eq_step_m es ?d) (s, []) (eq_pairs_m (length es) ?d)\<close>)
    have g: \<open>gate_andor_m s1 ls True = (s', e)\<close> using assms(8) Eq r by (auto simp: enc_eq_m_def)
    have p1: \<open>pre s1 s'\<close> using pre_gate_andor[OF pre_refl, of s1 ls True] g by simp
    have sh: \<open>\<forall>i < length es. ss ! i = hd ss\<close> using ss(2) assms(4) by (auto simp: subset_iff)
    have e1: \<open>\<forall>i < length es. enc_wf s (es ! i) \<and> enc_ok I q ru (hd ss) (vs ! i) (es ! i)\<close> using assms(6) sh by simp
    have prs: \<open>\<forall>ij \<in> set (eq_pairs_m (length es) ?d). fst ij < length es \<and> snd ij < length es\<close>
      by (auto simp: eq_pairs_set)
    have li: \<open>\<forall>i < length es. \<forall>j < length es. is_lit_m (es ! i) = is_lit_m (es ! j)\<close>
      using e1 enc_ok_lit by metis
    have W: \<open>st_wf nf s1 \<and> (\<forall>l \<in> set ls. lit_wf s1 l) \<and> ext q s s1 \<and> pre s s1\<close>
      using eq_fold_wb[OF assms(1) _ li prs _ r pre_trans[OF p1 assms(9)] assms(10)] e1 by simp
    have F: \<open>(\<forall>l \<in> set ls. lv I q (fst l) (snd l)) =
        (\<forall>ij \<in> set (eq_pairs_m (length es) ?d). (vs ! fst ij = vs ! snd ij) = (\<not> ?d))\<close>
      using eq_fold_sem[OF assms(1) e1 _ prs assms(7) _ r pre_trans[OF p1 assms(9)] assms(10) cls_true_pre[OF p1 assms(11)]]
        assms(4,5) by simp
    have G: \<open>e = ELit (length (st_atoms s1)) True \<and> lv I q (length (st_atoms s1)) True = (\<forall>l \<in> set ls. lv I q (fst l) (snd l))\<close>
      using gate_andor_sem[OF conjunct1[OF conjunct2[OF W]] g assms(9,10,11)] by simp
    have V: \<open>smt_op_sem op vs = VBool (\<forall>ij \<in> set (eq_pairs_m (length es) ?d). (vs ! fst ij = vs ! snd ij) = (\<not> ?d))\<close>
    proof (cases ?d)
      case True
      then show ?thesis using assms(4,5) by (auto simp: eq_pairs_set distinct_conv_nth) (metis linorder_neqE_nat)
    next
      case False
      then have \<open>op = SmtOp_Eq\<close> using Eq by simp
      then show ?thesis using False assms(4,5) by (auto simp: eq_pairs_set)
    qed
    show ?thesis using F G V ss(1) by (simp add: enc_ok_def)
  next
    case Ite
    have ss: \<open>ss = [SmtSort_Bool, so, so]\<close> using op_sort_ite assms(3) Ite by simp
    have l3: \<open>length es = 3\<close> \<open>length vs = 3\<close> using assms(4,5) ss by simp_all
    have h: \<open>enc_ok I q ru SmtSort_Bool (vs ! 0) (es ! 0)\<close> \<open>enc_ok I q ru so (vs ! 1) (es ! 1)\<close>
      \<open>enc_ok I q ru so (vs ! 2) (es ! 2)\<close> \<open>enc_wf s (es ! 0)\<close> \<open>enc_wf s (es ! 1)\<close> \<open>enc_wf s (es ! 2)\<close>
      using assms(6) l3 ss by (auto simp: numeral_eq_Suc)
    obtain kc pc where c: \<open>es ! 0 = ELit kc pc\<close> using enc_ok_lit[OF h(1)] by (cases \<open>es ! 0\<close>) auto
    have vc: \<open>vs ! 0 = VBool (lv I q kc pc)\<close> using h(1) c by (simp add: enc_ok_def)
    have kc: \<open>kc < length (st_atoms s)\<close> using h(4) c by (simp add: enc_wf_def)
    have sem: \<open>smt_op_sem SmtOp_Ite vs = (if lv I q kc pc then vs ! 1 else vs ! 2)\<close> using vc by simp
    show ?thesis
    proof (cases \<open>is_lit_m (es ! 1)\<close>)
      case True
      then have sb: \<open>so = SmtSort_Bool\<close> using enc_ok_lit[OF h(2)] by simp
      obtain a pa where a: \<open>es ! 1 = ELit a pa\<close> using True by (cases \<open>es ! 1\<close>) auto
      obtain b pb where b: \<open>es ! 2 = ELit b pb\<close> using enc_ok_lit[OF h(3)] sb by (cases \<open>es ! 2\<close>) auto
      have g: \<open>gate_ite_m s (kc, pc) (a, pa) (b, pb) = (s', e)\<close> using assms(8) Ite True a b c by simp
      have ab: \<open>a < length (st_atoms s)\<close> \<open>b < length (st_atoms s)\<close> using h(5,6) a b by (simp_all add: enc_wf_def)
      have G: \<open>e = ELit (length (st_atoms s)) True \<and>
          lv I q (length (st_atoms s)) True = (if lv I q kc pc then lv I q a pa else lv I q b pb)\<close>
        using gate_ite_sem[OF kc ab g assms(9,10,11)] .
      have \<open>vs ! 1 = VBool (lv I q a pa)\<close> \<open>vs ! 2 = VBool (lv I q b pb)\<close> using h(2,3) a b by (simp_all add: enc_ok_def)
      then show ?thesis using G sem sb Ite by (simp add: enc_ok_def)
    next
      case False
      then have sb: \<open>so \<noteq> SmtSort_Bool\<close> using enc_ok_lit[OF h(2)] by simp
      obtain k1 where a: \<open>es ! 1 = ETerm k1\<close> using False by (cases \<open>es ! 1\<close>) auto
      obtain k2 where b: \<open>es ! 2 = ETerm k2\<close> using enc_ok_lit[OF h(3)] sb by (cases \<open>es ! 2\<close>) auto
      have g: \<open>ite_term_m s es = (s', e)\<close> using assms(8) Ite False by simp
      have ab: \<open>k1 < length (st_terms s)\<close> \<open>k2 < length (st_terms s)\<close> using h(5,6) a b by (simp_all add: enc_wf_def)
      have c': \<open>enc_lit_m (es ! 0) = (kc, pc)\<close> using c by simp
      have G: \<open>e = ETerm (length (st_terms s)) \<and>
          tv I q (length (st_terms s)) = (if lv I q kc pc then tv I q k1 else tv I q k2)\<close>
        using ite_term_sem[OF c' kc a b ab g assms(9,10,11)] .
      have \<open>ru (vs ! 1) (tv I q k1)\<close> \<open>ru (vs ! 2) (tv I q k2)\<close> using h(2,3) a b by (simp_all add: enc_ok_def)
      then show ?thesis using G sem sb Ite by (simp add: enc_ok_def)
    qed
  qed
qed

subsection \<open>Meanings of definitions\<close>

lemma smt_def_sems_snoc:
  \<open>smt_def_sems I (ds @ [d]) = smt_def_sems I ds @ [\<lambda>vs. smt_eval I (smt_def_sems I ds) vs (SmtDef_body d)]\<close>
  by (simp add: smt_def_sems_def)

lemma smt_def_sems_length: \<open>length (smt_def_sems I ds) = length ds\<close>
  by (induction ds rule: rev_induct) (simp_all add: smt_def_sems_snoc, simp add: smt_def_sems_def)

lemma smt_def_sems_nth:
  \<open>d < length ds \<Longrightarrow> smt_def_sems I ds ! d = (\<lambda>vs. smt_eval I (take d (smt_def_sems I ds)) vs (SmtDef_body (ds ! d)))\<close>
proof (induction ds rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ds)
  show ?case
  proof (cases \<open>d < length ds\<close>)
    case True
    then show ?thesis using snoc.IH by (simp add: smt_def_sems_snoc nth_append smt_def_sems_length)
  next
    case False
    then have \<open>d = length ds\<close> using snoc.prems by simp
    then show ?thesis by (simp add: smt_def_sems_snoc nth_append smt_def_sems_length)
  qed
qed

lemma map_Some_ex: \<open>map g args = map Some L \<Longrightarrow> a \<in> set args \<Longrightarrow> \<exists>y. g a = Some y\<close>
  by (induction args arbitrary: L) auto

lemma smt_eval_take:
  \<open>smt_tsort fs (take d ds) ps t \<noteq> None \<Longrightarrow> length dv = length ds \<Longrightarrow>
     smt_eval I (take d dv) xs t = smt_eval I dv xs t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close>
    using SmtTerm_Fun.prems(1) by (auto split: if_splits intro: map_Some_ex)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_Fun.IH SmtTerm_Fun.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  then show ?case by (metis smt_eval.simps(4))
next
  case (SmtTerm_Def d' args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close> and u: \<open>unat d' < length (take d ds)\<close>
    using SmtTerm_Def.prems(1) by (auto split: if_splits intro: map_Some_ex)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_Def.IH SmtTerm_Def.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  moreover have \<open>take d dv ! unat d' = dv ! unat d'\<close> using u SmtTerm_Def.prems(2) by simp
  ultimately show ?case by (metis smt_eval.simps(5))
next
  case (SmtTerm_App op args)
  have \<open>\<forall>a \<in> set args. \<exists>y. smt_tsort fs (take d ds) ps a = Some y\<close>
    using SmtTerm_App.prems(1) by (auto split: if_splits) (metis image_eqI option.exhaust)
  then have e: \<open>\<forall>a \<in> set args. smt_eval I (take d dv) xs a = smt_eval I dv xs a\<close>
    using SmtTerm_App.IH SmtTerm_App.prems(2) by blast
  have \<open>map (smt_eval I (take d dv) xs) args = map (smt_eval I dv xs) args\<close> using e by (intro map_cong) auto
  then show ?case by (metis smt_eval.simps(6))
qed auto

subsection \<open>The translation of terms\<close>

text \<open>The declared symbols of \<open>p\<close> and their translations agree: applied to elements that stand
  for values of the argument sorts, a symbol gives an element that stands for the value of the
  symbol (for a Boolean symbol: the element is TRUE exactly when the value is true).\<close>
definition jrel :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> (sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> bool\<close> where
  \<open>jrel p I q ru J \<equiv> \<forall>f < length (SmtProblem_funs p). \<forall>vs ds.
     let sg = SmtProblem_funs p ! f in
     length vs = length (SmtFun_args sg) \<and> length ds = length (SmtFun_args sg) \<and>
     (\<forall>i < length (SmtFun_args sg). vrel I q ru (SmtFun_args sg ! i) (vs ! i) (ds ! i)) \<longrightarrow>
     (if SmtFun_ret sg = SmtSort_Bool then J f vs = VBool (I f ds = tv I q 0) else ru (J f vs) (I f ds))\<close>

definition env_sem :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> (sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> SmtSort list \<Rightarrow> sval list \<Rightarrow> enc_m list \<Rightarrow> bool\<close> where
  \<open>env_sem I q ru ps xs env \<equiv> length xs = length ps \<and> (\<forall>i < length ps. enc_ok I q ru (ps ! i) (xs ! i) (env ! i))\<close>

definition dm_sem :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> st \<Rightarrow> (sval \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> nat \<Rightarrow> enc_m list \<Rightarrow> bool\<close> where
  \<open>dm_sem p I q ru J n dm \<equiv> \<forall>d < n. SmtDef_params (SmtProblem_defs p ! d) = [] \<longrightarrow>
     enc_ok I q ru (SmtDef_ret (SmtProblem_defs p ! d)) ((smt_def_sems J (SmtProblem_defs p) ! d) []) (dm ! d)\<close>

lemma lv_atom0: \<open>lv I q 0 True \<Longrightarrow> lv I q 0 b = b\<close>
  by (auto simp: lv_def)

lemma tr_sem:
  shows \<open>tr_term_m p dm env n s t = (s', e) \<Longrightarrow> smt_wf p \<Longrightarrow> smt_fragment p \<Longrightarrow> smt_term_no_bv t \<Longrightarrow>
     smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps t = Some so \<Longrightarrow>
     env_ok s ps env \<Longrightarrow> dm_ok p s n dm \<Longrightarrow> st_wf (length (SmtProblem_funs p)) s \<Longrightarrow> pre s' q \<Longrightarrow> bnd q \<Longrightarrow>
     ru_ok ru \<Longrightarrow> jrel p I q ru J \<Longrightarrow> lv I q 0 True \<Longrightarrow> env_sem I q ru ps xs env \<Longrightarrow> dm_sem p I q ru J n dm \<Longrightarrow>
     cls_true q I s' \<Longrightarrow>
     enc_ok I q ru so (smt_eval J (smt_def_sems J (SmtProblem_defs p)) xs t) e\<close>
    and \<open>tr_args_m p dm env n s ts = (s', es) \<Longrightarrow> smt_wf p \<Longrightarrow> smt_fragment p \<Longrightarrow> (\<forall>t \<in> set ts. smt_term_no_bv t) \<Longrightarrow>
     map (smt_tsort (SmtProblem_funs p) (take n (SmtProblem_defs p)) ps) ts = map Some ss \<Longrightarrow>
     env_ok s ps env \<Longrightarrow> dm_ok p s n dm \<Longrightarrow> st_wf (length (SmtProblem_funs p)) s \<Longrightarrow> pre s' q \<Longrightarrow> bnd q \<Longrightarrow>
     ru_ok ru \<Longrightarrow> jrel p I q ru J \<Longrightarrow> lv I q 0 True \<Longrightarrow> env_sem I q ru ps xs env \<Longrightarrow> dm_sem p I q ru J n dm \<Longrightarrow>
     cls_true q I s' \<Longrightarrow>
     \<forall>i < length ts. enc_ok I q ru (ss ! i) (smt_eval J (smt_def_sems J (SmtProblem_defs p)) xs (ts ! i)) (es ! i)\<close>
proof (induction p dm env n s t and p dm env n s ts arbitrary: s' e ps so xs and s' es ps ss xs rule: tr_term_m_tr_args_m.induct)
  case (1 p dm env n s b s' e ps so xs)
  then show ?case by (auto simp: enc_ok_def lv_atom0)
next
  case (2 p dm env n s bs s' e ps so xs)
  then show ?case by simp
next
  case (3 p dm env n s k s' e ps so xs)
  then show ?case by (auto simp: env_sem_def split: if_splits)
next
  case (4 p dm env n s f args s' e ps so xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close> and ?dv = \<open>smt_def_sems J (SmtProblem_defs p)\<close>
  let ?sg = \<open>SmtProblem_funs p ! unat f\<close> and ?vs = \<open>map (smt_eval J (smt_def_sems J (SmtProblem_defs p)) xs) args\<close>
  have ts: \<open>unat f < length ?fs\<close> \<open>map (smt_tsort ?fs (take n (SmtProblem_defs p)) ps) args = map Some (SmtFun_args ?sg)\<close>
    \<open>so = SmtFun_ret ?sg\<close> using 4(6) by (auto split: if_splits)
  have la: \<open>length args = length (SmtFun_args ?sg)\<close> using ts(2) by (metis length_map)
  obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  obtain s2 ts2 where r2: \<open>enc_terms_m s1 es1 = (s2, ts2)\<close> by (cases \<open>enc_terms_m s1 es1\<close>)
  obtain s3 k where r3: \<open>add_term_m s2 (unat f) ts2 = (s3, k)\<close> by (cases \<open>add_term_m s2 (unat f) ts2\<close>)
  have r2': \<open>foldl (\<lambda>(s, ts) e. let r = enc_term_m s e in (fst r, ts @ [snd r])) (s1, []) es1 = (s2, ts2)\<close>
    using r2 by (simp add: enc_terms_m_def)
  have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
  have p2: \<open>pre s1 s2\<close> using pre_enc_terms[of s1 \<open>(s1, [])\<close> es1] r2' pre_refl by simp
  have p3: \<open>pre s2 s3\<close> using pre_add_term[OF pre_refl, of s2 \<open>unat f\<close> ts2] r3 by simp
  have res: \<open>if SmtFun_ret ?sg = SmtSort_Bool
      then s' = fst (add_atom_m s3 k 0) \<and> e = ELit (snd (add_atom_m s3 k 0)) True else s' = s3 \<and> e = ETerm k\<close>
    using 4(2) r1 r2 r3 by (auto simp: Let_def split: if_splits)
  have p4: \<open>pre s3 s'\<close> using res pre_add_atom[OF pre_refl, of s3 k 0] pre_refl by (auto split: if_splits)
  have q3: \<open>pre s3 q\<close> using pre_trans[OF p4 4(10)] .
  have q2: \<open>pre s2 q\<close> using pre_trans[OF p3 q3] .
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 q2] .
  have c3: \<open>cls_true q I s3\<close> using cls_true_pre[OF p4 4(17)] .
  have c2: \<open>cls_true q I s2\<close> using cls_true_pre[OF p3 c3] .
  have c1: \<open>cls_true q I s1\<close> using cls_true_pre[OF p2 c2] .
  have W1: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (SmtFun_args ?sg ! i) (es1 ! i)) \<and> ext q s s1\<close>
    using tr_wb(2)[OF r1 4(3,4) _ ts(2) 4(7,8,9) q1 4(11)] 4(5) by simp
  have A: \<open>\<forall>i < length args. enc_ok I q ru (SmtFun_args ?sg ! i) (?vs ! i) (es1 ! i)\<close>
    using 4(1)[OF r1 4(3,4) _ ts(2) 4(7,8,9) q1 4(11,12,13,14,15,16) c1] 4(5) by simp
  have ew: \<open>\<forall>x \<in> set es1. enc_wf s1 x\<close> using W1 p1(2) by (auto simp: in_set_conv_nth)
  have W2: \<open>st_wf ?nf s2 \<and> (\<forall>t \<in> set ts2. t < length (st_terms s2)) \<and> ext q s1 s2 \<and> pre s1 s2\<close>
    using enc_terms_wb[OF conjunct1[OF W1] ew _ r2' q2 4(11)] by simp
  have E: \<open>\<exists>new. ts2 = [] @ new \<and> length new = length es1 \<and>
      (\<forall>i < length es1. vrel I q ru (SmtFun_args ?sg ! i) (?vs ! i) (tv I q (new ! i)))\<close>
    using enc_terms_sem[where ss=\<open>SmtFun_args ?sg\<close> and vs=\<open>?vs\<close> and ru=ru and I=I, OF conjunct1[OF W1] _ _ _ r2' q2 4(11) c2]
      W1 A p1(2) la by simp
  then have E': \<open>length ts2 = length args\<close> \<open>\<forall>i < length args. vrel I q ru (SmtFun_args ?sg ! i) (?vs ! i) (tv I q (ts2 ! i))\<close>
    using p1(2) by auto
  have J: \<open>if SmtFun_ret ?sg = SmtSort_Bool then J (unat f) ?vs = VBool (I (unat f) (map (tv I q) ts2) = tv I q 0)
      else ru (J (unat f) ?vs) (I (unat f) (map (tv I q) ts2))\<close>
  proof -
    have h: \<open>length ?vs = length (SmtFun_args ?sg) \<and> length (map (tv I q) ts2) = length (SmtFun_args ?sg) \<and>
        (\<forall>i < length (SmtFun_args ?sg). vrel I q ru (SmtFun_args ?sg ! i) (?vs ! i) (map (tv I q) ts2 ! i))\<close>
      using E' la by (simp only: length_map nth_map) simp
    show ?thesis using 4(13)[unfolded jrel_def Let_def, rule_format, OF ts(1) h] .
  qed
  have s3: \<open>s3 = St (st_terms s2 @ [make_Term (word_of_nat (unat f)) (map word_of_nat ts2)]) (st_atoms s2) (st_clauses s2) (st_next s2)\<close>
    \<open>k = length (st_terms s2)\<close> using r3 by (auto simp: add_term_m_def)
  have kb: \<open>k < 2 ^ 64\<close> using pre_len[OF q3] 4(11) s3 by (auto simp: bnd_def)
  have T: \<open>tv I q k = I (unat f) (map (tv I q) ts2)\<close>
    using tv_new[OF q3, of k \<open>unat f\<close> ts2] s3 W2 kb unat_lt2p[of f] by simp
  have ev: \<open>smt_eval J ?dv xs (SmtTerm_Fun f args) = J (unat f) ?vs\<close> by simp
  show ?case
  proof (cases \<open>SmtFun_ret ?sg = SmtSort_Bool\<close>)
    case True
    obtain s4 a where r4: \<open>add_atom_m s3 k 0 = (s4, a)\<close> by (cases \<open>add_atom_m s3 k 0\<close>)
    have se: \<open>s' = s4\<close> \<open>e = ELit a True\<close> using res True r4 by simp_all
    have s4: \<open>s4 = St (st_terms s3) (st_atoms s3 @ [make_Atom (word_of_nat k) (word_of_nat 0)]) (st_clauses s3) (st_next s3)\<close>
      \<open>a = length (st_atoms s3)\<close> using r4 by (auto simp: add_atom_m_def)
    have L: \<open>lv I q a True = (tv I q k = tv I q 0)\<close>
      using lv_new[OF 4(10)[unfolded se], of a k 0 I True] s4 kb by simp
    show ?thesis using L J T ev se ts(3) True by (simp add: enc_ok_def)
  next
    case False
    then show ?thesis using res J T ev ts(3) by (simp add: enc_ok_def)
  qed
next
  case (5 p dm env n s d args s' e ps so xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?dv = \<open>smt_def_sems J (SmtProblem_defs p)\<close>
  have d: \<open>unat d < length (take n ?ds)\<close> \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some (SmtDef_params (?ds ! unat d))\<close>
    \<open>so = SmtDef_ret (?ds ! unat d)\<close> using 5(7) by (auto split: if_splits)
  have dn: \<open>unat d < n\<close> \<open>unat d < length ?ds\<close> using d(1) by auto
  have la: \<open>length args = length (SmtDef_params (?ds ! unat d))\<close> using d(2) by (metis length_map)
  have tb: \<open>smt_tsort ?fs (take (unat d) ?ds) (SmtDef_params (?ds ! unat d)) (SmtDef_body (?ds ! unat d)) = Some (SmtDef_ret (?ds ! unat d))\<close>
    using 5(4) dn(2) by (simp add: smt_wf_def Let_def)
  let ?xs' = \<open>map (smt_eval J ?dv xs) args\<close>
  have v: \<open>smt_eval J ?dv xs (SmtTerm_Def d args) = smt_eval J ?dv ?xs' (SmtDef_body (?ds ! unat d))\<close>
    using smt_def_sems_nth[OF dn(2), of J] tb
      smt_eval_take[of ?fs \<open>unat d\<close> ?ds \<open>SmtDef_params (?ds ! unat d)\<close> \<open>SmtDef_body (?ds ! unat d)\<close> ?dv J ?xs']
    by (simp add: smt_def_sems_length)
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! unat d) = []\<close>)
    case True
    then have a: \<open>args = []\<close> using la by simp
    have \<open>s' = s\<close> \<open>e = dm ! unat d\<close> using 5(3) True by simp_all
    moreover have \<open>(?dv ! unat d) [] = smt_eval J ?dv [] (SmtDef_body (?ds ! unat d))\<close>
      using v a smt_def_sems_nth[OF dn(2), of J] tb
        smt_eval_take[of ?fs \<open>unat d\<close> ?ds \<open>[]\<close> \<open>SmtDef_body (?ds ! unat d)\<close> ?dv J \<open>[]\<close>] True
      by (simp add: smt_def_sems_length)
    ultimately show ?thesis using 5(17)[unfolded dm_sem_def, rule_format, OF dn(1) True] a d(3) by simp
  next
    case False
    obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
    have res: \<open>tr_term_m p dm es1 (unat d) s1 (SmtDef_body (?ds ! unat d)) = (s', e)\<close>
      using 5(3) False dn(1) r1 by (simp add: Let_def)
    have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
    have p2: \<open>pre s1 s'\<close> using tr_pre(1)[OF res] .
    have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 5(11)] .
    have c1: \<open>cls_true q I s1\<close> using cls_true_pre[OF p2 5(18)] .
    have W: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (SmtDef_params (?ds ! unat d) ! i) (es1 ! i)) \<and> ext q s s1\<close>
      using tr_wb(2)[OF r1 5(4,5) _ d(2) 5(8,9,10) q1 5(12)] 5(6) by simp
    have A: \<open>\<forall>i < length args. enc_ok I q ru (SmtDef_params (?ds ! unat d) ! i) (?xs' ! i) (es1 ! i)\<close>
      using 5(1)[OF False dn(1) r1 5(4,5) _ d(2) 5(8,9,10) q1 5(12,13,14,15,16,17) c1] 5(6) by simp
    have env1: \<open>env_ok s1 (SmtDef_params (?ds ! unat d)) es1\<close> using W p1(2) la by (simp add: env_ok_def)
    have es1: \<open>env_sem I q ru (SmtDef_params (?ds ! unat d)) ?xs' es1\<close> using A la by (simp add: env_sem_def)
    have dm1: \<open>dm_ok p s1 (unat d) dm\<close> using dm_ok_pre[OF p1(1) 5(9)] dn(1) by simp
    have dms: \<open>dm_sem p I q ru J (unat d) dm\<close> using 5(17) dn(1) by (simp add: dm_sem_def)
    have nb: \<open>smt_term_no_bv (SmtDef_body (?ds ! unat d))\<close> using 5(5) dn(2) by (simp add: smt_fragment_def)
    have B: \<open>enc_ok I q ru (SmtDef_ret (?ds ! unat d)) (smt_eval J ?dv ?xs' (SmtDef_body (?ds ! unat d))) e\<close>
      using 5(2)[OF False dn(1) r1[symmetric], simplified, OF res 5(4,5) nb tb env1 dm1 conjunct1[OF W] 5(11,12,13,14,15) es1 dms 5(18)] .
    show ?thesis using B v d(3) by simp
  qed
next
  case (6 p dm env n s op args s' e ps so xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?dv = \<open>smt_def_sems J (SmtProblem_defs p)\<close>
  let ?ss = \<open>map (the \<circ> smt_tsort ?fs (take n ?ds) ps) args\<close> and ?vs = \<open>map (smt_eval J ?dv xs) args\<close>
  have o: \<open>None \<notin> set (map (smt_tsort ?fs (take n ?ds) ps) args)\<close> \<open>smt_op_sort op ?ss = Some so\<close>
    using 6(6) by (auto split: if_splits)
  have m: \<open>map (smt_tsort ?fs (take n ?ds) ps) args = map Some ?ss\<close> using o(1) by (induction args) auto
  obtain s1 es1 where r1: \<open>tr_args_m p dm env n s args = (s1, es1)\<close> by (cases \<open>tr_args_m p dm env n s args\<close>)
  have res: \<open>enc_app_m s1 op es1 = (s', e)\<close> using 6(2) r1 by (simp add: Let_def)
  have p1: \<open>pre s s1\<close> \<open>length es1 = length args\<close> using tr_pre(2)[OF r1] by simp_all
  have p2: \<open>pre s1 s'\<close> using pre_enc_app[OF pre_refl, of s1 op es1] res by simp
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2 6(10)] .
  have c1: \<open>cls_true q I s1\<close> using cls_true_pre[OF p2 6(17)] .
  have W: \<open>st_wf ?nf s1 \<and> (\<forall>i < length args. enc_wf s1 (es1 ! i) \<and> shape (?ss ! i) (es1 ! i)) \<and> ext q s s1\<close>
    using tr_wb(2)[OF r1 6(3,4) _ m 6(7,8,9) q1 6(11)] 6(5) by simp
  have A: \<open>\<forall>i < length args. enc_ok I q ru (?ss ! i) (smt_eval J ?dv xs (args ! i)) (es1 ! i)\<close>
    using 6(1)[OF r1 6(3,4) _ m 6(7,8,9) q1 6(11,12,13,14,15,16) c1] 6(5) by simp
  have co: \<open>smt_core_op op\<close> using 6(5) by simp
  have h: \<open>\<forall>i < length es1. enc_wf s1 (es1 ! i) \<and> enc_ok I q ru (?ss ! i) (?vs ! i) (es1 ! i)\<close>
    using W A p1(2) by simp
  have \<open>enc_ok I q ru so (smt_op_sem op ?vs) e\<close>
    using enc_app_sem[OF conjunct1[OF W] co o(2) _ _ h 6(12) res 6(10,11,17)] p1(2) by simp
  then show ?case by simp
next
  case (7 p dm env n s s' es ps ss xs)
  then show ?case by simp
next
  case (8 p dm env n s a rest s' es ps ss xs)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  obtain s1 e1 where r1: \<open>tr_term_m p dm env n s a = (s1, e1)\<close> by (cases \<open>tr_term_m p dm env n s a\<close>)
  obtain s2 es2 where r2: \<open>tr_args_m p dm env n s1 rest = (s2, es2)\<close> by (cases \<open>tr_args_m p dm env n s1 rest\<close>)
  have res: \<open>s' = s2\<close> \<open>es = e1 # es2\<close> using 8(3) r1 r2 by (simp_all add: Let_def)
  obtain s0 ss' where ss: \<open>ss = s0 # ss'\<close> \<open>smt_tsort ?fs (take n ?ds) ps a = Some s0\<close>
    \<open>map (smt_tsort ?fs (take n ?ds) ps) rest = map Some ss'\<close> using 8(7) by (cases ss) auto
  have p1: \<open>pre s s1\<close> using tr_pre(1)[OF r1] .
  have p2: \<open>pre s1 s2\<close> using tr_pre(2)[OF r2] by simp
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p2] 8(11) res by simp
  have c1: \<open>cls_true q I s1\<close> using cls_true_pre[OF p2] 8(18) res by simp
  have W: \<open>st_wf ?nf s1 \<and> enc_wf s1 e1 \<and> shape s0 e1 \<and> ext q s s1\<close>
    using tr_wb(1)[OF r1 8(4,5) _ ss(2) 8(8,9,10) q1 8(12)] 8(6) by simp
  have A: \<open>enc_ok I q ru s0 (smt_eval J (smt_def_sems J ?ds) xs a) e1\<close>
    using 8(1)[OF r1 8(4,5) _ ss(2) 8(8,9,10) q1 8(12,13,14,15,16,17) c1] 8(6) by simp
  have B: \<open>\<forall>i < length rest. enc_ok I q ru (ss' ! i) (smt_eval J (smt_def_sems J ?ds) xs (rest ! i)) (es2 ! i)\<close>
    using 8(2)[OF r1[symmetric], simplified, OF r2 8(4,5) _ ss(3) env_ok_pre[OF p1 8(8)] dm_ok_pre[OF p1 8(9) order_refl]
        conjunct1[OF W] _ 8(12,13,14,15,16,17)] 8(6) 8(11,18) res by simp
  show ?case using A B res ss(1) by (auto simp: nth_Cons split: nat.splits)
qed

section \<open>The translation of a problem\<close>

subsection \<open>Agreement\<close>

lemma enc_ok_agree:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close> \<open>enc_wf s e\<close>
  shows \<open>enc_ok I' q ru so v e = enc_ok I q ru so v e\<close>
  using assms tv_agree[OF assms(1,2,3)] lv_agree[OF assms(1,2,3)] by (cases e) (simp_all add: enc_ok_def enc_wf_def)

lemma dm_sem_agree:
  assumes \<open>st_wf nf s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close> \<open>dm_ok p s n dm\<close>
  shows \<open>dm_sem p I' q ru J n dm = dm_sem p I q ru J n dm\<close>
  using assms(4) enc_ok_agree[OF assms(1,2,3)] unfolding dm_sem_def dm_ok_def by auto

lemma jrel_agree:
  assumes \<open>st_wf (length (SmtProblem_funs p)) s\<close> \<open>pre s q\<close> \<open>agree (st_next s) I I'\<close>
  shows \<open>jrel p I' q ru J = jrel p I q ru J\<close>
proof -
  have l2: \<open>0 < length (st_terms s)\<close> \<open>1 < length (st_terms s)\<close> using assms(1) by (auto simp: st_wf_def)
  have t: \<open>tv I' q 0 = tv I q 0\<close> \<open>tv I' q 1 = tv I q 1\<close> using tv_agree[OF assms] l2 by simp_all
  have f: \<open>f < length (SmtProblem_funs p) \<Longrightarrow> I' f = I f\<close> for f
    using assms(1,3) by (auto simp: st_wf_def agree_def)
  show ?thesis unfolding jrel_def vrel_def using t f by (simp cong: conj_cong)
qed

lemma lv0: \<open>st_atoms q ! 0 = make_Atom 0 0 \<Longrightarrow> lv I q 0 True\<close>
  by (simp add: lv_def)

subsection \<open>The assertions\<close>

lemma pre_asserts: \<open>pre s (foldl (tr_asserts_step p dm) s ts)\<close>
proof (induction ts arbitrary: s)
  case Nil
  then show ?case by (simp add: pre_refl)
next
  case (Cons t ts)
  obtain s1 e where r: \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) s t = (s1, e)\<close>
    by (cases \<open>tr_term_m p dm [] (length (SmtProblem_defs p)) s t\<close>)
  have \<open>tr_asserts_step p dm s t = add_clause_m s1 [lit_m (fst (enc_lit_m e)) (snd (enc_lit_m e))]\<close>
    using r by (simp add: tr_asserts_step_def Let_def)
  then have \<open>pre s (tr_asserts_step p dm s t)\<close> using pre_add_clause[OF tr_pre(1)[OF r]] by simp
  then show ?case using pre_trans[OF _ Cons.IH] by simp
qed

lemma asserts_inv:
  fixes q :: st
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close>
    \<open>\<forall>t \<in> set ts. smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] t = Some SmtSort_Bool \<and> smt_term_no_bv t\<close>
    \<open>st_wf (length (SmtProblem_funs p)) s\<close> \<open>dm_ok p s (length (SmtProblem_defs p)) dm\<close>
    \<open>foldl (tr_asserts_step p dm) s ts = s'\<close> \<open>pre s' q\<close> \<open>bnd q\<close> \<open>st_atoms q ! 0 = make_Atom 0 0\<close>
  shows \<open>st_wf (length (SmtProblem_funs p)) s' \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I q ru J \<and> dm_sem p I q ru J (length (SmtProblem_defs p)) dm \<and>
       cls_true q I s' \<longrightarrow> (\<forall>t \<in> set ts. smt_eval J (smt_def_sems J (SmtProblem_defs p)) [] t = VBool True)) \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. base q I \<and> cls_true q I s \<and> ru_ok ru \<and> jrel p I q ru J \<and>
       dm_sem p I q ru J (length (SmtProblem_defs p)) dm \<and>
       (\<forall>t \<in> set ts. smt_eval J (smt_def_sems J (SmtProblem_defs p)) [] t = VBool True) \<longrightarrow>
       (\<exists>I'. agree (st_next s) I I' \<and> base q I' \<and> cls_true q I' s'))\<close>
  using assms(3-7)
proof (induction ts arbitrary: s)
  case Nil
  then show ?case by (auto simp: agree_def)
next
  case (Cons t ts)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?dv = \<open>\<lambda>J. smt_def_sems J (SmtProblem_defs p)\<close>
  obtain s1 e where r: \<open>tr_term_m p dm [] (length ?ds) s t = (s1, e)\<close> by (cases \<open>tr_term_m p dm [] (length ?ds) s t\<close>)
  let ?s2 = \<open>add_clause_m s1 [lit_m (fst (enc_lit_m e)) (snd (enc_lit_m e))]\<close>
  have st: \<open>tr_asserts_step p dm s t = ?s2\<close> using r by (simp add: tr_asserts_step_def Let_def)
  have f: \<open>foldl (tr_asserts_step p dm) ?s2 ts = s'\<close> using Cons.prems(4) st by simp
  have p1: \<open>pre s s1\<close> using tr_pre(1)[OF r] .
  have p12: \<open>pre s1 ?s2\<close> using pre_add_clause[OF pre_refl] .
  have p2: \<open>pre ?s2 s'\<close> using pre_asserts[of ?s2 p dm ts] f by simp
  have q2: \<open>pre ?s2 q\<close> using pre_trans[OF p2 Cons.prems(5)] .
  have q1: \<open>pre s1 q\<close> using pre_trans[OF p12 q2] .
  have tt: \<open>smt_tsort ?fs (take (length ?ds) ?ds) [] t = Some SmtSort_Bool\<close> \<open>smt_term_no_bv t\<close> using Cons.prems(1) by simp_all
  have env: \<open>env_ok s [] []\<close> by (simp add: env_ok_def)
  have W: \<open>st_wf ?nf s1 \<and> enc_wf s1 e \<and> shape SmtSort_Bool e \<and> ext q s s1\<close>
    using tr_wb(1)[OF r assms(1,2) tt(2) tt(1) env Cons.prems(3,2) q1 assms(8)] .
  then obtain a pos where e: \<open>e = ELit a pos\<close> by (cases e) (auto simp: shape_def)
  have a: \<open>a < length (st_atoms s1)\<close> using W e by (simp add: enc_wf_def)
  have ab: \<open>a < 2 ^ 64\<close> using a pre_len[OF q1] assms(8) by (simp add: bnd_def)
  have s2: \<open>?s2 = St (st_terms s1 @ []) (st_atoms s1 @ []) (st_clauses s1 @ [make_Clause [lit_m a pos]]) (st_next s1)\<close>
    using e by (simp add: add_clause_m_def)
  have w2: \<open>st_wf ?nf ?s2\<close>
    using wf_extend[OF conjunct1[OF W] s2] W a ab by (simp add: lit_m_def unat_wn) (auto simp: st_wf_def)
  have dm1: \<open>dm_ok p ?s2 (length ?ds) dm\<close> using dm_ok_pre[OF pre_trans[OF p1 p12] Cons.prems(3) order_refl] .
  have ts: \<open>\<forall>t \<in> set ts. smt_tsort ?fs ?ds [] t = Some SmtSort_Bool \<and> smt_term_no_bv t\<close> using Cons.prems(1) by simp
  note IH = Cons.IH[OF ts w2 dm1 f Cons.prems(5)]
  have S: \<open>lv I q a pos = (smt_eval J (?dv J) [] t = VBool True)\<close>
    if h: \<open>ru_ok ru\<close> \<open>jrel p I q ru J\<close> \<open>dm_sem p I q ru J (length ?ds) dm\<close> \<open>cls_true q I s1\<close> for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
  proof -
    have es: \<open>env_sem I q ru [] [] []\<close> by (simp add: env_sem_def)
    have \<open>enc_ok I q ru SmtSort_Bool (smt_eval J (?dv J) [] t) e\<close>
      using tr_sem(1)[OF r assms(1,2) tt(2) tt(1) env Cons.prems(3,2) q1 assms(8) h(1,2) lv0[OF assms(9)] es h(3,4)] .
    then show ?thesis using e by (simp add: enc_ok_def)
  qed
  have U: \<open>cls_true q I ?s2 = (cls_true q I s1 \<and> lv I q a pos)\<close> for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close>
    using e ab by (auto simp: cls_true_def add_clause_m_def clause_true_mk lit_true_m)
  show ?case
  proof (intro conjI allI impI)
    show \<open>st_wf ?nf s'\<close> using IH by blast
  next
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
    assume h: \<open>ru_ok ru \<and> jrel p I q ru J \<and> dm_sem p I q ru J (length ?ds) dm \<and> cls_true q I s'\<close>
    have c2: \<open>cls_true q I ?s2\<close> using cls_true_pre[OF p2] h by blast
    then have \<open>smt_eval J (?dv J) [] t = VBool True\<close> using S[of ru I J] h U by blast
    moreover have \<open>\<forall>t \<in> set ts. smt_eval J (?dv J) [] t = VBool True\<close>
      using conjunct1[OF conjunct2[OF IH], rule_format, where I=I and ru=ru and J=J] h by simp
    ultimately show \<open>\<forall>t \<in> set (t # ts). smt_eval J (?dv J) [] t = VBool True\<close> by simp
  next
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
    assume h: \<open>base q I \<and> cls_true q I s \<and> ru_ok ru \<and> jrel p I q ru J \<and> dm_sem p I q ru J (length ?ds) dm \<and>
       (\<forall>t \<in> set (t # ts). smt_eval J (?dv J) [] t = VBool True)\<close>
    obtain I1 where I1: \<open>agree (st_next s) I I1\<close> \<open>base q I1\<close> \<open>cls_true q I1 s1\<close> using W h unfolding ext_def by blast
    have sq: \<open>pre s q\<close> using pre_trans[OF p1 q1] .
    have j1: \<open>jrel p I1 q ru J\<close> using jrel_agree[OF Cons.prems(2) sq I1(1)] h by simp
    have d1: \<open>dm_sem p I1 q ru J (length ?ds) dm\<close> using dm_sem_agree[OF Cons.prems(2) sq I1(1) Cons.prems(3)] h by simp
    have \<open>lv I1 q a pos\<close> using S[OF _ j1 d1 I1(3)] h by simp
    then have c2: \<open>cls_true q I1 ?s2\<close> using U I1(3) by simp
    have \<open>\<exists>I'. agree (st_next ?s2) I1 I' \<and> base q I' \<and> cls_true q I' s'\<close>
      using conjunct2[OF conjunct2[OF IH], rule_format, where I=I1 and ru=ru and J=J] I1(2) c2 h j1 d1 by simp
    then obtain I' where I': \<open>agree (st_next ?s2) I1 I'\<close> \<open>base q I'\<close> \<open>cls_true q I' s'\<close> by blast
    have \<open>st_next s \<le> st_next ?s2\<close> using pre_len[OF pre_trans[OF p1 p12]] by simp
    then have \<open>agree (st_next s) I I'\<close> using I1(1) I'(1) by (auto simp: agree_def)
    then show \<open>\<exists>I'. agree (st_next s) I I' \<and> base q I' \<and> cls_true q I' s'\<close> using I' by blast
  qed
qed

subsection \<open>The definitions\<close>

lemma defs_inv:
  fixes q :: st
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>k \<le> length (SmtProblem_defs p)\<close>
    \<open>foldl (tr_defs_step p) (tr_init_m p, []) [0..<k] = (s, dm)\<close> \<open>pre s q\<close> \<open>bnd q\<close>
    \<open>st_atoms q ! 0 = make_Atom 0 0\<close> \<open>st_wf (length (SmtProblem_funs p)) (tr_init_m p)\<close>
  shows \<open>st_wf (length (SmtProblem_funs p)) s \<and> dm_ok p s k dm \<and> length dm = k \<and> ext q (tr_init_m p) s \<and>
    pre (tr_init_m p) s \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I q ru J \<and> cls_true q I s \<longrightarrow> dm_sem p I q ru J k dm)\<close>
  using assms(3,4,5)
proof (induction k arbitrary: s dm)
  case 0
  then show ?case using assms(8) by (auto simp: dm_ok_def dm_sem_def ext_refl pre_refl)
next
  case (Suc k)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  obtain s0 dm0 where f0: \<open>foldl (tr_defs_step p) (tr_init_m p, []) [0..<k] = (s0, dm0)\<close>
    by (cases \<open>foldl (tr_defs_step p) (tr_init_m p, []) [0..<k]\<close>)
  have st: \<open>tr_defs_step p (s0, dm0) k = (s, dm)\<close> using Suc.prems(2) f0 by simp
  have kd: \<open>k < length ?ds\<close> using Suc.prems(1) by simp
  show ?case
  proof (cases \<open>SmtDef_params (?ds ! k) = []\<close>)
    case True
    obtain s1 e where r: \<open>tr_term_m p dm0 [] k s0 (SmtDef_body (?ds ! k)) = (s1, e)\<close>
      by (cases \<open>tr_term_m p dm0 [] k s0 (SmtDef_body (?ds ! k))\<close>)
    have se: \<open>s = s1\<close> \<open>dm = dm0 @ [e]\<close> using st True r by (simp_all add: tr_defs_step_def)
    have p1: \<open>pre s0 s1\<close> using tr_pre(1)[OF r] .
    have q0: \<open>pre s0 q\<close> using pre_trans[OF p1] Suc.prems(3) se by simp
    have IH: \<open>st_wf ?nf s0 \<and> dm_ok p s0 k dm0 \<and> length dm0 = k \<and> ext q (tr_init_m p) s0 \<and> pre (tr_init_m p) s0 \<and>
      (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I q ru J \<and> cls_true q I s0 \<longrightarrow> dm_sem p I q ru J k dm0)\<close>
      using Suc.IH[OF _ f0 q0] kd by simp
    have tb0: \<open>smt_tsort ?fs (take k ?ds) (SmtDef_params (?ds ! k)) (SmtDef_body (?ds ! k)) = Some (SmtDef_ret (?ds ! k))\<close>
      using assms(1) kd by (simp add: smt_wf_def Let_def)
    then have tb: \<open>smt_tsort ?fs (take k ?ds) [] (SmtDef_body (?ds ! k)) = Some (SmtDef_ret (?ds ! k))\<close>
      using True by simp
    have nb: \<open>smt_term_no_bv (SmtDef_body (?ds ! k))\<close> using assms(2) kd by (simp add: smt_fragment_def)
    have env: \<open>env_ok s0 [] []\<close> by (simp add: env_ok_def)
    have q1: \<open>pre s1 q\<close> using Suc.prems(3) se by simp
    have W: \<open>st_wf ?nf s1 \<and> enc_wf s1 e \<and> shape (SmtDef_ret (?ds ! k)) e \<and> ext q s0 s1\<close>
      using tr_wb(1)[OF r assms(1,2) nb tb env _ _ q1 assms(6)] IH by simp
    have dmo: \<open>dm_ok p s1 (Suc k) (dm0 @ [e])\<close>
      using dm_ok_pre[OF p1, of p k dm0 k] IH W kd True by (auto simp: dm_ok_def nth_append less_Suc_eq)
    have nx: \<open>st_next (tr_init_m p) \<le> st_next s0\<close> using IH pre_len by blast
    have dv: \<open>(smt_def_sems J ?ds ! k) [] = smt_eval J (smt_def_sems J ?ds) [] (SmtDef_body (?ds ! k))\<close> for J
      using smt_def_sems_nth[OF kd, of J] tb smt_eval_take[of ?fs k ?ds \<open>[]\<close> \<open>SmtDef_body (?ds ! k)\<close> \<open>smt_def_sems J ?ds\<close> J \<open>[]\<close>]
      by (simp add: smt_def_sems_length)
    have S: \<open>dm_sem p I q ru J (Suc k) (dm0 @ [e])\<close>
      if h: \<open>ru_ok ru\<close> \<open>jrel p I q ru J\<close> \<open>cls_true q I s1\<close> for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
    proof -
      have d0: \<open>dm_sem p I q ru J k dm0\<close> using IH h cls_true_pre[OF p1 h(3)] by blast
      have es: \<open>env_sem I q ru [] [] []\<close> by (simp add: env_sem_def)
      have \<open>enc_ok I q ru (SmtDef_ret (?ds ! k)) (smt_eval J (smt_def_sems J ?ds) [] (SmtDef_body (?ds ! k))) e\<close>
        using tr_sem(1)[OF r assms(1,2) nb tb env _ _ q1 assms(6) h(1,2) lv0[OF assms(7)] es d0 h(3)] IH by simp
      then show ?thesis using d0 IH dv by (auto simp: dm_sem_def nth_append less_Suc_eq)
    qed
    show ?thesis using W IH se dmo ext_trans[OF _ _ nx] S pre_trans[OF _ p1] by auto
  next
    case False
    have se: \<open>s = s0\<close> \<open>dm = dm0 @ [ELit 0 True]\<close> using st False by (simp_all add: tr_defs_step_def)
    have IH: \<open>st_wf ?nf s0 \<and> dm_ok p s0 k dm0 \<and> length dm0 = k \<and> ext q (tr_init_m p) s0 \<and> pre (tr_init_m p) s0 \<and>
      (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I q ru J \<and> cls_true q I s0 \<longrightarrow> dm_sem p I q ru J k dm0)\<close>
      using Suc.IH[OF _ f0] Suc.prems(3) se kd by simp
    have dmo: \<open>dm_ok p s0 (Suc k) (dm0 @ [ELit 0 True])\<close>
      using IH kd False by (auto simp: dm_ok_def nth_append less_Suc_eq enc_wf_def st_wf_def)
    have S: \<open>dm_sem p I q ru J k dm0 \<Longrightarrow> dm_sem p I q ru J (Suc k) (dm0 @ [ELit 0 True])\<close> for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
      using IH False by (auto simp: dm_sem_def nth_append less_Suc_eq)
    show ?thesis using IH se dmo S by auto
  qed
qed

subsection \<open>The whole translation\<close>

lemma init_eq:
  \<open>tr_init_m p = St [make_Term (word_of_nat (length (SmtProblem_funs p))) [], make_Term (word_of_nat (length (SmtProblem_funs p) + 1)) []]
      [make_Atom 0 0, make_Atom 0 1] [make_Clause [lit_m 1 False]] (length (SmtProblem_funs p) + 2)\<close>
  by (simp add: tr_init_m_def add_term_m_def add_atom_m_def add_clause_m_def Let_def)

lemma pre_defs: \<open>pre (fst sdm) (fst (foldl (tr_defs_step p) sdm ks))\<close>
proof (induction ks arbitrary: sdm)
  case Nil
  then show ?case by (simp add: pre_refl)
next
  case (Cons k ks)
  obtain s dm where sdm: \<open>sdm = (s, dm)\<close> by (cases sdm)
  have \<open>pre s (fst (tr_defs_step p (s, dm) k))\<close>
  proof (cases \<open>SmtDef_params (SmtProblem_defs p ! k) = []\<close>)
    case True
    obtain s1 e where r: \<open>tr_term_m p dm [] k s (SmtDef_body (SmtProblem_defs p ! k)) = (s1, e)\<close>
      by (cases \<open>tr_term_m p dm [] k s (SmtDef_body (SmtProblem_defs p ! k))\<close>)
    then show ?thesis using True tr_pre(1)[OF r] by (simp add: tr_defs_step_def)
  next
    case False
    then show ?thesis by (simp add: tr_defs_step_def pre_refl)
  qed
  then show ?case using Cons.IH[of \<open>tr_defs_step p (s, dm) k\<close>] sdm pre_trans by simp
qed

text \<open>The translation does not overflow: the next unused function symbol, the number of terms
  and the number of atoms stay below \<open>2^64\<close>.\<close>
definition tr_bounded :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>tr_bounded p \<equiv> length (SmtProblem_funs p) + length (Problem_terms (tr_problem_m p)) < 2 ^ 64 \<and>
     length (Problem_atoms (tr_problem_m p)) < 2 ^ 64\<close>

lemma tr_main:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>tr_bounded p\<close>
  shows \<open>st_wf (length (SmtProblem_funs p)) (tr_state_m p)\<close>
    and \<open>pre (tr_init_m p) (tr_state_m p)\<close> and \<open>bnd (tr_state_m p)\<close>
    and \<open>\<And>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<Longrightarrow> jrel p I (tr_state_m p) ru J \<Longrightarrow>
           cls_true (tr_state_m p) I (tr_state_m p) \<Longrightarrow> smt_satisfies p J\<close>
    and \<open>\<And>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. base (tr_state_m p) I \<Longrightarrow> cls_true (tr_state_m p) I (tr_init_m p) \<Longrightarrow>
           ru_ok ru \<Longrightarrow> jrel p I (tr_state_m p) ru J \<Longrightarrow> smt_satisfies p J \<Longrightarrow>
           \<exists>I'. agree (st_next (tr_init_m p)) I I' \<and> cls_true (tr_state_m p) I' (tr_state_m p)\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?ds = \<open>SmtProblem_defs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?q = \<open>tr_state_m p\<close> and ?i = \<open>tr_init_m p\<close>
  obtain sd dm where D: \<open>tr_defs_m p = (sd, dm)\<close> by (cases \<open>tr_defs_m p\<close>)
  have D': \<open>foldl (tr_defs_step p) (?i, []) [0..<length ?ds] = (sd, dm)\<close> using D by (simp add: tr_defs_m_def)
  have A: \<open>foldl (tr_asserts_step p dm) sd (SmtProblem_asserts p) = ?q\<close>
    using D by (simp add: tr_state_m_def tr_asserts_m_def)
  have pid: \<open>pre ?i sd\<close> using pre_defs[of \<open>(?i, [])\<close> p \<open>[0..<length ?ds]\<close>] D' by simp
  have pdq: \<open>pre sd ?q\<close> using pre_asserts[of sd p dm \<open>SmtProblem_asserts p\<close>] A by simp
  show piq: \<open>pre ?i ?q\<close> using pre_trans[OF pid pdq] .
  have tp: \<open>tr_problem_m p = st_prob ?q\<close> by (simp add: tr_problem_m_def st_prob_def Let_def)
  have nx: \<open>st_next ?q \<le> ?nf + length (st_terms ?q)\<close> using piq by (simp add: pre_def init_eq)
  show bq: \<open>bnd ?q\<close> using assms(3) nx by (simp add: tr_bounded_def tp st_prob_def bnd_def)
  have b2: \<open>?nf + 2 < 2 ^ 64\<close> using pre_len[OF piq] bq by (simp add: bnd_def init_eq)
  have u1: \<open>unat (1 + word_of_nat ?nf :: 64 word) = Suc ?nf\<close> using unat_wn[of \<open>Suc ?nf\<close>] b2 by simp
  have wi: \<open>st_wf ?nf ?i\<close> using b2 u1 by (simp add: init_eq st_wf_def unat_wn lit_m_def less_Suc_eq)
  have a0: \<open>st_atoms ?q ! 0 = make_Atom 0 0\<close> using pre_nth_atoms[OF piq, of 0] by (simp add: init_eq)
  have DI: \<open>st_wf ?nf sd \<and> dm_ok p sd (length ?ds) dm \<and> length dm = length ?ds \<and> ext ?q ?i sd \<and> pre ?i sd \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I ?q ru J \<and> cls_true ?q I sd \<longrightarrow> dm_sem p I ?q ru J (length ?ds) dm)\<close>
    using defs_inv[OF assms(1,2) order_refl D' pdq bq a0 wi] .
  have tas: \<open>\<forall>t \<in> set (SmtProblem_asserts p). smt_tsort ?fs ?ds [] t = Some SmtSort_Bool \<and> smt_term_no_bv t\<close>
    using assms(1,2) by (simp add: smt_wf_def smt_fragment_def Let_def)
  have AI: \<open>st_wf ?nf ?q \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. ru_ok ru \<and> jrel p I ?q ru J \<and> dm_sem p I ?q ru J (length ?ds) dm \<and>
       cls_true ?q I ?q \<longrightarrow> (\<forall>t \<in> set (SmtProblem_asserts p). smt_eval J (smt_def_sems J ?ds) [] t = VBool True)) \<and>
    (\<forall>(I :: nat \<Rightarrow> nat list \<Rightarrow> nat) ru J. base ?q I \<and> cls_true ?q I sd \<and> ru_ok ru \<and> jrel p I ?q ru J \<and>
       dm_sem p I ?q ru J (length ?ds) dm \<and>
       (\<forall>t \<in> set (SmtProblem_asserts p). smt_eval J (smt_def_sems J ?ds) [] t = VBool True) \<longrightarrow>
       (\<exists>I'. agree (st_next sd) I I' \<and> base ?q I' \<and> cls_true ?q I' ?q))\<close>
    using asserts_inv[OF assms(1,2) tas _ _ A pre_refl bq a0] DI by blast
  show \<open>st_wf ?nf ?q\<close> using AI by blast
  show \<open>smt_satisfies p J\<close> if h: \<open>ru_ok ru\<close> \<open>jrel p I ?q ru J\<close> \<open>cls_true ?q I ?q\<close> for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
  proof -
    have \<open>dm_sem p I ?q ru J (length ?ds) dm\<close> using DI h cls_true_pre[OF pdq h(3)] by blast
    then show ?thesis using AI h by (simp add: smt_satisfies_def)
  qed
  show \<open>\<exists>I'. agree (st_next ?i) I I' \<and> cls_true ?q I' ?q\<close>
    if h: \<open>base ?q I\<close> \<open>cls_true ?q I ?i\<close> \<open>ru_ok ru\<close> \<open>jrel p I ?q ru J\<close> \<open>smt_satisfies p J\<close>
    for I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> and ru J
  proof -
    obtain I1 where I1: \<open>agree (st_next ?i) I I1\<close> \<open>base ?q I1\<close> \<open>cls_true ?q I1 sd\<close>
      using DI h(1,2) unfolding ext_def by blast
    have j1: \<open>jrel p I1 ?q ru J\<close> using jrel_agree[OF wi piq I1(1)] h(4) by simp
    have d1: \<open>dm_sem p I1 ?q ru J (length ?ds) dm\<close> using DI h(3) j1 I1(3) by blast
    have sa: \<open>\<forall>t \<in> set (SmtProblem_asserts p). smt_eval J (smt_def_sems J ?ds) [] t = VBool True\<close>
      using h(5) by (simp add: smt_satisfies_def)
    have \<open>\<exists>I'. agree (st_next sd) I1 I' \<and> base ?q I' \<and> cls_true ?q I' ?q\<close>
      using AI I1(2,3) h(3) j1 d1 sa by blast
    then obtain I' where I': \<open>agree (st_next sd) I1 I'\<close> \<open>cls_true ?q I' ?q\<close> by blast
    have \<open>st_next ?i \<le> st_next sd\<close> using pre_len[OF pid] by simp
    then have \<open>agree (st_next ?i) I I'\<close> using I1(1) I'(1) by (auto simp: agree_def)
    then show ?thesis using I'(2) by blast
  qed
qed

lemma problem_true_cls: \<open>problem_true I (tr_problem_m p) = cls_true (tr_state_m p) I (tr_state_m p)\<close>
  by (simp add: problem_true_def cls_true_def tr_problem_m_def st_prob_def Let_def)

theorem tr_wf_problem:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>tr_bounded p\<close>
  shows \<open>wf_problem (tr_problem_m p)\<close>
  using tr_main(1)[OF assms] by (simp add: wf_problem_def st_wf_def tr_problem_m_def Let_def)

lemma tv01:
  assumes \<open>pre (tr_init_m p) q\<close> \<open>bnd q\<close>
  shows \<open>tv I q 0 = I (length (SmtProblem_funs p)) []\<close> \<open>tv I q 1 = I (length (SmtProblem_funs p) + 1) []\<close>
proof -
  let ?nf = \<open>length (SmtProblem_funs p)\<close>
  have b: \<open>?nf + 2 < 2 ^ 64\<close> using pre_len[OF assms(1)] assms(2) by (simp add: bnd_def init_eq)
  show \<open>tv I q 0 = I ?nf []\<close>
    using tv_new[OF assms(1), of 0 ?nf \<open>[]\<close> I] b by (simp add: init_eq)
  show \<open>tv I q 1 = I (?nf + 1) []\<close>
    using tv_new[OF assms(1), of 1 \<open>?nf + 1\<close> \<open>[]\<close> I] b by (simp add: init_eq)
qed

lemma cls_init:
  assumes \<open>pre (tr_init_m p) q\<close> \<open>bnd q\<close>
  shows \<open>cls_true q I (tr_init_m p) = (tv I q 0 \<noteq> tv I q 1)\<close>
proof -
  have \<open>lv I q 1 False = (tv I q 0 \<noteq> tv I q 1)\<close>
    using lv_new[OF assms(1), of 1 0 1 I False] by (simp add: init_eq)
  then show ?thesis by (simp add: cls_true_def init_eq clause_true_mk lit_true_m)
qed

subsection \<open>Completeness: a model of \<open>p\<close> gives a model of the translation\<close>

text \<open>The elements of the translation for the values of \<open>p\<close>: true and false are 0 and 1, the
  element \<open>e\<close> of an uninterpreted sort is \<open>e + 2\<close>.\<close>
fun encv :: \<open>sval \<Rightarrow> nat\<close> where
  \<open>encv (VBool b) = (if b then 0 else 1)\<close>
| \<open>encv (VElem e) = e + 2\<close>
| \<open>encv (VBv w x) = 0\<close>

definition decv :: \<open>SmtSort \<Rightarrow> nat \<Rightarrow> sval\<close> where
  \<open>decv srt d \<equiv>
     (case srt of
        SmtSort_Bool \<Rightarrow> (VBool (d = 0))
      | _ \<Rightarrow> (VElem (d - 2)))\<close>

lemma decv_simps [simp]:
  \<open>decv SmtSort_Bool d = VBool (d = 0)\<close>
  \<open>decv (SmtSort_BitVec a0) d = VElem (d - 2)\<close>
  \<open>decv (SmtSort_Uninterpreted a0) d = VElem (d - 2)\<close>
  by (simp_all add: decv_def)

text \<open>The interpretation of the declared symbols, TRUE and FALSE for an interpretation \<open>J\<close> of \<open>p\<close>.\<close>
definition interp_of :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where
  \<open>interp_of p J f ds \<equiv>
     if f < length (SmtProblem_funs p)
     then encv (J f (map (\<lambda>(s, d). decv s d) (zip (SmtFun_args (SmtProblem_funs p ! f)) ds)))
     else if f = length (SmtProblem_funs p) then 0 else 1\<close>

theorem tr_complete:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>tr_bounded p\<close> \<open>smt_satisfiable p\<close>
  shows \<open>satisfiable (tr_problem_m p)\<close>
proof -
  obtain J where J: \<open>smt_interp_ok p J\<close> \<open>smt_satisfies p J\<close> using assms(4) by (auto simp: smt_satisfiable_def)
  let ?fs = \<open>SmtProblem_funs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close>
  let ?I = \<open>interp_of p J\<close> and ?ru = \<open>\<lambda>v d. \<exists>e. v = VElem e \<and> d = e + 2\<close> and ?q = \<open>tr_state_m p\<close>
  note M = tr_main[OF assms(1,2,3)]
  have t0: \<open>tv ?I ?q 0 = 0\<close> \<open>tv ?I ?q 1 = 1\<close> using tv01[OF M(2,3), of ?I] by (simp_all add: interp_of_def)
  have bI: \<open>base ?q ?I\<close> using t0 by (simp add: base_def)
  have cI: \<open>cls_true ?q ?I (tr_init_m p)\<close> using cls_init[OF M(2,3), of ?I] t0 by simp
  have ru: \<open>ru_ok ?ru\<close> by (auto simp: ru_ok_def)
  have fr: \<open>\<forall>f < ?nf. (\<forall>x \<in> set (SmtFun_args (?fs ! f)). smt_sort_no_bv x) \<and> smt_sort_no_bv (SmtFun_ret (?fs ! f))\<close>
    using assms(2) nth_mem unfolding smt_fragment_def by blast
  have jr: \<open>jrel p ?I ?q ?ru J\<close>
    unfolding jrel_def Let_def
  proof (intro allI impI)
    fix f vs ds
    assume f: \<open>f < ?nf\<close>
    let ?sa = \<open>SmtFun_args (?fs ! f)\<close> and ?r = \<open>SmtFun_ret (?fs ! f)\<close>
    assume h: \<open>length vs = length ?sa \<and> length ds = length ?sa \<and> (\<forall>i < length ?sa. vrel ?I ?q ?ru (?sa ! i) (vs ! i) (ds ! i))\<close>
    have nb: \<open>\<forall>i < length ?sa. smt_sort_no_bv (?sa ! i)\<close> using fr f by simp
    have el: \<open>decv (?sa ! i) (ds ! i) = vs ! i \<and> smt_has_sort (?sa ! i) (vs ! i)\<close> if i: \<open>i < length ?sa\<close> for i
      using h[THEN conjunct2, THEN conjunct2, rule_format, OF i] nb[rule_format, OF i] t0
      by (cases \<open>?sa ! i\<close>) (auto simp: vrel_def)
    have dv: \<open>map (\<lambda>(s, d). decv s d) (zip ?sa ds) = vs\<close>
      using el h by (intro nth_equalityI) auto
    have la: \<open>list_all2 smt_has_sort ?sa vs\<close> using el h by (simp add: list_all2_conv_all_nth)
    have hs: \<open>smt_has_sort ?r (J f vs)\<close> using J(1) f la by (simp add: smt_interp_ok_def)
    have Iv: \<open>?I f ds = encv (J f vs)\<close> using f dv by (simp add: interp_of_def)
    show \<open>if ?r = SmtSort_Bool then J f vs = VBool (?I f ds = tv ?I ?q 0) else ?ru (J f vs) (?I f ds)\<close>
      using hs Iv t0 fr f by (cases ?r; cases \<open>J f vs\<close>) auto
  qed
  obtain I' :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where \<open>cls_true ?q I' ?q\<close> using M(5)[OF bI cI ru jr J(2)] by blast
  then show ?thesis using problem_true_cls[of I' p] by (auto simp: satisfiable_def)
qed

subsection \<open>Soundness: a model of the translation gives a model of \<open>p\<close>\<close>

lemma find_map_filter:
  assumes \<open>\<forall>x \<in> set xs. P x \<longrightarrow> F x\<close> \<open>\<forall>x \<in> set xs. F x \<longrightarrow> Q (g x) = P x\<close>
  shows \<open>List.find Q (map g (filter F xs)) = map_option g (List.find P xs)\<close>
  using assms by (induction xs) auto

lemma const_value_interp: \<open>const_value_m m f = model_interp m f []\<close>
  by (simp add: const_value_m_def model_interp_def)

lemma model_interp_lt: \<open>model_interp m f ds < 2 ^ 64\<close>
  by (auto simp: model_interp_def split: option.splits intro: unat_lt2p[THEN less_le_trans])

lemma tr_interp_val:
  assumes \<open>t \<noteq> u\<close> \<open>f < length (SmtProblem_funs p)\<close>
    \<open>length ds = length (SmtFun_args (SmtProblem_funs p ! f))\<close> \<open>length vs = length (SmtFun_args (SmtProblem_funs p ! f))\<close>
    \<open>\<forall>k < length (SmtFun_args (SmtProblem_funs p ! f)). if SmtFun_args (SmtProblem_funs p ! f) ! k = SmtSort_Bool
       then (\<exists>b. vs ! k = VBool b \<and> ds ! k = (if b then t else u)) else vs ! k = VElem (ds ! k)\<close>
  shows \<open>smt_interp_of (tr_interp_m p m f t u) vs =
    smt_val_of (value_of_m (SmtFun_ret (SmtProblem_funs p ! f)) (model_interp m f ds) t)\<close>
proof -
  let ?sg = \<open>SmtProblem_funs p ! f\<close>
  let ?sa = \<open>SmtFun_args ?sg\<close>
  let ?P = \<open>\<lambda>e. unat (Entry_fun e) = f \<and> List.map unat (Entry_args e) = ds\<close>
  let ?Q = \<open>\<lambda>e. List.map smt_val_of (SmtEntry_args e) = vs\<close>
  have PF: \<open>\<forall>x \<in> set (Model_entries m). ?P x \<longrightarrow> entry_ok_m ?sg f t u x\<close>
  proof (intro ballI impI)
    fix x assume \<open>?P x\<close>
    then have x: \<open>unat (Entry_fun x) = f\<close> \<open>length (Entry_args x) = length ?sa\<close> \<open>\<forall>k < length ?sa. unat (Entry_args x ! k) = ds ! k\<close>
      using assms(3) by (auto simp: list_eq_iff_nth_eq)
    then show \<open>entry_ok_m ?sg f t u x\<close> using assms(5) unfolding entry_ok_m_def by (metis (full_types))
  qed
  have el: \<open>(smt_val_of (value_of_m (?sa ! k) (unat a) t) = vs ! k) = (unat a = ds ! k)\<close>
    if k: \<open>k < length ?sa\<close> and ab: \<open>?sa ! k = SmtSort_Bool \<longrightarrow> unat a = t \<or> unat a = u\<close> for k and a :: \<open>64 word\<close>
  proof (cases \<open>?sa ! k = SmtSort_Bool\<close>)
    case True
    then have \<open>\<exists>b. vs ! k = VBool b \<and> ds ! k = (if b then t else u)\<close> using assms(5) k by simp
    then obtain b where \<open>vs ! k = VBool b\<close> \<open>ds ! k = (if b then t else u)\<close> by blast
    then show ?thesis using True ab assms(1) by auto
  next
    case False
    then have \<open>vs ! k = VElem (ds ! k)\<close> using assms(5) k by auto
    then show ?thesis using False by (cases \<open>?sa ! k\<close>) auto
  qed
  have FQ: \<open>\<forall>x \<in> set (Model_entries m). entry_ok_m ?sg f t u x \<longrightarrow> ?Q (tr_entry_m ?sg t x) = ?P x\<close>
  proof (intro ballI impI)
    fix x assume \<open>entry_ok_m ?sg f t u x\<close>
    then have x: \<open>unat (Entry_fun x) = f\<close> \<open>length (Entry_args x) = length ?sa\<close>
      \<open>\<forall>k < length ?sa. ?sa ! k = SmtSort_Bool \<longrightarrow> unat (Entry_args x ! k) = t \<or> unat (Entry_args x ! k) = u\<close>
      by (auto simp: entry_ok_m_def)
    have len: \<open>length (SmtEntry_args (tr_entry_m ?sg t x)) = length ?sa\<close> using x(2) by (simp add: tr_entry_m_def)
    have nth: \<open>\<forall>k < length ?sa. SmtEntry_args (tr_entry_m ?sg t x) ! k = value_of_m (?sa ! k) (unat (Entry_args x ! k)) t\<close>
      using x(2) by (simp add: tr_entry_m_def)
    have \<open>?Q (tr_entry_m ?sg t x) = (\<forall>k < length ?sa. smt_val_of (SmtEntry_args (tr_entry_m ?sg t x) ! k) = vs ! k)\<close>
      using len assms(4) by (simp add: list_eq_iff_nth_eq)
    also have \<open>\<dots> = (\<forall>k < length ?sa. smt_val_of (value_of_m (?sa ! k) (unat (Entry_args x ! k)) t) = vs ! k)\<close>
      using nth by simp
    also have \<open>\<dots> = (\<forall>k < length ?sa. unat (Entry_args x ! k) = ds ! k)\<close> using el x(3) by auto
    also have \<open>\<dots> = ?P x\<close> using x(1,2) assms(3) by (auto simp: list_eq_iff_nth_eq)
    finally show \<open>?Q (tr_entry_m ?sg t x) = ?P x\<close> .
  qed
  have fd: \<open>List.find ?Q (map (tr_entry_m ?sg t) (filter (entry_ok_m ?sg f t u) (Model_entries m))) =
      map_option (tr_entry_m ?sg t) (List.find ?P (Model_entries m))\<close>
    using find_map_filter[where P=\<open>?P\<close> and Q=\<open>?Q\<close> and F=\<open>entry_ok_m ?sg f t u\<close> and g=\<open>tr_entry_m ?sg t\<close>, OF PF FQ] .
  show ?thesis
    using fd by (auto simp: smt_interp_of_def tr_interp_m_def model_interp_def tr_entry_m_def Let_def split: option.splits)
qed

lemma dsize_fold: \<open>n \<le> foldl dsize_step n xs \<and> (\<forall>x \<in> set xs. unat x < foldl dsize_step n xs)\<close>
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have \<open>n \<le> dsize_step n x\<close> \<open>unat x < dsize_step n x\<close> by (auto simp: dsize_step_def)
  then show ?case using Cons.IH[of \<open>dsize_step n x\<close>] by (auto intro: le_trans less_le_trans)
qed

lemma domain_size_fold:
  \<open>n \<le> foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) n es \<and>
   (\<forall>e \<in> set es. unat (Entry_val e) < foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) n es \<and>
      (\<forall>a \<in> set (Entry_args e). unat a < foldl (\<lambda>n e. foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)) n es))\<close>
proof (induction es arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  let ?n = \<open>foldl dsize_step (dsize_step n (Entry_val e)) (Entry_args e)\<close>
  have \<open>n \<le> dsize_step n (Entry_val e)\<close> \<open>unat (Entry_val e) < dsize_step n (Entry_val e)\<close> by (auto simp: dsize_step_def)
  then have h: \<open>n \<le> ?n\<close> \<open>unat (Entry_val e) < ?n\<close> \<open>\<forall>a \<in> set (Entry_args e). unat a < ?n\<close>
    using dsize_fold[of \<open>dsize_step n (Entry_val e)\<close> \<open>Entry_args e\<close>] by auto
  then show ?case using Cons.IH[of ?n] by (auto intro: le_trans less_le_trans)
qed

lemma domain_size_m:
  \<open>1 \<le> domain_size_m m\<close>
  \<open>e \<in> set (Model_entries m) \<Longrightarrow> unat (Entry_val e) < domain_size_m m\<close>
  \<open>e \<in> set (Model_entries m) \<Longrightarrow> a \<in> set (Entry_args e) \<Longrightarrow> unat a < domain_size_m m\<close>
  using domain_size_fold[of 1 \<open>Model_entries m\<close>] by (auto simp: domain_size_m_def)

theorem tr_model_correct:
  assumes \<open>smt_wf p\<close> \<open>smt_fragment p\<close> \<open>tr_bounded p\<close> \<open>problem_true (model_interp m) (tr_problem_m p)\<close>
    \<open>domain_size_m m < 2 ^ 64\<close>
  shows \<open>smt_is_model p (tr_model_m p m)\<close>
proof -
  let ?fs = \<open>SmtProblem_funs p\<close> and ?nf = \<open>length (SmtProblem_funs p)\<close> and ?q = \<open>tr_state_m p\<close>
  let ?I = \<open>model_interp m\<close> and ?J = \<open>smt_model_interp (tr_model_m p m)\<close> and ?ru = \<open>\<lambda>v d. v = VElem d\<close>
  let ?t = \<open>const_value_m m ?nf\<close> and ?u = \<open>const_value_m m (?nf + 1)\<close>
  note M = tr_main[OF assms(1,2,3)]
  have cq: \<open>cls_true ?q ?I ?q\<close> using assms(4) problem_true_cls by blast
  have t0: \<open>tv ?I ?q 0 = ?t\<close> \<open>tv ?I ?q 1 = ?u\<close> using tv01[OF M(2,3), of ?I] by (simp_all add: const_value_interp)
  have tu: \<open>?t \<noteq> ?u\<close> using cls_init[OF M(2,3), of ?I] cls_true_pre[OF M(2) cq] t0 by simp
  have ru: \<open>ru_ok ?ru\<close> by (auto simp: ru_ok_def)
  have Jf: \<open>?J f vs = smt_interp_of (tr_interp_m p m f ?t ?u) vs\<close> if \<open>f < ?nf\<close> for f vs
    using that by (simp add: smt_model_interp_def tr_model_m_def Let_def)
  have jr: \<open>jrel p ?I ?q ?ru ?J\<close>
    unfolding jrel_def Let_def
  proof (intro allI impI)
    fix f vs ds
    assume f: \<open>f < ?nf\<close>
    let ?sa = \<open>SmtFun_args (?fs ! f)\<close> and ?r = \<open>SmtFun_ret (?fs ! f)\<close>
    assume h: \<open>length vs = length ?sa \<and> length ds = length ?sa \<and> (\<forall>i < length ?sa. vrel ?I ?q ?ru (?sa ! i) (vs ! i) (ds ! i))\<close>
    have h': \<open>\<forall>k < length ?sa. if ?sa ! k = SmtSort_Bool
       then (\<exists>b. vs ! k = VBool b \<and> ds ! k = (if b then ?t else ?u)) else vs ! k = VElem (ds ! k)\<close>
      using conjunct2[OF conjunct2[OF h[unfolded vrel_def t0]]] by blast
    have v: \<open>?J f vs = smt_val_of (value_of_m ?r (?I f ds) ?t)\<close>
      using tr_interp_val[OF tu f _ _ h'] h Jf[OF f] by simp
    show \<open>if ?r = SmtSort_Bool then ?J f vs = VBool (?I f ds = tv ?I ?q 0) else ?ru (?J f vs) (?I f ds)\<close>
      using v t0 model_interp_lt[of m f ds] by (cases ?r) (simp_all add: unat_wn)
  qed
  have S: \<open>smt_satisfies p ?J\<close> using M(4)[OF ru jr cq] .
  have wf: \<open>\<forall>f \<in> set ?fs. (\<forall>s \<in> set (SmtFun_args f). smt_wf_sort (unat (SmtProblem_num_sorts p)) s \<and> smt_sort_no_bv s) \<and>
      smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtFun_ret f) \<and> smt_sort_no_bv (SmtFun_ret f)\<close>
    using assms(1,2) unfolding smt_wf_def smt_fragment_def Let_def by blast
  let ?n = \<open>domain_size_m m\<close>
  have n: \<open>unat (word_of_nat ?n :: 64 word) = ?n\<close> \<open>1 \<le> ?n\<close> using assms(5) domain_size_m(1) by (simp_all add: unat_wn)
  let ?dms = \<open>replicate (unat (SmtProblem_num_sorts p)) (word_of_nat ?n :: 64 word)\<close>
  have vok: \<open>smt_model_value_ok ?dms s (value_of_m s v ?t)\<close>
    if \<open>smt_wf_sort (unat (SmtProblem_num_sorts p)) s\<close> \<open>smt_sort_no_bv s\<close> \<open>v < ?n\<close> \<open>v < 2 ^ 64\<close> for s v
    using that n by (cases s) (auto simp: unat_wn)
  have W: \<open>smt_model_wf p (tr_model_m p m)\<close>
    unfolding smt_model_wf_def Let_def
  proof (intro conjI allI impI ballI)
    show \<open>length (SmtModel_domains (tr_model_m p m)) = unat (SmtProblem_num_sorts p)\<close> by (simp add: tr_model_m_def Let_def)
    show \<open>0 < unat x\<close> if \<open>x \<in> set (SmtModel_domains (tr_model_m p m))\<close> for x
      using that n by (auto simp: tr_model_m_def Let_def)
    show \<open>length (SmtModel_funs (tr_model_m p m)) = ?nf\<close> by (simp add: tr_model_m_def Let_def)
    fix f assume f: \<open>f < ?nf\<close>
    have ti: \<open>SmtModel_funs (tr_model_m p m) ! f = tr_interp_m p m f ?t ?u\<close> \<open>SmtModel_domains (tr_model_m p m) = ?dms\<close>
      using f by (simp_all add: tr_model_m_def Let_def)
    have sf: \<open>(\<forall>s \<in> set (SmtFun_args (?fs ! f)). smt_wf_sort (unat (SmtProblem_num_sorts p)) s \<and> smt_sort_no_bv s) \<and>
      smt_wf_sort (unat (SmtProblem_num_sorts p)) (SmtFun_ret (?fs ! f)) \<and> smt_sort_no_bv (SmtFun_ret (?fs ! f))\<close>
      using bspec[OF wf nth_mem[OF f]] .
    show \<open>smt_model_value_ok (SmtModel_domains (tr_model_m p m)) (SmtFun_ret (?fs ! f)) (SmtInterp_default (SmtModel_funs (tr_model_m p m) ! f))\<close>
      using ti sf vok[of \<open>SmtFun_ret (?fs ! f)\<close> 0] n by (simp add: tr_interp_m_def Let_def)
    fix e' assume e': \<open>e' \<in> set (SmtInterp_entries (SmtModel_funs (tr_model_m p m) ! f))\<close>
    then obtain e where e: \<open>e \<in> set (Model_entries m)\<close> \<open>entry_ok_m (?fs ! f) f ?t ?u e\<close> \<open>e' = tr_entry_m (?fs ! f) ?t e\<close>
      using ti by (auto simp: tr_interp_m_def Let_def)
    have la: \<open>length (Entry_args e) = length (SmtFun_args (?fs ! f))\<close> using e(2) by (simp add: entry_ok_m_def)
    show \<open>list_all2 (smt_model_value_ok (SmtModel_domains (tr_model_m p m))) (SmtFun_args (?fs ! f)) (SmtEntry_args e')\<close>
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show \<open>length (SmtFun_args (?fs ! f)) = length (SmtEntry_args e')\<close> using e(3) la by (simp add: tr_entry_m_def)
      fix k assume k: \<open>k < length (SmtFun_args (?fs ! f))\<close>
      have \<open>unat (Entry_args e ! k) < ?n\<close> using domain_size_m(3)[OF e(1)] k la by simp
      then show \<open>smt_model_value_ok (SmtModel_domains (tr_model_m p m)) (SmtFun_args (?fs ! f) ! k) (SmtEntry_args e' ! k)\<close>
        using vok[of \<open>SmtFun_args (?fs ! f) ! k\<close> \<open>unat (Entry_args e ! k)\<close>] sf k la e(3) ti(2) unat_lt2p[of \<open>Entry_args e ! k\<close>]
        by (simp add: tr_entry_m_def)
    qed
    show \<open>smt_model_value_ok (SmtModel_domains (tr_model_m p m)) (SmtFun_ret (?fs ! f)) (SmtEntry_val e')\<close>
      using vok[of \<open>SmtFun_ret (?fs ! f)\<close> \<open>unat (Entry_val e)\<close>] sf domain_size_m(2)[OF e(1)] e(3) ti(2) unat_lt2p[of \<open>Entry_val e\<close>]
      by (simp add: tr_entry_m_def)
  qed
  show ?thesis using W S by (simp add: smt_is_model_def)
qed

end
