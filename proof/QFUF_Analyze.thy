theory QFUF_Analyze
  imports QFUF_Propagate
begin

section \<open>Conflict analysis\<close>

text \<open>The analysis of \<^verbatim>\<open>cdcl\<close> keeps its clause as two lists of flags over the atoms, \<open>cp\<close>
  for the positive and \<open>cn\<close> for the negative literals. It starts from a clause that holds in
  every model, and each step resolves it with another such clause; the result holds in every model
  whatever the records of the search say (\<open>lits_ok_resolve\<close>). The records (levels, time stamps,
  reasons) only choose the steps, so the functions that read them are only proved not to fail.\<close>

subsection \<open>Pure facts\<close>

text \<open>Some literal of the clause \<open>cp\<close>, \<open>cn\<close> holds in \<open>I\<close>.\<close>
definition lits_true :: \<open>(nat \<Rightarrow> nat list \<Rightarrow> nat) \<Rightarrow> Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>lits_true I p cp cn \<equiv> \<exists>j < length (Problem_atoms p).
     cp ! j \<and> atom_vals I p ! j \<or> cn ! j \<and> \<not> atom_vals I p ! j\<close>

text \<open>The clause \<open>cp\<close>, \<open>cn\<close> over the atoms of \<open>p\<close> holds in every model of \<open>p\<close>.\<close>
definition lits_ok :: \<open>Problem \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>lits_ok p cp cn \<equiv> length cp = length (Problem_atoms p) \<and> length cn = length (Problem_atoms p) \<and>
     (\<forall>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p \<longrightarrow> lits_true I p cp cn)\<close>

text \<open>The literal \<open>l\<close> is among the flags \<open>cp\<close>, \<open>cn\<close>.\<close>
definition lit_in :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_in cp cn l \<equiv> if Lit_pos l then cp ! unat (Lit_atom l) else cn ! unat (Lit_atom l)\<close>

text \<open>\<open>cp'\<close>, \<open>cn'\<close> contain the flags of \<open>cp\<close>, \<open>cn\<close>.\<close>
definition flags_le :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>flags_le cp cn cp' cn' \<equiv> length cp' = length cp \<and> length cn' = length cn \<and>
     (\<forall>j < length cp. cp ! j \<longrightarrow> cp' ! j) \<and> (\<forall>j < length cn. cn ! j \<longrightarrow> cn' ! j)\<close>

lemma flags_le_refl:
  \<open>flags_le cp cn cp cn\<close>
  unfolding flags_le_def by simp

lemma flags_le_trans:
  \<open>flags_le cp cn cp' cn' \<Longrightarrow> flags_le cp' cn' cp'' cn'' \<Longrightarrow> flags_le cp cn cp'' cn''\<close>
  unfolding flags_le_def by auto

lemma lits_ok_mono:
  assumes \<open>lits_ok p cp cn\<close> \<open>flags_le cp cn cp' cn'\<close>
  shows \<open>lits_ok p cp' cn'\<close>
  using assms unfolding lits_ok_def flags_le_def lits_true_def by metis

lemma lit_true_vals:
  \<open>unat (Lit_atom l) < length (Problem_atoms p) \<Longrightarrow>
   lit_true I p l = (if Lit_pos l then atom_vals I p ! unat (Lit_atom l) else \<not> atom_vals I p ! unat (Lit_atom l))\<close>
  unfolding lit_true_def atom_vals_def by simp

text \<open>A clause that holds in every model, all of whose literals are among the flags.\<close>
lemma lits_ok_clause:
  assumes c: \<open>clause_ok p c\<close> and len: \<open>length cp = length (Problem_atoms p)\<close> \<open>length cn = length (Problem_atoms p)\<close>
      and inc: \<open>\<forall>l \<in> set (Clause_lits c). lit_in cp cn l\<close>
  shows \<open>lits_ok p cp cn\<close>
  unfolding lits_ok_def
proof (intro conjI allI impI len)
  fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close>
  assume \<open>problem_true I p\<close>
  then obtain l where l: \<open>l \<in> set (Clause_lits c)\<close> \<open>lit_true I p l\<close>
    using c unfolding clause_ok_def clause_true_def by blast
  have a: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close> using c l(1) unfolding clause_ok_def by blast
  show \<open>lits_true I p cp cn\<close>
    using l inc a lit_true_vals[OF a, of I] unfolding lits_true_def lit_in_def
    by (cases \<open>Lit_pos l\<close>) auto
qed

text \<open>Resolution on atom \<open>x\<close>, whose value under the assignment is \<open>b\<close>: drop the literal of \<open>x\<close>
  with sign \<open>\<not> b\<close> from the clause \<open>cp\<close>, \<open>cn\<close>, and add the literals of \<open>r\<close> other than the one of
  \<open>x\<close> with sign \<open>b\<close>. If \<open>x\<close> has value \<open>b\<close> in a model, the dropped literal is false there, so
  another literal of the clause holds; otherwise the literal of \<open>x\<close> with sign \<open>b\<close> is false, so
  another literal of \<open>r\<close> holds.\<close>
lemma lits_ok_resolve:
  assumes ok: \<open>lits_ok p cp cn\<close> and r: \<open>clause_ok p r\<close> and x: \<open>x < length (Problem_atoms p)\<close>
      and le: \<open>flags_le (if b then cp else cp[x := False]) (if b then cn[x := False] else cn) cp' cn'\<close>
      and inc: \<open>\<forall>l \<in> set (Clause_lits r). \<not> (unat (Lit_atom l) = x \<and> Lit_pos l = b) \<longrightarrow> lit_in cp' cn' l\<close>
  shows \<open>lits_ok p cp' cn'\<close>
  unfolding lits_ok_def
proof (intro conjI allI impI)
  show \<open>length cp' = length (Problem_atoms p)\<close> \<open>length cn' = length (Problem_atoms p)\<close>
    using ok le unfolding lits_ok_def flags_le_def by (auto split: if_splits)
  fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close>
  assume I: \<open>problem_true I p\<close>
  show \<open>lits_true I p cp' cn'\<close>
  proof (cases \<open>atom_vals I p ! x = b\<close>)
    case True
    obtain j where j: \<open>j < length (Problem_atoms p)\<close> \<open>cp ! j \<and> atom_vals I p ! j \<or> cn ! j \<and> \<not> atom_vals I p ! j\<close>
      using ok I unfolding lits_ok_def lits_true_def by blast
    have \<open>(if b then cp else cp[x := False]) ! j \<and> atom_vals I p ! j \<or>
          (if b then cn[x := False] else cn) ! j \<and> \<not> atom_vals I p ! j\<close>
      using j True by (cases \<open>j = x\<close>) (auto simp add: nth_list_update)
    then show ?thesis
      using j(1) ok le unfolding lits_true_def flags_le_def lits_ok_def by (auto split: if_splits)
  next
    case False
    obtain l where l: \<open>l \<in> set (Clause_lits r)\<close> \<open>lit_true I p l\<close>
      using r I unfolding clause_ok_def clause_true_def by blast
    have a: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close> using r l(1) unfolding clause_ok_def by blast
    have \<open>\<not> (unat (Lit_atom l) = x \<and> Lit_pos l = b)\<close>
      using False l(2) lit_true_vals[OF a, of I] by (cases \<open>Lit_pos l\<close>) auto
    then have \<open>lit_in cp' cn' l\<close> using inc l(1) by blast
    then show ?thesis
      using a l(2) lit_true_vals[OF a, of I] unfolding lits_true_def lit_in_def
      by (cases \<open>Lit_pos l\<close>) auto
  qed
qed

text \<open>The literals of the clause that \<^verbatim>\<open>lits_clause\<close> builds from the first \<open>i\<close> flags.\<close>
definition flag_lits :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> Lit set\<close> where
  \<open>flag_lits cp cn i \<equiv> {make_Lit (word_of_nat j) True | j. j < i \<and> cp ! j} \<union>
     {make_Lit (word_of_nat j) False | j. j < i \<and> cn ! j}\<close>

lemma flag_lits_Suc:
  \<open>flag_lits cp cn (Suc i) = flag_lits cp cn i \<union> (if cp ! i then {make_Lit (word_of_nat i) True} else {}) \<union>
     (if cn ! i then {make_Lit (word_of_nat i) False} else {})\<close>
  unfolding flag_lits_def by (auto simp add: less_Suc_eq)

lemma flag_lits_clause_ok:
  assumes ok: \<open>lits_ok p cp cn\<close> and n: \<open>length (Problem_atoms p) < 2^63\<close>
      and c: \<open>set (Clause_lits c) = flag_lits cp cn (length cp)\<close>
  shows \<open>clause_ok p c\<close>
proof -
  have len: \<open>length cp = length (Problem_atoms p)\<close> \<open>length cn = length (Problem_atoms p)\<close>
    using ok unfolding lits_ok_def by simp_all
  have j: \<open>unat (word_of_nat j :: 64 word) = j\<close> if \<open>j < length (Problem_atoms p)\<close> for j
    using that n by (simp add: unat_of_nat_eq)
  show ?thesis
    unfolding clause_ok_def
  proof (intro conjI allI impI)
    show \<open>\<forall>l \<in> set (Clause_lits c). unat (Lit_atom l) < length (Problem_atoms p)\<close>
      using c len j unfolding flag_lits_def by auto
    fix I :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat\<close>
    assume \<open>problem_true I p\<close>
    then obtain k where k: \<open>k < length (Problem_atoms p)\<close>
        \<open>cp ! k \<and> atom_vals I p ! k \<or> cn ! k \<and> \<not> atom_vals I p ! k\<close>
      using ok unfolding lits_ok_def lits_true_def by blast
    show \<open>clause_true I p c\<close>
    proof (cases \<open>cp ! k \<and> atom_vals I p ! k\<close>)
      case True
      then have \<open>make_Lit (word_of_nat k) True \<in> set (Clause_lits c)\<close> using c k(1) len unfolding flag_lits_def by auto
      then show ?thesis using True k(1) j[OF k(1)] unfolding clause_true_def
        by (intro bexI[of _ \<open>make_Lit (word_of_nat k) True\<close>]) (auto simp add: lit_true_vals)
    next
      case False
      then have kn: \<open>cn ! k \<and> \<not> atom_vals I p ! k\<close> using k(2) by blast
      then have \<open>make_Lit (word_of_nat k) False \<in> set (Clause_lits c)\<close> using c k(1) len unfolding flag_lits_def by auto
      then show ?thesis using kn k(1) j[OF k(1)] unfolding clause_true_def
        by (intro bexI[of _ \<open>make_Lit (word_of_nat k) False\<close>]) (auto simp add: lit_true_vals)
    qed
  qed
qed

lemma flag_lits_card:
  \<open>card (flag_lits cp cn i) \<le> 2 * i\<close>
proof -
  have \<open>{make_Lit (word_of_nat j) True | j. j < i \<and> cp ! j} \<subseteq> (\<lambda>j. make_Lit (word_of_nat j) True) ` {..<i}\<close>
       \<open>{make_Lit (word_of_nat j) False | j. j < i \<and> cn ! j} \<subseteq> (\<lambda>j. make_Lit (word_of_nat j) False) ` {..<i}\<close>
    by auto
  then have \<open>card {make_Lit (word_of_nat j) True | j. j < i \<and> cp ! j} \<le> i\<close>
            \<open>card {make_Lit (word_of_nat j) False | j. j < i \<and> cn ! j} \<le> i\<close>
    by (metis (no_types, lifting) card_image_le card_lessThan finite_lessThan le_trans card_mono finite_imageI)+
  then show ?thesis unfolding flag_lits_def using card_Un_le by (metis (no_types, lifting) le_trans mult_2 add_mono)
qed

text \<open>The tautology on an atom of \<open>p\<close> holds in every model.\<close>
lemma tautology_clause_ok:
  assumes \<open>unat x < length (Problem_atoms p)\<close>
      and \<open>Clause_lits c = [make_Lit x True, make_Lit x False]\<close>
  shows \<open>clause_ok p c\<close>
  using assms unfolding clause_ok_def clause_true_def lit_true_def by auto

context QFUF_ctx
begin

subsection \<open>The records of the search\<close>

text \<open>\<^verbatim>\<open>QFUF_SmtSize\<close> proves the value of \<^const>\<open>sat_add\<close>; the search only needs that it
  does not fail.\<close>
definition sat_add_ok_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>sat_add_ok_contract a b \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma sat_add_ok_spec:
  shows \<open>\<Gamma>; sat_add a b \<Turnstile>\<^sub>F sat_add_ok_contract a b\<close>
  apply (crush_boot f: sat_add_def contract: sat_add_ok_contract_def)
  apply (crush_base inline: cap_def simp add: word_le_nat_alt word_less_nat_alt unat_sub)
  done

definition note_contract :: \<open>64 word list \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  \<open>note_contract v \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma note_spec:
  shows \<open>\<Gamma>; note_fn v x y \<Turnstile>\<^sub>F note_contract v\<close>
  apply (crush_boot f: note_fn_def contract: note_contract_def)
  apply (crush_base specs add: set_at_spec[where n=\<open>length v\<close>] contracts add: set_at_contract_def)
  done

lemma note_new_spec:
  shows \<open>\<Gamma>; note_new t f t1 f1 v y \<Turnstile>\<^sub>F note_contract v\<close>
  apply (crush_boot f: note_new_def contract: note_contract_def)
  apply crush_base
  subgoal for w_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' xs. w_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>xs \<star> \<langle>length xs = length v\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: set_at_spec[where n=\<open>length v\<close>] contracts add: set_at_contract_def
        simp add: unat_of_nat_eq word_less_nat_alt)
    apply (auto dest: unat_lt_len intro: unat_idx_lt(1))
    done
  done

lemma note_true_spec:
  shows \<open>\<Gamma>; note_true t t1 v y \<Turnstile>\<^sub>F note_contract v\<close>
  apply (crush_boot f: note_true_def contract: note_contract_def)
  apply crush_base
  subgoal for w_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' xs. w_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>xs \<star> \<langle>length xs = length v\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: set_at_spec[where n=\<open>length v\<close>] contracts add: set_at_contract_def
        simp add: unat_of_nat_eq word_less_nat_alt)
    apply (auto dest: unat_lt_len intro: unat_idx_lt(1))
    done
  done

subsection \<open>Reasons\<close>

definition tautology_contract :: \<open>64 word \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>tautology_contract x \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>Clause_lits r = [make_Lit x True, make_Lit x False]\<rangle>)\<close>

lemma tautology_spec:
  shows \<open>\<Gamma>; tautology x \<Turnstile>\<^sub>F tautology_contract x\<close>
  apply (crush_boot f: tautology_def contract: tautology_contract_def)
  apply (crush_base inline: vec_push_def)
  done

definition copy_clause_contract :: \<open>Clause \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>copy_clause_contract c \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>length (Clause_lits c) < 2^64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>Clause_lits r = Clause_lits c\<rangle>)\<close>

lemma copy_clause_spec:
  shows \<open>\<Gamma>; copy_clause c \<Turnstile>\<^sub>F copy_clause_contract c\<close>
  apply (crush_boot f: copy_clause_def contract: copy_clause_contract_def)
  apply (crush_base inline: vec_push_def)
  subgoal for lits_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' ls. lits_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ls \<star>
                 \<langle>ls = take i (Clause_lits c)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq take_Suc_conv_app_nth Lit.expand)
    done
  done

text \<open>A clause that the search may resolve with: it holds in every model and has a length.\<close>
definition clause_fits :: \<open>Problem \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_fits p c \<equiv> clause_ok p c \<and> length (Clause_lits c) < 2^64\<close>

lemma clause_fits_tautology:
  \<open>unat x < length (Problem_atoms p) \<Longrightarrow> Clause_lits c = [make_Lit x True, make_Lit x False] \<Longrightarrow> clause_fits p c\<close>
  unfolding clause_fits_def using tautology_clause_ok by simp

lemma clause_fits_copy:
  \<open>clause_fits p c \<Longrightarrow> Clause_lits c' = Clause_lits c \<Longrightarrow> clause_fits p c'\<close>
  unfolding clause_fits_def clause_ok_def clause_true_def by simp

lemma clauses_ok_fits:
  \<open>clauses_ok p l \<Longrightarrow> i < length l \<Longrightarrow> clause_fits p (l ! i)\<close>
  unfolding clauses_ok_def clause_fits_def by simp

definition indexed_clause_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>indexed_clause_contract p l x \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> unat x < length (Problem_atoms p)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>clause_fits p r\<rangle>)\<close>

lemma indexed_clause_spec:
  shows \<open>\<Gamma>; indexed_clause p l r x \<Turnstile>\<^sub>F indexed_clause_contract p l x\<close>
  apply (crush_boot f: indexed_clause_def contract: indexed_clause_contract_def)
  apply (crush_base specs add: copy_clause_spec tautology_spec
      contracts add: copy_clause_contract_def tautology_contract_def
      simp add: word_le_nat_alt word_less_nat_alt unat_sub)
  subgoal by (rule clause_fits_tautology)
  subgoal by (rule clause_fits_tautology)
  subgoal by (rule clause_fits_copy[OF clauses_ok_fits]) (auto dest: unat_lt_len)
  subgoal by (auto simp add: clauses_ok_def dest: unat_lt_len)
  subgoal by (auto dest: unat_lt_len)
  subgoal by (rule clause_fits_copy[OF clauses_ok_fits[OF clauses_ok_problem]]) (auto dest: unat_lt_len)
  subgoal using clauses_ok_problem[of p] by (auto simp add: clauses_ok_def dest: unat_lt_len)
  subgoal by (auto dest: unat_lt_len)
  done

definition reason_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> 64 word \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>reason_contract p l t x \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and>
          unat x < length (Problem_atoms p)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>clause_fits p r\<rangle>)\<close>

lemma theory_reason_spec:
  shows \<open>\<Gamma>; theory_reason p xs ys ls x \<Turnstile>\<^sub>F reason_contract p l t x\<close>
  apply (crush_boot f: theory_reason_def contract: reason_contract_def)
  apply (crush_base specs add: path_explain_log_spec rows_join_spec conflict_clause_spec tautology_spec
      contracts add: path_explain_log_contract_def rows_join_contract_def conflict_clause_contract_def
        tautology_contract_def)
  subgoal by (rule clause_fits_tautology)
  subgoal for a aa xa xb
    unfolding clause_fits_def using conflict_lits_clause_ok[of p x a xb] by (auto simp add: sizes_ok_def)
  subgoal by (simp add: sizes_ok_def)
  done

lemma reason_spec:
  shows \<open>\<Gamma>; reason p l xs ys ls rs x \<Turnstile>\<^sub>F reason_contract p l t x\<close>
  apply (crush_boot f: reason_def contract: reason_contract_def)
  apply (crush_base specs add: get_or_spec theory_reason_spec[where l=l and t=t] indexed_clause_spec
      contracts add: get_or_contract_def reason_contract_def indexed_clause_contract_def)
  done

subsection \<open>The clause of the analysis\<close>

text \<open>The flags \<open>cp\<close>, \<open>cn\<close> contain the literals of \<open>c\<close> before position \<open>i\<close> whose atoms are
  in bounds, except the literal of atom \<open>x\<close> with sign \<open>b\<close>.\<close>
definition has_lits :: \<open>Clause \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>has_lits c x b i cp cn \<equiv> \<forall>k < i. \<not> (Lit_atom (Clause_lits c ! k) = x \<and> Lit_pos (Clause_lits c ! k) = b) \<longrightarrow>
     unat (Lit_atom (Clause_lits c ! k)) < length cp \<longrightarrow> unat (Lit_atom (Clause_lits c ! k)) < length cn \<longrightarrow>
     lit_in cp cn (Clause_lits c ! k)\<close>

definition add_lits_contract :: \<open>Clause \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('s, bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  \<open>add_lits_contract c x b cp cn \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length (Clause_lits c) < 2^64 \<and> length cp < 2^64 \<and> length cn < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>flags_le cp cn (fst r) (fst (snd r)) \<and> has_lits c x b (length (Clause_lits c)) (fst r) (fst (snd r))\<rangle> in
     make_function_contract pre post\<close>

lemma has_lits_0:
  \<open>has_lits c x b 0 cp cn\<close>
  unfolding has_lits_def by simp

lemma has_lits_skip:
  assumes \<open>has_lits c x b i ps ns\<close>
      and \<open>Lit_atom (Clause_lits c ! i) = x \<and> Lit_pos (Clause_lits c ! i) = b \<or>
           \<not> unat (Lit_atom (Clause_lits c ! i)) < length ps \<or> \<not> unat (Lit_atom (Clause_lits c ! i)) < length ns\<close>
  shows \<open>has_lits c x b (Suc i) ps ns\<close>
  using assms unfolding has_lits_def by (auto simp add: less_Suc_eq)

lemma has_lits_pos:
  assumes \<open>has_lits c x b i ps ns\<close> \<open>Lit_pos (Clause_lits c ! i)\<close> \<open>unat (Lit_atom (Clause_lits c ! i)) < length ps\<close>
  shows \<open>has_lits c x b (Suc i) (ps[unat (Lit_atom (Clause_lits c ! i)) := True]) ns\<close>
  using assms unfolding has_lits_def lit_in_def by (auto simp add: less_Suc_eq nth_list_update)

lemma has_lits_neg:
  assumes \<open>has_lits c x b i ps ns\<close> \<open>\<not> Lit_pos (Clause_lits c ! i)\<close> \<open>unat (Lit_atom (Clause_lits c ! i)) < length ns\<close>
  shows \<open>has_lits c x b (Suc i) ps (ns[unat (Lit_atom (Clause_lits c ! i)) := True])\<close>
  using assms unfolding has_lits_def lit_in_def by (auto simp add: less_Suc_eq nth_list_update)

lemma nth_update_true:
  \<open>k < length xs \<Longrightarrow> xs ! k \<Longrightarrow> xs[j := True] ! k\<close>
  by (cases \<open>j = k\<close>) auto

lemma flags_le_set:
  \<open>flags_le cp cn ps ns \<Longrightarrow> flags_le cp cn (ps[j := True]) ns\<close>
  \<open>flags_le cp cn ps ns \<Longrightarrow> flags_le cp cn ps (ns[j := True])\<close>
  unfolding flags_le_def by (auto intro: nth_update_true)

lemma add_lits_spec:
  shows \<open>\<Gamma>; add_lits c x b cp cn \<Turnstile>\<^sub>F add_lits_contract c x b cp cn\<close>
  apply (crush_boot f: add_lits_def contract: add_lits_contract_def)
  apply crush_base
  subgoal for cp_ref cn_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. (\<Squnion>g ps. cp_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>ps \<star> (\<Squnion>g' ns. cn_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ns \<star>
                 \<langle>length ps = length cp \<and> length ns = length cn \<and> flags_le cp cn ps ns \<and> has_lits c x b i ps ns\<rangle>))\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq word_less_nat_alt)
    apply (auto intro: has_lits_skip has_lits_pos has_lits_neg flags_le_set flags_le_refl has_lits_0
        simp add: unat_of_nat_eq)
    done
  done

text \<open>Resolution in the form of the analysis' step (\<open>lits_ok_resolve\<close>).\<close>
lemma lits_ok_resolve':
  assumes ok: \<open>lits_ok p cp cn\<close> and r: \<open>clause_fits p r\<close> and x: \<open>unat x < length (Problem_atoms p)\<close>
      and le: \<open>flags_le (if b then cp else cp[unat x := False]) (if b then cn[unat x := False] else cn) cp' cn'\<close>
      and h: \<open>has_lits r x b (length (Clause_lits r)) cp' cn'\<close>
  shows \<open>lits_ok p cp' cn'\<close>
proof (rule lits_ok_resolve[OF ok _ x le])
  show \<open>clause_ok p r\<close> using r unfolding clause_fits_def by simp
  have len: \<open>length cp' = length (Problem_atoms p)\<close> \<open>length cn' = length (Problem_atoms p)\<close>
    using ok le unfolding lits_ok_def flags_le_def by (auto split: if_splits)
  show \<open>\<forall>l \<in> set (Clause_lits r). \<not> (unat (Lit_atom l) = unat x \<and> Lit_pos l = b) \<longrightarrow> lit_in cp' cn' l\<close>
  proof (intro ballI impI)
    fix l assume l: \<open>l \<in> set (Clause_lits r)\<close> \<open>\<not> (unat (Lit_atom l) = unat x \<and> Lit_pos l = b)\<close>
    then obtain k where k: \<open>k < length (Clause_lits r)\<close> \<open>l = Clause_lits r ! k\<close> by (auto simp add: in_set_conv_nth)
    have a: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close> using r l(1) unfolding clause_fits_def clause_ok_def by blast
    show \<open>lit_in cp' cn' l\<close> using h k l(2) a len unfolding has_lits_def by auto
  qed
qed

text \<open>The first clause of the analysis: all literals of a clause that holds in every model.\<close>
lemma lits_ok_start:
  assumes c: \<open>clause_fits p c\<close> and len: \<open>length cp = length (Problem_atoms p)\<close> \<open>length cn = length (Problem_atoms p)\<close>
      and n: \<open>length (Problem_atoms p) < 2^63\<close>
      and h: \<open>has_lits c (word_of_nat (length (Problem_atoms p))) True (length (Clause_lits c)) cp cn\<close>
  shows \<open>lits_ok p cp cn\<close>
proof (rule lits_ok_clause[OF _ len])
  show co: \<open>clause_ok p c\<close> using c unfolding clause_fits_def by simp
  show \<open>\<forall>l \<in> set (Clause_lits c). lit_in cp cn l\<close>
  proof
    fix l assume l: \<open>l \<in> set (Clause_lits c)\<close>
    then obtain k where k: \<open>k < length (Clause_lits c)\<close> \<open>l = Clause_lits c ! k\<close> by (auto simp add: in_set_conv_nth)
    have a: \<open>unat (Lit_atom l) < length (Problem_atoms p)\<close> using co l unfolding clause_ok_def by blast
    then have \<open>Lit_atom l \<noteq> word_of_nat (length (Problem_atoms p))\<close>
      using n by (auto simp add: unat_of_nat_eq)
    then show \<open>lit_in cp cn l\<close> using h k a len unfolding has_lits_def by auto
  qed
qed

text \<open>The scans that choose the steps of the analysis: only that they do not fail.\<close>
definition at_level_contract :: \<open>bool list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>at_level_contract cp j \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>unat j < length cp\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma at_level_spec:
  shows \<open>\<Gamma>; at_level lv cp cn d j \<Turnstile>\<^sub>F at_level_contract cp j\<close>
  apply (crush_boot f: at_level_def contract: at_level_contract_def)
  apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def simp add: word_less_nat_alt)
  apply (auto dest: unat_lt_len)
  done

definition scan_ok_contract :: \<open>bool list \<Rightarrow> ('s, 'r, 'abort) function_contract\<close> where
  \<open>scan_ok_contract cp \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>length cp < 2^64\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma last_at_spec:
  shows \<open>\<Gamma>; last_at lv ts cp cn d \<Turnstile>\<^sub>F scan_ok_contract cp\<close>
  apply (crush_boot f: last_at_def contract: scan_ok_contract_def)
  apply crush_base
  subgoal for x_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' v. x_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: at_level_spec get_or_spec contracts add: at_level_contract_def get_or_contract_def
        simp add: unat_of_nat_eq)
    done
  done

lemma other_at_spec:
  shows \<open>\<Gamma>; other_at lv cp cn d x \<Turnstile>\<^sub>F scan_ok_contract cp\<close>
  apply (crush_boot f: other_at_def contract: scan_ok_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>_. can_alloc_reference\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base specs add: at_level_spec contracts add: at_level_contract_def simp add: unat_of_nat_eq)
  done

lemma level_below_spec:
  shows \<open>\<Gamma>; level_below lv cp cn d \<Turnstile>\<^sub>F scan_ok_contract cp\<close>
  apply (crush_boot f: level_below_def contract: scan_ok_contract_def)
  apply crush_base
  subgoal for b_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g' v. b_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>v)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: get_or_spec contracts add: get_or_contract_def simp add: unat_of_nat_eq)
    using unat_lt_len by (fastforce simp add: word_less_nat_alt unat_of_nat_eq)
  done

subsection \<open>Resolution\<close>

text \<open>\<open>lits_ok_resolve'\<close> for the two values of the resolved atom, in the form of the goals that
  \<open>crush_base\<close> leaves.\<close>
lemma resolve_step_ok:
  assumes \<open>lits_ok p cp cn\<close> \<open>clause_fits p r\<close> \<open>\<not> unat (word_of_nat (length cp) :: 64 word) \<le> unat x\<close>
  shows \<open>flags_le (cp[unat x := False]) cn a aa \<Longrightarrow> has_lits r x False (length (Clause_lits r)) a aa \<Longrightarrow> lits_ok p a aa\<close>
    \<open>flags_le cp (cn[unat x := False]) a aa \<Longrightarrow> has_lits r x True (length (Clause_lits r)) a aa \<Longrightarrow> lits_ok p a aa\<close>
proof -
  have \<open>unat x < length (Problem_atoms p)\<close>
    using assms(1,3) unat_lt_len unfolding lits_ok_def by (metis not_le)
  then show \<open>flags_le (cp[unat x := False]) cn a aa \<Longrightarrow> has_lits r x False (length (Clause_lits r)) a aa \<Longrightarrow> lits_ok p a aa\<close>
    \<open>flags_le cp (cn[unat x := False]) a aa \<Longrightarrow> has_lits r x True (length (Clause_lits r)) a aa \<Longrightarrow> lits_ok p a aa\<close>
    using lits_ok_resolve'[OF assms(1,2), of x False a aa] lits_ok_resolve'[OF assms(1,2), of x True a aa] by simp_all
qed

definition resolve_step_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ('s, bool \<times> bool list \<times> bool list \<times> tnil, 'abort) function_contract\<close> where
  \<open>resolve_step_contract p l t cp cn \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and> lits_ok p cp cn\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>lits_ok p (fst (snd r)) (fst (snd (snd r)))\<rangle> in
     make_function_contract pre post\<close>

lemma resolve_step_spec:
  shows \<open>\<Gamma>; resolve_step p l t lv ts rs xs ys ls d cp cn \<Turnstile>\<^sub>F resolve_step_contract p l t cp cn\<close>
  apply (crush_boot f: resolve_step_def contract: resolve_step_contract_def)
  apply (crush_base specs add: last_at_spec other_at_spec get_or_spec reason_spec[where t=t] add_lits_spec
      contracts add: scan_ok_contract_def get_or_contract_def reason_contract_def add_lits_contract_def
      simp add: word_le_nat_alt word_less_nat_alt)
  apply (all \<open>(solves \<open>rule resolve_step_ok; assumption\<close>)?\<close>)
  apply (auto simp add: clause_fits_def lits_ok_def sizes_ok_def not_le dest: unat_lt_len)
  done

definition lits_clause_contract :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> ('s, Clause, 'abort) function_contract\<close> where
  \<open>lits_clause_contract cp cn \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length cn = length cp \<and> length cp < 2^63\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>set (Clause_lits r) = flag_lits cp cn (length cp) \<and> length (Clause_lits r) \<le> 2 * length cp\<rangle> in
     make_function_contract pre post\<close>

lemma lits_clause_spec:
  shows \<open>\<Gamma>; lits_clause cp cn \<Turnstile>\<^sub>F lits_clause_contract cp cn\<close>
  apply (crush_boot f: lits_clause_def contract: lits_clause_contract_def)
  apply (crush_base inline: vec_push_def)
  subgoal for lits_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>g' ls. lits_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ls \<star>
                 \<langle>set ls = flag_lits cp cn i \<and> length ls \<le> 2 * i\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq flag_lits_Suc)
    subgoal by (simp add: word_less_nat_alt unat_of_nat_eq)
    subgoal by (simp add: word_less_nat_alt unat_of_nat_eq)
    subgoal by (simp add: insert_commute)
    subgoal by (simp add: flag_lits_def)
    done
  done

subsection \<open>The analysis and the conflict\<close>

lemma flag_lits_fits:
  assumes \<open>lits_ok p cp cn\<close> \<open>length (Problem_atoms p) < 9223372036854775808\<close>
      and \<open>set (Clause_lits c) = flag_lits cp cn (length cp)\<close> \<open>length (Clause_lits c) \<le> 2 * length cp\<close>
  shows \<open>clause_fits p c\<close>
  using assms flag_lits_clause_ok[of p cp cn c] unfolding clause_fits_def lits_ok_def by simp

definition analyze_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow>
      ('s, Clause \<times> bool \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  \<open>analyze_contract p l t c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and> clause_fits p c\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>clause_fits p (fst r)\<rangle> in
     make_function_contract pre post\<close>

lemma analyze_spec:
  shows \<open>\<Gamma>; analyze p l t lv ts rs xs ys ls d c \<Turnstile>\<^sub>F analyze_contract p l t c\<close>
  apply (crush_boot f: analyze_def contract: analyze_contract_def)
  apply (crush_base specs add: add_lits_spec contracts add: add_lits_contract_def simp add: sizes_ok_def unat_of_nat_eq)
  subgoal for a aa cp_ref cn_ref go_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ _. can_alloc_reference \<star> (\<Squnion>g ps. cp_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>ps \<star>
                 (\<Squnion>g' ns. cn_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>ns \<star> (\<Squnion>g'' b. go_ref \<mapsto>\<langle>\<top>\<rangle> g''\<down>b) \<star>
                 \<langle>lits_ok p ps ns\<rangle>))\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: resolve_step_spec last_at_spec other_at_spec level_below_spec lits_clause_spec
        contracts add: resolve_step_contract_def scan_ok_contract_def lits_clause_contract_def
        simp add: sizes_ok_def)
    apply (all \<open>(solves \<open>rule flag_lits_fits; assumption\<close>)?\<close>)
    apply (all \<open>(solves \<open>rule lits_ok_start; (assumption | simp add: flags_le_def)\<close>)?\<close>)
    apply (auto simp add: lits_ok_def)
    done
  subgoal by (simp add: clause_fits_def)
  done

definition on_conflict_contract :: \<open>Problem \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow>
      ('s, Model option \<times> Clause list \<times> 64 word \<times> tnil, 'abort) function_contract\<close> where
  \<open>on_conflict_contract p l t c \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> clauses_ok p l \<and> length t = length (Problem_atoms p) \<and> clause_fits p c\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>fst r = None \<and> clauses_ok p (fst (snd r))\<rangle> in
     make_function_contract pre post\<close>

lemma on_conflict_spec:
  shows \<open>\<Gamma>; on_conflict p l t lv ts rs xs ys ls d c \<Turnstile>\<^sub>F on_conflict_contract p l t c\<close>
  apply (crush_boot f: on_conflict_def contract: on_conflict_contract_def)
  apply (crush_base specs add: analyze_spec learn_spec contracts add: analyze_contract_def learn_contract_def)
  apply (auto intro: clauses_ok_append simp add: clause_fits_def)
  done

end

end
